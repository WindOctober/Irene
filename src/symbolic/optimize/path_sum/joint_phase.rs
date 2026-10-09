//! Joint cofactor phase analysis, rather than rejecting individual selectors.
//!
//! P(y,z) = P(0,z) + y * (P(1,z)-P(0,z)) modulo one. The returned
//! certificate is only used by existing Fourier/Omega rules, which retain
//! P(0,z) and separately check all observable/history/guard/scalar uses.
use super::*;
use crate::symbolic::{PhasePolynomial, RootStorage, StorageCounter};

// Bounds only this optional proof attempt, not the stored phase domain.
// A refusal leaves the original HPS and all existing fallbacks unchanged.
const MAX_BITS: u32 = 12;
const MAX_SELECTOR_WORK: usize = 100_000;

/// A concrete counterexample to 4*delta being integral rejects only the local
/// Fourier/Omega rule. Each u64 lane is an exact Boolean assignment, not a
/// numerical approximation. No counterexample means unknown, never admissible.
fn low_bit_witness(summands: &[(BooleanPolynomial, u64)], width: u32) -> bool {
    if width <= 2 {
        return false;
    }
    let low_width = width - 2;
    let mask = (1u64 << low_width) - 1;
    let relevant: Vec<_> = summands
        .iter()
        .filter(|(_, value)| value & mask != 0)
        .collect();
    if relevant.is_empty() {
        return false;
    }
    let roots: Vec<_> = relevant.iter().map(|(p, _)| p.clone()).collect();
    let (network, _) = BooleanPolynomial::graph_network(&roots);
    let mut values = Vec::with_capacity(network.nodes.len());
    for &[op, a, b] in &network.nodes {
        let value = match op {
            0 => {
                if a == 0 {
                    0
                } else {
                    u64::MAX
                }
            }
            1 => {
                // All-zero/all-one, then 31 one-hot/one-cold assignments.
                let mut bits = 0xaaaaaaaaaaaaaaaau64;
                if a < 31 {
                    bits &= !(1u64 << (3 + 2 * a));
                    bits |= 1u64 << (2 + 2 * a);
                }
                bits
            }
            2 => values[a as usize] ^ values[b as usize],
            3 => values[a as usize] & values[b as usize],
            _ => unreachable!("internally constructed XAG"),
        };
        values.push(value);
    }
    let mut bits = vec![0u64; low_width as usize];
    for ((_, coefficient), output) in relevant.into_iter().zip(network.outputs) {
        let selector = values[output as usize];
        let mut carry = 0;
        for (i, bit) in bits.iter_mut().enumerate() {
            let rhs = if coefficient & (1 << i) != 0 {
                selector
            } else {
                0
            };
            let xor = *bit ^ rhs;
            let next = (*bit & rhs) ^ (xor & carry);
            *bit = xor ^ carry;
            carry = next;
        }
    }
    // Inspect the complete modular sum, not an intermediate partial sum:
    // later summands may cancel every currently nonzero low bit.
    bits.into_iter().any(|bit| bit != 0)
}

#[cfg(test)]
mod tests;

pub(super) fn profile(query: &mut analysis::Query<'_>) -> PhaseProfile {
    analyze_query(query).unwrap_or(PhaseProfile::Unsupported)
}

#[cfg(test)]
fn analyze(c: &Component, y: &Variable) -> Option<PhaseProfile> {
    analyze_query(&mut analysis::Analysis::new(c).query(y))
}

fn analyze_query(query: &mut analysis::Query<'_>) -> Option<PhaseProfile> {
    let mut difference = PhasePolynomial::zero();
    let mut difference_storage = StorageCounter::default();
    let mut work = MAX_SELECTOR_WORK;
    for i in 0..query.len() {
        if crate::symbolic::deadline::expired() {
            return None;
        }
        let coefficient = query.coefficient(i).clone();
        // Reject unsupported numeric atoms, never drop their contribution.
        coefficient.as_rational()?;
        work = work.checked_sub(query.size(i))?;
        let (low, high) = query.cofactors(i);
        difference.add_boolean(high, coefficient.clone());
        difference.add_boolean(low, coefficient.scaled(BigInt::from(-1)));
        let size = difference_storage.update(difference.selectors().map(|(p, _)| p));
        #[cfg(test)]
        assert_eq!(size, difference.storage_size());
        if size > MAX_SELECTOR_WORK {
            return None;
        }
    }
    // Cheap path first: joint coefficient merging often already exposes the
    // half-turn parity, without constructing any bit-vector function.
    let mut constant = integer(0);
    let mut parity = BooleanPolynomial::zero();
    let mut simple = true;
    for (selector, coefficient) in difference.selectors() {
        let coefficient = coefficient.as_rational()?;
        if selector.is_one() {
            constant += coefficient;
        } else if coefficient == ratio(1, 2) {
            parity = parity.xor(&selector);
        } else {
            simple = false;
        }
    }
    if simple {
        let constant = PhaseCoefficient::rational(constant).as_rational()?;
        let profile = PhaseProfile::classify(true, constant, parity, BooleanPolynomial::complement);
        if !matches!(profile, PhaseProfile::Unsupported) {
            return Some(profile);
        }
    }
    let mut width = 2;
    let mut summands = Vec::new();
    for (selector, coefficient) in difference.selectors() {
        let rational = coefficient.as_rational()?;
        let denominator = u64::try_from(rational.denom()).ok()?;
        if !denominator.is_power_of_two() {
            return None;
        }
        width = width.max(denominator.trailing_zeros());
        if width > MAX_BITS {
            return None;
        }
        summands.push((selector, u64::try_from(rational.numer()).ok()?, denominator));
    }
    let modulus = 1u64 << width;
    let summands: Vec<_> = summands
        .into_iter()
        .map(|(p, numerator, denominator)| Some((p, numerator.checked_mul(modulus / denominator)?)))
        .collect::<Option<_>>()?;
    if low_bit_witness(&summands, width) {
        return None;
    }
    let mut bits = vec![BooleanPolynomial::zero(); width as usize];
    // Keep each bit's counter in its own slot, so changed roots reuse the
    // previous graph for that bit, not an unrelated retired bit's graph.
    let mut bit_storage: Vec<_> = (0..width).map(|_| RootStorage::default()).collect();
    for (selector, value) in summands {
        if crate::symbolic::deadline::expired() {
            return None;
        }
        // Coefficients are normalized into [0,1), so this product < modulus.
        let mut carry = BooleanPolynomial::zero();
        for (i, bit) in bits.iter_mut().enumerate() {
            let rhs = if value & (1 << i) != 0 {
                selector.clone()
            } else {
                BooleanPolynomial::zero()
            };
            let xor = bit.xor(&rhs);
            // Arithmetic is modulo 2^width: the carry out of the highest
            // retained bit is discarded, so do not construct its XAG at all.
            let next = (i + 1 < width as usize).then(|| bit.and(&rhs).xor(&xor.and(&carry)));
            *bit = xor.xor(&carry);
            if let Some(next) = next {
                carry = next;
            }
        }
        let size: usize = bit_storage
            .iter_mut()
            .zip(&bits)
            .map(|(counter, bit)| counter.update(bit.clone()))
            .sum();
        #[cfg(test)]
        assert_eq!(
            size,
            bits.iter()
                .map(BooleanPolynomial::storage_size)
                .sum::<usize>()
        );
        if size > MAX_SELECTOR_WORK {
            return None;
        }
    }
    let bits = BooleanPolynomial::normalize_local(&bits)?;
    // With all sub-quarter bits zero and a constant quarter bit, the exact
    // derivative is f/2 or 1/4 + f/2. Only f remains input-dependent. This is
    // the Fourier/Omega certificate; a varying quarter bit is NOT sufficient.
    if bits[..bits.len() - 2].iter().any(|bit| !bit.is_zero()) {
        return None;
    }
    let quarter = &bits[bits.len() - 2];
    let parity = bits[bits.len() - 1].clone();
    if quarter.is_zero() {
        Some(PhaseProfile::Fourier(parity))
    } else if quarter.is_one() {
        Some(PhaseProfile::Omega {
            parity,
            sign: OmegaSign::Positive,
        })
    } else {
        None
    }
}
