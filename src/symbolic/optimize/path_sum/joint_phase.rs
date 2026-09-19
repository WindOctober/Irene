//! Joint cofactor phase analysis, rather than rejecting individual selectors.
//!
//! P(y,z) = P(0,z) + y * (P(1,z)-P(0,z)) modulo one. The returned
//! certificate is only used by existing Fourier/Omega rules, which retain
//! P(0,z) and separately check all observable/history/guard/scalar uses.
use super::*;
use crate::symbolic::PhasePolynomial;

// Bounds only this optional proof attempt, not the stored phase domain.
// A refusal leaves the original HPS and all existing fallbacks unchanged.
const MAX_BITS: u32 = 12;
const MAX_SELECTOR_WORK: usize = 100_000;

#[cfg(test)]
mod tests;

pub(super) fn profile(c: &Component, y: &Variable) -> PhaseProfile {
    analyze(c, y).unwrap_or(PhaseProfile::Unsupported)
}

fn analyze(c: &Component, y: &Variable) -> Option<PhaseProfile> {
    let mut difference = PhasePolynomial::zero();
    let mut work = MAX_SELECTOR_WORK;
    for (selector, coefficient) in c.phase.selectors() {
        if !selector.variables().contains(y) {
            continue;
        }
        // Reject unsupported numeric atoms, never drop their contribution.
        coefficient.as_rational()?;
        work = work.checked_sub(selector.storage_size())?;
        let high = selector.substitute(y, &BooleanPolynomial::one());
        let low = selector.substitute(y, &BooleanPolynomial::zero());
        difference.add_boolean(&high, coefficient.clone());
        difference.add_boolean(&low, coefficient.scaled(BigInt::from(-1)));
        if difference.storage_size() > MAX_SELECTOR_WORK {
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
        if constant == integer(0) {
            return Some(PhaseProfile::Fourier(parity));
        }
        if constant == ratio(1, 2) {
            return Some(PhaseProfile::Fourier(parity.complement()));
        }
        if constant == ratio(1, 4) {
            return Some(PhaseProfile::Omega {
                parity,
                sign: OmegaSign::Positive,
            });
        }
        if constant == ratio(3, 4) {
            return Some(PhaseProfile::Omega {
                parity,
                sign: OmegaSign::Negative,
            });
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
    let mut bits = vec![BooleanPolynomial::zero(); width as usize];
    for (selector, numerator, denominator) in summands {
        // Coefficients are normalized into [0,1), so this product < modulus.
        let value = numerator.checked_mul(modulus / denominator)?;
        let mut carry = BooleanPolynomial::zero();
        for (i, bit) in bits.iter_mut().enumerate() {
            let rhs = if value & (1 << i) != 0 {
                selector.clone()
            } else {
                BooleanPolynomial::zero()
            };
            let xor = bit.xor(&rhs);
            let next = bit.and(&rhs).xor(&xor.and(&carry));
            *bit = xor.xor(&carry);
            carry = next;
        }
        if bits
            .iter()
            .map(BooleanPolynomial::storage_size)
            .sum::<usize>()
            > MAX_SELECTOR_WORK
        {
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
