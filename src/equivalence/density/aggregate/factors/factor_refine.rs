//! Recover smaller products from complete expanded phase sums.
//! Candidates are accepted only after exact reconstruction. Failure is
//! inconclusive; a common selector is restored on every refined factor.
//! Multiplication callbacks must return the complete exact product or None,
//! never a prefix. The append callback must preserve the whole guarded term
//! (or prove it zero); any refusal discards the entire refinement result.
use crate::equivalence::density::aggregate::collection::{
    ExactAggregate, ExactCoefficient, ExactEntry, ExactTerm, accumulate_exact_term,
};
use crate::equivalence::density::aggregate::scalar::integer;
use crate::equivalence::density::aggregate::{
    KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, KernelVariable, WorkingTerm,
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

pub(in crate::equivalence::density::aggregate) fn tensor(
    source: &ExactAggregate,
    scan_limit: usize,
    mut multiply: impl FnMut(ExactAggregate, ExactAggregate) -> Option<ExactAggregate>,
) -> Option<[ExactAggregate; 2]> {
    if source.len() != 1 {
        return None;
    }
    // A common selector may identify a ket coordinate with a bra coordinate.
    // Such coordinates are shared parameters, not evidence of entanglement
    // between the remaining coordinate sets. Keep their exact dependence in
    // both factors and in the nonzero exponential used as a pivot.
    let shared = source
        .keys()
        .next()?
        .constraints
        .iter()
        .flat_map(KernelBooleanPolynomial::variables)
        .collect::<BTreeSet<_>>();
    let coefficients = source.values().next()?;
    // Cells are formal complex coefficients constant in the two private
    // coordinate sets, but may depend on shared selector parameters. No
    // phase independence is assumed.
    let mut cells: BTreeMap<(KernelPhasePolynomial, KernelPhasePolynomial), ExactCoefficient> =
        BTreeMap::new();
    let mut scanned = 0usize;
    for (phase, coefficient) in coefficients {
        if !phase.is_algebraic() {
            return None;
        }
        if !matches!(coefficient, KernelScalar::Rational(_)) {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("aggregate tensor refused: non-rational scalar");
            }
            return None;
        }
        let mut ket = KernelPhasePolynomial::default();
        let mut bra = KernelPhasePolynomial::default();
        let mut constant = KernelPhasePolynomial::default();
        for (monomial, coefficient) in phase.terms() {
            let mut is_ket = false;
            let mut is_bra = false;
            for variable in monomial.variables() {
                scanned = scanned.checked_add(1)?;
                if scanned > scan_limit {
                    return None;
                }
                if shared.contains(variable) {
                    continue;
                }
                match variable {
                    KernelVariable::InputKet(_) | KernelVariable::QuantumOutputKet(_) => {
                        is_ket = true
                    }
                    KernelVariable::InputBra(_) | KernelVariable::QuantumOutputBra(_) => {
                        is_bra = true
                    }
                    _ => return None,
                }
            }
            let target = match (is_ket, is_bra) {
                (true, false) => &mut ket,
                (false, true) => &mut bra,
                (false, false) => &mut constant,
                (true, true) => {
                    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                        eprintln!("aggregate tensor refused: mixed monomial {monomial:?}");
                    }
                    return None;
                }
            };
            target.add_boolean(
                &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                coefficient.clone(),
            );
        }
        if cells
            .entry((ket, bra))
            .or_default()
            .insert(constant, coefficient.clone())
            .is_some()
        {
            return None;
        }
    }
    let ((pivot_ket, pivot_bra), pivot) = cells.iter().find(|(_, cell)| cell.len() == 1)?;
    let (pivot_phase, KernelScalar::Rational(pivot_scalar)) = pivot.first_key_value()? else {
        return None;
    };
    if *pivot_scalar == integer(0) {
        return None;
    }
    let mut ket_factor = ExactAggregate::new();
    let mut bra_factor = ExactAggregate::new();
    let mut ket_atoms = 0;
    let mut bra_atoms = 0;
    for ((ket, bra), cell) in &cells {
        for (constant, coefficient) in cell {
            if bra == pivot_bra {
                let mut phase = ket.clone();
                for (monomial, value) in constant.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.clone(),
                    );
                }
                accumulate_exact_term(
                    ExactTerm {
                        constraints: Vec::new(),
                        coefficient: coefficient.clone(),
                        phase,
                    },
                    &mut ket_factor,
                    &mut ket_atoms,
                )?;
            }
            if ket == pivot_ket {
                let KernelScalar::Rational(value) = coefficient else {
                    return None;
                };
                let mut phase = bra.clone();
                for (monomial, value) in constant.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.clone(),
                    );
                }
                for (monomial, value) in pivot_phase.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.scaled(BigInt::from(-1)),
                    );
                }
                accumulate_exact_term(
                    ExactTerm {
                        constraints: Vec::new(),
                        coefficient: KernelScalar::Rational(value / pivot_scalar),
                        phase,
                    },
                    &mut bra_factor,
                    &mut bra_atoms,
                )?;
            }
        }
    }
    // This is the certificate gate: a false rank-one guess, missing cell,
    // sign, relative phase, or scale can never survive reconstruction.
    let reconstructed = multiply(ket_factor.clone(), bra_factor.clone())?;
    let expected = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        coefficients.clone(),
    )]);
    if reconstructed != expected {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate tensor refused: reconstruction");
        }
        return None;
    }
    Some([ket_factor, bra_factor])
}

/// A four-atom product need not follow the syntactic ket/bra partition.
/// Try at most six rectangles around one nonzero atom; accept ONLY exact
/// reconstruction, with every selector and all relative phases retained.
pub(in crate::equivalence::density::aggregate) fn binomials(
    source: &ExactAggregate,
    mut multiply: impl FnMut(ExactAggregate, ExactAggregate) -> Option<ExactAggregate>,
) -> Option<[ExactAggregate; 2]> {
    if source.len() != 1 {
        return None;
    }
    let (entry, coefficients) = source.first_key_value()?;
    if coefficients.len() != 4 {
        return None;
    }
    let atoms = coefficients.iter().collect::<Vec<_>>();
    let (pivot_phase, KernelScalar::Rational(pivot_scalar)) = atoms[0] else {
        return None;
    };
    if *pivot_scalar == integer(0)
        || pivot_scalar.numer().bits() > 4096
        || pivot_scalar.denom().bits() > 4096
    {
        return None;
    }
    for row in 1..4 {
        for column in 1..4 {
            if row == column {
                continue;
            }
            let KernelScalar::Rational(column_scalar) = atoms[column].1 else {
                return None;
            };
            let mut left = ExactAggregate::new();
            let mut left_atoms = 0;
            for index in [0, row] {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        coefficient: atoms[index].1.clone(),
                        phase: atoms[index].0.clone(),
                    },
                    &mut left,
                    &mut left_atoms,
                )?;
            }
            let mut right = ExactAggregate::new();
            let mut right_atoms = 0;
            for (coefficient, phase) in [
                (integer(1), KernelPhasePolynomial::default()),
                (
                    column_scalar / pivot_scalar,
                    KernelPhasePolynomial::difference(atoms[column].0, pivot_phase),
                ),
            ] {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        coefficient: KernelScalar::Rational(coefficient),
                        phase,
                    },
                    &mut right,
                    &mut right_atoms,
                )?;
            }
            if multiply(left.clone(), right.clone())? == *source {
                return Some([left, right]);
            }
        }
    }
    None
}

/// Refine a small factor only after the existing tensor routine reconstructs
/// its entire unguarded aggregate. Reattach its OWN selector to both children;
/// idempotence preserves it even if it is stronger than the common selector.
pub(in crate::equivalence::density::aggregate) fn refine<C>(
    source: ExactAggregate,
    scan_limit: usize,
    context: &mut C,
    mut multiply: impl FnMut(ExactAggregate, ExactAggregate, &mut C) -> Option<ExactAggregate>,
    mut append: impl FnMut(WorkingTerm, &mut ExactAggregate, &mut usize, &mut C) -> Option<()>,
) -> Option<Vec<ExactAggregate>> {
    let count = source.values().map(BTreeMap::len).sum::<usize>();
    if count < 4 {
        return Some(vec![source]);
    }
    let Some([left, right]) = tensor(&source, scan_limit, |l, r| multiply(l, r, context))
        .or_else(|| binomials(&source, |l, r| multiply(l, r, context)))
    else {
        return Some(vec![source]);
    };
    let size = |factor: &ExactAggregate| factor.values().map(BTreeMap::len).sum::<usize>();
    if size(&left) < 2 || size(&right) < 2 || size(&left) >= count || size(&right) >= count {
        return Some(vec![source]);
    }
    let selector = source.keys().next()?.constraints.clone();
    let mut result = Vec::new();
    for factor in [left, right] {
        let mut guarded = ExactAggregate::new();
        let mut atoms = 0;
        for (entry, coefficients) in factor {
            for (phase, coefficient) in coefficients {
                let mut constraints = entry.constraints.clone();
                constraints.extend(selector.iter().cloned());
                append(
                    WorkingTerm {
                        constraints,
                        coefficient,
                        phase,
                        paths: BTreeSet::new(),
                    },
                    &mut guarded,
                    &mut atoms,
                    context,
                )?;
            }
        }
        result.push(guarded);
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored tensor refinement: {count} -> {:?}",
            result.iter().map(size).collect::<Vec<_>>()
        );
    }
    Some(result)
}
