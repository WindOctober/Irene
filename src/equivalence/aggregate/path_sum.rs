//! Closed-form sums of bound paths in an algebraic density-kernel term.
use super::{
    KernelBooleanPolynomial, KernelMonomial, KernelPhasePolynomial, KernelScalar, KernelVariable,
    WorkingTerm,
};
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

// Share the algebra with HPS reduction, but retain kernel dependency checks.
pub(super) type PhaseProfile = crate::symbolic::path_rules::PhaseProfile<KernelBooleanPolynomial>;

/// Classifies `phase = phase_without_v + v * coefficient` for exact local sums.
fn phase_profile(phase: &KernelPhasePolynomial, variable: &KernelVariable) -> PhaseProfile {
    let mut present = false;
    let mut constant = integer(0);
    let mut parity_terms = Vec::new();
    for (monomial, coefficient) in phase.terms_containing(variable) {
        present = true;
        let Some(coefficient) = coefficient.as_rational() else {
            return PhaseProfile::Unsupported;
        };
        let reduced = monomial.without(variable);
        if reduced == KernelMonomial::one() {
            constant = coefficient;
        } else if coefficient == ratio(1, 2) {
            parity_terms.push(reduced);
        } else {
            return PhaseProfile::Unsupported;
        }
    }
    let parity = KernelBooleanPolynomial::from_monomials(parity_terms);
    PhaseProfile::classify(
        present,
        constant,
        parity,
        KernelBooleanPolynomial::complement,
    )
}

impl WorkingTerm {
    /// Graph-native Fourier rule using Boolean cofactors, without ANF expansion.
    /// Returns the weight factor; the caller removes the binder and multiplies it in.
    pub(super) fn graph_fourier(&mut self, variable: &KernelVariable) -> Option<KernelScalar> {
        if !self.paths.contains(variable)
            || !variable.is_bound_path()
            || self.occurs_outside_phase(variable)
        {
            return None;
        }
        let mut parity = KernelBooleanPolynomial::zero();
        let mut base = KernelPhasePolynomial::default();
        for (p, c) in self.phase.selectors() {
            if !p.variables().contains(variable) {
                base.add_boolean(&p, c);
                continue;
            }
            if c.as_rational() != Some(ratio(1, 2)) {
                return None;
            }
            let p0 = p.substitute(variable, &KernelBooleanPolynomial::zero());
            let p1 = p.substitute(variable, &KernelBooleanPolynomial::one());
            parity = parity.xor(&p0.xor(&p1));
            base.add_boolean(&p0, c);
        }
        self.phase = base;
        // Equal cofactors prove independence; remove syntactic binder uses too.
        self.coefficient = self
            .coefficient
            .substitute(variable, &KernelBooleanPolynomial::zero());
        self.constraints.push(parity);
        Some(KernelScalar::Rational(integer(2)))
    }

    pub(super) fn phase_sum_profile(&self, variable: &KernelVariable) -> PhaseProfile {
        if !self.paths.contains(variable)
            || !variable.is_bound_path()
            || !self.phase.is_algebraic()
            || self.occurs_outside_phase(variable)
        {
            return PhaseProfile::Unsupported;
        }
        phase_profile(&self.phase, variable)
    }

    pub(super) fn occurs_outside_phase(&self, variable: &KernelVariable) -> bool {
        self.constraints
            .iter()
            .any(|value| value.variables().contains(variable))
            || self
                .coefficient
                .substitute(variable, &KernelBooleanPolynomial::zero())
                != self
                    .coefficient
                    .substitute(variable, &KernelBooleanPolynomial::one())
    }
}

impl PhaseProfile {
    /// Exact phase additions; the caller checks their expansion cost before applying.
    pub(super) fn omega_additions(
        &self,
    ) -> Option<[(KernelBooleanPolynomial, PhaseCoefficient); 2]> {
        let Self::Omega { parity, sign } = self else {
            return None;
        };
        let (constant, coefficient) = sign.phase_coefficients();
        Some([
            (
                KernelBooleanPolynomial::one(),
                PhaseCoefficient::rational(constant),
            ),
            (parity.clone(), PhaseCoefficient::rational(coefficient)),
        ])
    }

    /// Applies a profile obtained from this unchanged term's phase_sum_profile.
    /// Returns the exact weight factor; the caller multiplies it into the scalar
    /// and removes the binder. Unsupported profiles leave the term unchanged.
    pub(super) fn apply(
        self,
        term: &mut WorkingTerm,
        variable: &KernelVariable,
    ) -> Option<KernelScalar> {
        match self {
            Self::Absent => Some(KernelScalar::Rational(integer(2))),
            Self::Fourier(relation) => {
                term.phase
                    .substitute(variable, &KernelBooleanPolynomial::zero());
                term.constraints.push(relation);
                Some(KernelScalar::Rational(integer(2)))
            }
            omega @ Self::Omega { .. } => {
                let additions = omega.omega_additions().unwrap();
                term.phase
                    .substitute(variable, &KernelBooleanPolynomial::zero());
                for (polynomial, coefficient) in additions {
                    term.phase.add_boolean(&polynomial, coefficient);
                }
                Some(KernelScalar::Sqrt(Box::new(KernelScalar::Rational(
                    integer(2),
                ))))
            }
            Self::Unsupported => None,
        }
    }
}

fn integer(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

#[cfg(test)]
mod tests;
