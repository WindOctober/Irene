//! Representation-independent algebra for one Boolean path sum.
//!
//! Callers must first certify that the path is bound and has no forbidden
//! dependencies. HPS histories and kernel constraints have different admission
//! rules; this module deliberately does not decide those conditions.
use num_rational::BigRational;

pub(crate) enum PhaseProfile<P> {
    Absent,
    Fourier(P),
    Omega { parity: P, sign: OmegaSign },
    Unsupported,
}

#[derive(Clone, Copy)]
pub(crate) enum OmegaSign {
    Positive,
    Negative,
}

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

impl<P> PhaseProfile<P> {
    /// Classify the complete coefficient c + parity/2 of the summed path.
    /// The caller supplies c reduced modulo one and a representation adapter.
    pub(crate) fn classify(
        present: bool,
        constant: BigRational,
        parity: P,
        complement: impl FnOnce(&P) -> P,
    ) -> Self {
        if !present {
            Self::Absent
        } else if constant == ratio(0, 1) {
            Self::Fourier(parity)
        } else if constant == ratio(1, 2) {
            Self::Fourier(complement(&parity))
        } else if constant == ratio(1, 4) {
            Self::Omega {
                parity,
                sign: OmegaSign::Positive,
            }
        } else if constant == ratio(3, 4) {
            Self::Omega {
                parity,
                sign: OmegaSign::Negative,
            }
        } else {
            Self::Unsupported
        }
    }
}

impl OmegaSign {
    /// sum_y i^(±y) (-1)^(y f) = sqrt(2) exp(2πi (a + b f)).
    pub(crate) fn phase_coefficients(self) -> (BigRational, BigRational) {
        match self {
            Self::Positive => (ratio(1, 8), ratio(-1, 4)),
            Self::Negative => (ratio(-1, 8), ratio(1, 4)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn supported_quarter_turns_and_complement_are_exact() {
        for parity in [false, true] {
            let classify = |n, d| PhaseProfile::classify(true, ratio(n, d), parity, |p| !p);
            assert!(matches!(classify(0, 1), PhaseProfile::Fourier(p) if p == parity));
            assert!(matches!(classify(1, 2), PhaseProfile::Fourier(p) if p != parity));
            assert!(matches!(classify(1, 4),
                PhaseProfile::Omega { parity: p, sign: OmegaSign::Positive } if p == parity));
            assert!(matches!(classify(3, 4),
                PhaseProfile::Omega { parity: p, sign: OmegaSign::Negative } if p == parity));
            for n in [1, 3, 5, 7] {
                assert!(matches!(classify(n, 8), PhaseProfile::Unsupported));
            }
        }
    }

    #[test]
    fn absent_path_does_not_inspect_or_complement_parity() {
        assert!(matches!(
            PhaseProfile::classify(false, ratio(0, 1), (), |_| panic!("absent path")),
            PhaseProfile::Absent
        ));
    }

    #[test]
    fn omega_phases_match_both_values_of_the_parity() {
        for (sign, expected) in [
            (OmegaSign::Positive, [ratio(1, 8), ratio(-1, 8)]),
            (OmegaSign::Negative, [ratio(-1, 8), ratio(1, 8)]),
        ] {
            let (constant, coefficient) = sign.phase_coefficients();
            assert_eq!(constant, expected[0]);
            assert_eq!(constant + coefficient, expected[1]);
        }
    }
}
