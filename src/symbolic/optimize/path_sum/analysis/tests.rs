use super::*;
use crate::symbolic::{HybridMemory, PhasePolynomial};

fn fixture() -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::one(),
        path_support: [0, 1].into(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}

#[test]
fn exact_witness_preserves_joint_cancellations_and_rejects_nonquarter_derivative() {
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = BooleanPolynomial::variable(Variable::Path(1));
    let mut c = fixture();
    c.phase
        .add_boolean(&y, PhaseCoefficient::rational(ratio(1, 8)));
    c.phase
        .add_boolean(&y.and(&z), PhaseCoefficient::rational(ratio(1, 2)));
    assert!(
        Analysis::new(&c)
            .query(&Variable::Path(0))
            .excludes_local_profile()
    );
    // y*z/8 + y*!z/8 + y/8 = y/4. Looking at individual denominators
    // would incorrectly reject this valid joint Omega profile.
    c.phase = PhasePolynomial::zero();
    for selector in [y.and(&z), y.and(&z.complement()), y] {
        c.phase
            .add_boolean(&selector, PhaseCoefficient::rational(ratio(1, 8)));
    }
    let analysis = Analysis::new(&c);
    let mut query = analysis.query(&Variable::Path(0));
    assert!(!query.excludes_local_profile());
    assert!(matches!(
        joint_phase::profile(&mut query),
        PhaseProfile::Omega { .. }
    ));
}

#[test]
fn witness_never_rejects_an_accepted_exact_profile() {
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = BooleanPolynomial::variable(Variable::Path(1));
    let selectors = [y.clone(), y.xor(&z), y.and(&z), y.and(&z.complement())];
    for code in 0..4096 {
        let mut c = fixture();
        for (i, selector) in selectors.iter().enumerate() {
            c.phase.add_boolean(
                selector,
                PhaseCoefficient::rational(ratio((code >> (3 * i)) & 7, 8)),
            );
        }
        let analysis = Analysis::new(&c);
        let mut query = analysis.query(&Variable::Path(0));
        let rejects = query.excludes_local_profile();
        let cheap = phase_profile_query(&mut query);
        let joint = joint_phase::profile(&mut query);
        if !matches!(cheap, PhaseProfile::Unsupported)
            || !matches!(joint, PhaseProfile::Unsupported)
        {
            assert!(!rejects, "phase coefficients encoded by {code}");
        }
    }
}

#[test]
fn bounded_index_fallback_keeps_every_relevant_term_and_order() {
    let mut c = fixture();
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = BooleanPolynomial::variable(Variable::Path(1));
    for selector in [&y, &z, &y.xor(&z)] {
        c.phase
            .add_boolean(selector, PhaseCoefficient::rational(ratio(1, 8)));
    }
    let indexed = Analysis::new(&c);
    let fallback = Analysis::with_limit(&c, 0);
    assert!(fallback.by_variable.is_none());
    for v in [Variable::Path(0), Variable::Path(1), Variable::Path(2)] {
        let mut a = indexed.query(&v);
        let mut b = fallback.query(&v);
        assert_eq!(a.len(), b.len());
        assert_eq!(a.excludes_local_profile(), b.excludes_local_profile());
        for i in 0..a.len() {
            assert_eq!(a.coefficient(i), b.coefficient(i));
            assert_eq!(a.cofactors(i), b.cofactors(i));
        }
    }
}

#[test]
fn rewrite_refreshes_dependencies_before_visiting_the_next_path() {
    let mut c = fixture();
    let a = BooleanPolynomial::variable(Variable::Path(0));
    let b = BooleanPolynomial::variable(Variable::Path(1));
    // Eliminating b adds a=0 and simplification removes a. A stale phase
    // profile for a must not eliminate a second time or multiply the scalar.
    c.phase
        .add_boolean(&a.and(&b), PhaseCoefficient::rational(ratio(1, 2)));
    assert!(reduce_path_sums(&mut c, false));
    assert!(c.path_support.is_empty());
    assert_eq!(c.scalar, Scalar::rational(integer(2)));
}
