use super::*;
use std::convert::Infallible;

fn v(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}

fn value(p: &BooleanPolynomial, bits: usize) -> bool {
    p.evaluate::<Infallible>(|variable| match variable {
        Variable::Path(i) => Ok(bits & (1 << i) != 0),
        _ => unreachable!(),
    })
    .unwrap()
}

// Evaluate coefficients independently of the phase rewriting routines.
// Keep symbolic atoms separate: they must cancel exactly, not modulo one.
fn evaluate(p: &PhasePolynomial, bits: usize) -> (BigRational, BTreeMap<AngleBasis, BigRational>) {
    let mut turns = integer(0);
    let mut atoms = BTreeMap::new();
    for (selector, coefficient) in p.selectors() {
        if value(&selector, bits) {
            turns += &coefficient.rational_turns;
            for (atom, scale) in &coefficient.angle_terms {
                *atoms.entry(atom.clone()).or_insert_with(|| integer(0)) += scale;
            }
        }
    }
    atoms.retain(|_, scale| *scale != integer(0));
    (modulo_one(turns), atoms)
}

#[test]
fn weighted_xor_matches_boolean_truth_for_rational_and_symbolic_coefficients() {
    let atoms = [v(0), v(1).complement(), v(2).and(&v(3)), v(0).xor(&v(2))];
    let mut coefficients = Vec::new();
    for denominator in [2, 3, 4, 8, 16] {
        for numerator in [-9, -1, 1, 3, 8] {
            coefficients.push(PhaseCoefficient::rational(ratio(numerator, denominator)));
        }
    }
    coefficients.push(PhaseCoefficient {
        rational_turns: ratio(3, 8),
        angle_terms: BTreeMap::from([
            (AngleBasis::Input(SymbolId(0)), ratio(-7, 3)),
            (AngleBasis::Radian, ratio(2, 5)),
        ]),
    });
    for f in &atoms {
        for g in &atoms {
            for coefficient in &coefficients {
                let mut phase = PhasePolynomial::zero();
                phase.add_boolean(&f.xor(g), coefficient.clone());
                for bits in 0..16 {
                    let expected = if value(f, bits) ^ value(g, bits) {
                        (
                            coefficient.rational_turns.clone(),
                            coefficient.angle_terms.clone(),
                        )
                    } else {
                        (integer(0), BTreeMap::new())
                    };
                    assert_eq!(evaluate(&phase, bits), expected);
                }
            }
        }
    }
}

#[test]
fn xor_rewrite_boundary_preserves_all_assignments() {
    // Both sides of the local fanin limit must retain exact semantics.
    for count in [8, 9] {
        let parity = BooleanPolynomial::xor_all((0..count).map(v));
        let mut phase = PhasePolynomial::zero();
        phase.add_boolean(&parity, PhaseCoefficient::rational(ratio(1, 3)));
        for bits in 0usize..(1 << count) {
            let expected = if bits.count_ones() % 2 == 1 {
                ratio(1, 3)
            } else {
                integer(0)
            };
            assert_eq!(evaluate(&phase, bits), (expected, BTreeMap::new()));
        }
    }
}

#[test]
fn half_turns_merge_and_cancel_without_expanding_products() {
    let f = v(0).and(&v(1).xor(&v(2)));
    let g = v(0).and(&v(1).xor(&v(3)));
    let mut phase = PhasePolynomial::zero();
    for selector in [&f, &g] {
        phase.add_boolean(selector, PhaseCoefficient::rational(ratio(1, 2)));
    }
    for bits in 0..16 {
        let expected = if value(&f, bits) ^ value(&g, bits) {
            ratio(1, 2)
        } else {
            integer(0)
        };
        assert_eq!(evaluate(&phase, bits), (expected, BTreeMap::new()));
    }
    assert_eq!(phase.selectors().count(), 1);
    let cancellation = v(0).and(&v(2).xor(&v(3)));
    phase.add_boolean(&cancellation, PhaseCoefficient::rational(ratio(1, 2)));
    assert_eq!(phase.selectors().count(), 0);
}

#[test]
fn coincident_coefficients_cancel_modulo_one_turn() {
    let p = v(0).and(&v(1).complement());
    let mut phase = PhasePolynomial::zero();
    for coefficient in [ratio(-1, 8), ratio(3, 8), ratio(3, 4)] {
        phase.add_boolean(&p, PhaseCoefficient::rational(coefficient));
    }
    for bits in 0..4 {
        assert_eq!(evaluate(&phase, bits), (integer(0), BTreeMap::new()));
    }
    assert_eq!(phase.selectors().count(), 0);
}

#[test]
fn substitution_preserves_truth_and_handles_selector_collisions() {
    let mut original = PhasePolynomial::zero();
    original.add_boolean(&v(0).xor(&v(1)), PhaseCoefficient::rational(ratio(1, 8)));
    original.add_boolean(&v(0).and(&v(2)), PhaseCoefficient::rational(ratio(3, 8)));
    original.add_boolean(&v(1).and(&v(2)), PhaseCoefficient::rational(ratio(5, 8)));
    for replacement in [
        v(1),
        v(1).complement(),
        BooleanPolynomial::zero(),
        BooleanPolynomial::one(),
    ] {
        let mut rewritten = original.clone();
        rewritten.substitute(&Variable::Path(0), &replacement);
        for bits in 0..8 {
            let source_bits = (bits & !1) | usize::from(value(&replacement, bits));
            assert_eq!(evaluate(&rewritten, bits), evaluate(&original, source_bits));
        }
    }
    let mut swapped = original.clone();
    swapped.map_variables(|variable| match variable {
        Variable::Path(0) => v(1),
        Variable::Path(1) => v(0),
        other => BooleanPolynomial::variable(other.clone()),
    });
    for bits in 0..8 {
        let source_bits = (bits & !3) | ((bits & 1) << 1) | ((bits & 2) >> 1);
        assert_eq!(evaluate(&swapped, bits), evaluate(&original, source_bits));
    }
}

#[test]
fn global_phase_removal_preserves_relative_phases_not_just_output_bits() {
    let mut original = PhasePolynomial::zero();
    original.add_boolean(&v(0).complement(), PhaseCoefficient::rational(ratio(1, 2)));
    original.add_boolean(
        &v(1).complement(),
        PhaseCoefficient {
            rational_turns: ratio(1, 8),
            angle_terms: BTreeMap::from([(AngleBasis::Input(SymbolId(0)), ratio(2, 3))]),
        },
    );
    let mut reduced = original.clone();
    reduced.remove_global_phase();
    assert_eq!(evaluate(&reduced, 0), (integer(0), BTreeMap::new()));
    let (constant, constant_atoms) = evaluate(&original, 0);
    for bits in 0..4 {
        let (before, mut before_atoms) = evaluate(&original, bits);
        let (after, after_atoms) = evaluate(&reduced, bits);
        for (atom, scale) in &constant_atoms {
            *before_atoms
                .entry(atom.clone())
                .or_insert_with(|| integer(0)) -= scale;
        }
        before_atoms.retain(|_, scale| *scale != integer(0));
        assert_eq!(modulo_one(before - after), constant);
        assert_eq!(before_atoms, after_atoms);
    }
    // Z is not the identity, even though both preserve computational-basis bits.
    assert_ne!(evaluate(&reduced, 0), evaluate(&reduced, 1));
}
