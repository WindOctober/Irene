//! Exact constant algebra shared by the EQ reducers. No counterexample search.

use super::*;
use crate::ir::{NumericExpr, NumericExprKind};
use crate::symbolic::PhaseCoefficient;

const MAX_ATOMS: usize = 1024;
const MAX_CELLS: usize = 32768;
const MAX_CONSTANT_LEAVES: usize = 1024;
const MAX_WORK: usize = 1_000_000;
const MAX_ARITHMETIC: usize = 100_000;
const MAX_RATIONAL_BITS: u64 = 4096;
// The representation is sparse: no vector of this field's degree is allocated.
const ROOT_ORDER: u64 = 1 << 62;
const DEGREE: u64 = ROOT_ORDER / 2;
const MAX_VALUE_TERMS: usize = 1024;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Cyclotomic(BTreeMap<u64, BigRational>);

struct Budget {
    nodes: usize,
    work: usize,
    arithmetic: usize,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            nodes: MAX_CONSTANT_LEAVES,
            work: MAX_WORK,
            arithmetic: MAX_ARITHMETIC,
        }
    }
}

fn spend(remaining: &mut usize, amount: usize) -> Option<()> {
    if amount > *remaining {
        *remaining = 0;
        return None;
    }
    *remaining -= amount;
    Some(())
}

fn small_rational(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

impl Cyclotomic {
    fn add_term(&mut self, power: u64, mut value: BigRational, budget: &mut Budget) -> Option<()> {
        spend(&mut budget.arithmetic, 1)?;
        if !small_rational(&value) {
            return None;
        }
        let power = power % ROOT_ORDER;
        let power = if power >= DEGREE {
            value = -value;
            power - DEGREE
        } else {
            power
        };
        let value = self.0.remove(&power).unwrap_or_else(|| integer(0)) + value;
        if !small_rational(&value) {
            return None;
        }
        if value != integer(0) {
            self.0.insert(power, value);
        }
        if self.0.len() > MAX_VALUE_TERMS {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density cyclotomic support refused: terms={} arithmetic_remaining={}",
                    self.0.len(),
                    budget.arithmetic
                );
            }
            return None;
        }
        Some(())
    }

    fn monomial(power: u64, value: BigRational, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        result.add_term(power, value, budget)?;
        Some(result)
    }

    fn add(mut self, other: Self, budget: &mut Budget) -> Option<Self> {
        for (power, value) in other.0 {
            self.add_term(power, value, budget)?;
        }
        Some(self)
    }

    fn multiply(&self, other: &Self, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        for (left_power, left) in &self.0 {
            for (right_power, right) in &other.0 {
                spend(&mut budget.arithmetic, 1)?;
                result.add_term(left_power + right_power, left * right, budget)?;
            }
        }
        Some(result)
    }
}

fn exponent(coefficient: &PhaseCoefficient) -> Option<u64> {
    let value = coefficient.as_rational()?;
    if !small_rational(&value) {
        return None;
    }
    let value = value * BigInt::from(ROOT_ORDER);
    if value.denom() != &BigInt::from(1) {
        return None;
    }
    value.numer().try_into().ok()
}

/// Only closed Boolean constants are admitted; no assignment is synthesized.
fn boolean(polynomial: &KernelBooleanPolynomial) -> Option<bool> {
    if polynomial.is_zero() {
        Some(false)
    } else if polynomial.is_one() {
        Some(true)
    } else {
        None
    }
}

fn rational_root(value: &BigRational) -> Option<BigRational> {
    if !small_rational(value) || value < &integer(0) {
        return None;
    }
    let numerator = value.numer().sqrt();
    let denominator = value.denom().sqrt();
    (&numerator * &numerator == *value.numer() && &denominator * &denominator == *value.denom())
        .then(|| BigRational::new(numerator, denominator))
}

fn scalar(value: &KernelScalar, budget: &mut Budget) -> Option<Cyclotomic> {
    spend(&mut budget.work, 1)?;
    match value {
        KernelScalar::Rational(value) => Cyclotomic::monomial(0, value.clone(), budget),
        KernelScalar::Neg(value) => {
            let value = scalar(value, budget)?;
            let minus_one = Cyclotomic::monomial(0, integer(-1), budget)?;
            value.multiply(&minus_one, budget)
        }
        KernelScalar::Add(left, right) => scalar(left, budget)?.add(scalar(right, budget)?, budget),
        KernelScalar::Mul(left, right) => {
            scalar(left, budget)?.multiply(&scalar(right, budget)?, budget)
        }
        KernelScalar::Sqrt(value) => {
            let KernelScalar::Rational(value) = value.as_ref() else {
                return None;
            };
            if let Some(root) = rational_root(value) {
                return Cyclotomic::monomial(0, root, budget);
            }
            if !small_rational(value) || value < &integer(0) {
                return None;
            }
            // sqrt(r) = sqrt(2r)/2 * (zeta^(N/8) - zeta^(3N/8)).
            let factor = rational_root(&(value * integer(2)))? / integer(2);
            let mut result = Cyclotomic::monomial(ROOT_ORDER / 8, factor.clone(), budget)?;
            result.add_term(3 * ROOT_ORDER / 8, -factor, budget)?;
            Some(result)
        }
        KernelScalar::Inverse(value) => {
            let KernelScalar::Rational(value) = value.as_ref() else {
                return None;
            };
            if value == &integer(0) {
                return None;
            }
            Cyclotomic::monomial(0, value.recip(), budget)
        }
        KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => {
            let power = exponent(&PhaseCoefficient::angle(angle.clone(), integer(1)))?;
            let positive = Cyclotomic::monomial(power, ratio(1, 2), budget)?;
            let negative = Cyclotomic::monomial(
                (ROOT_ORDER - power) % ROOT_ORDER,
                if matches!(value, KernelScalar::Sin(_)) {
                    ratio(-1, 2)
                } else {
                    ratio(1, 2)
                },
                budget,
            )?;
            let result = positive.add(negative, budget)?;
            if matches!(value, KernelScalar::Sin(_)) {
                // 1/i = -i = zeta^(3N/4).
                result.multiply(
                    &Cyclotomic::monomial(3 * ROOT_ORDER / 4, integer(1), budget)?,
                    budget,
                )
            } else {
                Some(result)
            }
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition)? {
                when_true
            } else {
                when_false
            },
            budget,
        ),
    }
}

fn evaluate(source: &ExactAggregate, budget: &mut Budget) -> Option<Cyclotomic> {
    let mut result = Cyclotomic::default();
    for (entry, coefficients) in source {
        let mut active = true;
        for constraint in &entry.constraints {
            active &= !boolean(constraint)?;
        }
        if !active {
            continue;
        }
        for (phase, coefficient) in coefficients {
            let mut power = 0u64;
            for (monomial, coefficient) in phase.terms() {
                if monomial.variables().next().is_some() {
                    return None;
                }
                power = (power + exponent(coefficient)?) % ROOT_ORDER;
            }
            let phase = Cyclotomic::monomial(power, integer(1), budget)?;
            let coefficient = scalar(coefficient, budget).or_else(|| {
                let specialized = normalized_constant_scalar(coefficient, budget)?;
                scalar(&specialized, budget)
            })?;
            result = result.add(coefficient.multiply(&phase, budget)?, budget)?;
        }
    }
    Some(result)
}

/// A constant cofactor can be rational even when its individual radical
/// factors lie outside this field. Select the constant scalar branches,
/// then normalize the WHOLE scalar without erasing the original phase.
fn normalized_constant_scalar(value: &KernelScalar, budget: &mut Budget) -> Option<KernelScalar> {
    let mut geometry = Geometry { cells: 0 };
    geometry.scalar(value, 0)?;
    if geometry.cells > 256 {
        return None;
    }
    spend(&mut budget.work, 3 * geometry.cells.max(1))?;
    fn specialize(value: &KernelScalar) -> Option<KernelScalar> {
        Some(match value {
            KernelScalar::Rational(r) => {
                if r.numer().bits() > 256 || r.denom().bits() > 256 {
                    return None;
                }
                value.clone()
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => specialize(if boolean(condition)? {
                when_true
            } else {
                when_false
            })?,
            KernelScalar::Add(a, b) => {
                KernelScalar::Add(Box::new(specialize(a)?), Box::new(specialize(b)?))
            }
            KernelScalar::Mul(a, b) => {
                KernelScalar::Mul(Box::new(specialize(a)?), Box::new(specialize(b)?))
            }
            KernelScalar::Neg(a) => KernelScalar::Neg(Box::new(specialize(a)?)),
            KernelScalar::Sqrt(a) => {
                let a = normalize_scalar(specialize(a)?);
                if !matches!(&a, KernelScalar::Rational(r) if r >= &integer(0)) {
                    return None;
                }
                KernelScalar::Sqrt(Box::new(a))
            }
            KernelScalar::Inverse(a) => {
                let a = normalize_scalar(specialize(a)?);
                if !matches!(&a, KernelScalar::Rational(r) if r != &integer(0)) {
                    return None;
                }
                KernelScalar::Inverse(Box::new(a))
            }
            KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => {
                if !exact_trig::admitted(angle, &mut 64) {
                    return None;
                }
                value.clone()
            }
        })
    }
    let result = normalize_scalar(specialize(value)?);
    scalar_within_budget(&result).then_some(result)
}

struct Geometry {
    cells: usize,
}

impl Geometry {
    fn charge(&mut self, amount: usize) -> Option<()> {
        self.cells = self.cells.checked_add(amount)?;
        (self.cells <= MAX_CELLS).then_some(())
    }

    fn boolean(&mut self, value: &KernelBooleanPolynomial) -> Option<()> {
        self.charge(1)?;
        for monomial in value.terms() {
            self.charge(1)?;
            if monomial.variables().next().is_some() {
                return None;
            }
        }
        Some(())
    }

    fn numeric(&mut self, value: &NumericExpr, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth >= 64 {
            return None;
        }
        match &value.kind {
            NumericExprKind::Rational(value) => small_rational(value).then_some(()),
            NumericExprKind::Neg(value) => self.numeric(value, depth + 1),
            NumericExprKind::Add(left, right)
            | NumericExprKind::Sub(left, right)
            | NumericExprKind::Mul(left, right)
            | NumericExprKind::Div(left, right) => {
                self.numeric(left, depth + 1)?;
                self.numeric(right, depth + 1)
            }
            _ => Some(()),
        }
    }

    fn scalar(&mut self, value: &KernelScalar, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth >= 64 {
            return None;
        }
        match value {
            KernelScalar::Rational(_) => Some(()),
            KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => self.numeric(angle, 0),
            KernelScalar::Sqrt(value) | KernelScalar::Neg(value) | KernelScalar::Inverse(value) => {
                self.scalar(value, depth + 1)
            }
            KernelScalar::Add(left, right) | KernelScalar::Mul(left, right) => {
                self.scalar(left, depth + 1)?;
                self.scalar(right, depth + 1)
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                self.boolean(condition)?;
                self.scalar(when_true, depth + 1)?;
                self.scalar(when_false, depth + 1)
            }
        }
    }
}

fn geometry(source: &ExactAggregate) -> Option<Geometry> {
    let mut geometry = Geometry { cells: 0 };
    let mut atoms = 0usize;
    for (entry, coefficients) in source {
        geometry.charge(1)?;
        for row in &entry.constraints {
            geometry.boolean(row)?;
        }
        atoms = atoms.checked_add(coefficients.len())?;
        if atoms > MAX_ATOMS {
            return None;
        }
        for (phase, scalar) in coefficients {
            geometry.scalar(scalar, 0)?;
            for (monomial, _) in phase.terms() {
                geometry.charge(1)?;
                if monomial.variables().next().is_some() {
                    return None;
                }
            }
        }
    }
    Some(geometry)
}

/// Shared across all constant leaves of one universal equality obligation.
#[derive(Default)]
pub(super) struct ConstantBudget(Budget);

/// Exact constant value restricted to one nonzero rational/root monomial.
/// This is not a test-point certificate: callers must cover every cofactor.
pub(super) fn constant_monomial(
    source: &ExactAggregate,
    budget: &mut ConstantBudget,
) -> Option<(BigRational, BigRational)> {
    let geometry = geometry(source)?;
    spend(&mut budget.0.nodes, 1)?;
    spend(&mut budget.0.work, geometry.cells.max(1))?;
    let value = evaluate(source, &mut budget.0)?;
    if value.0.len() != 1 {
        return None;
    }
    let (mut power, mut scalar) = value.0.into_iter().next()?;
    if scalar < integer(0) {
        scalar = -scalar;
        power += DEGREE;
    }
    Some((scalar, BigRational::new(power.into(), ROOT_ORDER.into())))
}

pub(super) fn constant_is_zero(source: &ExactAggregate, budget: &mut ConstantBudget) -> bool {
    let Some(geometry) = geometry(source) else {
        return false;
    };
    if spend(&mut budget.0.nodes, 1).is_none()
        || spend(&mut budget.0.work, geometry.cells.max(1)).is_none()
    {
        return false;
    }
    evaluate(source, &mut budget.0).is_some_and(|value| value.0.is_empty())
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{AstIdGenerator, NumericConstant};
    fn phase(turns: BigRational) -> KernelPhasePolynomial {
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(turns),
        );
        phase
    }

    fn aggregate(
        constraints: Vec<KernelBooleanPolynomial>,
        terms: Vec<(BigRational, KernelScalar)>,
    ) -> ExactAggregate {
        BTreeMap::from([(
            ExactEntry { constraints },
            terms.into_iter().map(|(p, c)| (phase(p), c)).collect(),
        )])
    }

    #[test]
    fn constant_algebra_rejects_free_and_bound_dependencies_in_every_field() {
        for variable in [
            KernelVariable::InputKet(0),
            KernelVariable::PathKet { term: 0, path: 0 },
        ] {
            let value = KernelBooleanPolynomial::variable(variable);
            let guarded = aggregate(
                vec![value.clone()],
                vec![(integer(0), KernelScalar::Rational(integer(1)))],
            );
            let selected = aggregate(
                vec![],
                vec![(
                    integer(0),
                    KernelScalar::Select {
                        condition: value.clone(),
                        when_true: Box::new(KernelScalar::Rational(integer(1))),
                        when_false: Box::new(KernelScalar::Rational(integer(0))),
                    },
                )],
            );
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(&value, PhaseCoefficient::rational(ratio(1, 2)));
            let phased = BTreeMap::from([(
                ExactEntry {
                    constraints: vec![],
                },
                BTreeMap::from([(phase, KernelScalar::Rational(integer(1)))]),
            )]);
            for source in [guarded, selected, phased] {
                assert!(constant_monomial(&source, &mut ConstantBudget::default()).is_none());
                assert!(!constant_is_zero(&source, &mut ConstantBudget::default()));
            }
        }
    }

    #[test]
    fn constant_scalar_normalization_retains_radical_products_and_phase() {
        let root = KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3))));
        let product = KernelScalar::Mul(Box::new(root.clone()), Box::new(root));
        let source = aggregate(vec![], vec![(ratio(1, 8), product)]);
        assert_eq!(
            constant_monomial(&source, &mut ConstantBudget::default()),
            Some((integer(3), ratio(1, 8))),
        );
        for (condition, expected) in [
            (KernelBooleanPolynomial::zero(), integer(2)),
            (KernelBooleanPolynomial::one(), integer(1)),
        ] {
            let source = aggregate(
                vec![],
                vec![(
                    integer(0),
                    KernelScalar::Select {
                        condition,
                        when_true: Box::new(KernelScalar::Rational(integer(1))),
                        when_false: Box::new(KernelScalar::Rational(integer(2))),
                    },
                )],
            );
            assert_eq!(
                constant_monomial(&source, &mut ConstantBudget::default()),
                Some((expected, integer(0))),
            );
        }
    }

    #[test]
    fn cyclotomic_products_cover_all_root_pairs_and_exact_cancellation() {
        for left in 0..256 {
            for right in 0..256 {
                let mut budget = Budget::default();
                let a = Cyclotomic::monomial(left * (ROOT_ORDER / 256), ratio(2, 3), &mut budget)
                    .unwrap();
                let b = Cyclotomic::monomial(right * (ROOT_ORDER / 256), ratio(3, 5), &mut budget)
                    .unwrap();
                let power = ((left + right) % 256) * (ROOT_ORDER / 256);
                let expected = BTreeMap::from([(
                    power % DEGREE,
                    if power >= DEGREE {
                        ratio(-2, 5)
                    } else {
                        ratio(2, 5)
                    },
                )]);
                assert_eq!(a.multiply(&b, &mut budget).unwrap().0, expected);
            }
        }
        let mut sum = Cyclotomic::default();
        let mut budget = Budget::default();
        for power in 0..256 {
            sum.add_term(power * (ROOT_ORDER / 256), integer(1), &mut budget)
                .unwrap();
        }
        assert!(sum.0.is_empty());
    }

    #[test]
    fn sparse_high_order_powers_and_representation_boundaries() {
        let powers = [0, 1, 2, DEGREE - 1, DEGREE, DEGREE + 1, ROOT_ORDER - 1];
        for left in powers {
            for right in powers {
                let mut budget = Budget::default();
                let a = Cyclotomic::monomial(left, integer(1), &mut budget).unwrap();
                let b = Cyclotomic::monomial(right, integer(1), &mut budget).unwrap();
                let power = (left + right) % ROOT_ORDER;
                assert_eq!(
                    a.multiply(&b, &mut budget).unwrap().0,
                    BTreeMap::from([(
                        power % DEGREE,
                        integer(if power >= DEGREE { -1 } else { 1 })
                    )])
                );
            }
        }
        assert_eq!(
            exponent(&PhaseCoefficient::rational(ratio(1, ROOT_ORDER as i64))),
            Some(1)
        );
        assert_eq!(
            exponent(&PhaseCoefficient::rational(BigRational::new(
                BigInt::from(1),
                BigInt::from(ROOT_ORDER) * 2,
            ))),
            None
        );
        let mut budget = Budget::default();
        let mut value = Cyclotomic::default();
        for power in 0..MAX_VALUE_TERMS {
            value
                .add_term(power as u64, integer(1), &mut budget)
                .unwrap();
        }
        assert!(
            value
                .add_term(MAX_VALUE_TERMS as u64, integer(1), &mut budget)
                .is_none()
        );
    }

    #[test]
    fn exact_trigonometric_values_and_nonnegative_radicals() {
        for numerator in 0..256 {
            let mut ids = AstIdGenerator::default();
            let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
            let scale = ids.node(NumericExprKind::Rational(ratio(numerator, 128)));
            let angle = ids.node(NumericExprKind::Mul(Box::new(pi), Box::new(scale)));
            let mut budget = Budget::default();
            let sin = scalar(&KernelScalar::Sin(angle.clone()), &mut budget).unwrap();
            let cos = scalar(&KernelScalar::Cos(angle), &mut budget).unwrap();
            let squares = sin
                .multiply(&sin, &mut budget)
                .unwrap()
                .add(cos.multiply(&cos, &mut budget).unwrap(), &mut budget)
                .unwrap();
            assert_eq!(squares.0, BTreeMap::from([(0, integer(1))]));
            if numerator == 64 {
                assert_eq!(sin.0, BTreeMap::from([(0, integer(1))]));
            }
        }
        for value in [
            ratio(0, 1),
            ratio(1, 2),
            ratio(2, 1),
            ratio(8, 9),
            ratio(9, 2),
        ] {
            let mut budget = Budget::default();
            let root = scalar(
                &KernelScalar::Sqrt(Box::new(KernelScalar::Rational(value.clone()))),
                &mut budget,
            )
            .unwrap();
            let square = root.multiply(&root, &mut budget).unwrap();
            let expected = Cyclotomic::monomial(0, value, &mut budget).unwrap();
            assert_eq!(square, expected);
        }
    }

    #[test]
    fn constant_zero_budget_is_shared_and_all_free_branches_must_pass() {
        let terms = vec![
            (ratio(1, 8), KernelScalar::Rational(integer(1))),
            (ratio(3, 8), KernelScalar::Rational(integer(-1))),
            (
                integer(0),
                KernelScalar::Neg(Box::new(KernelScalar::Sqrt(Box::new(
                    KernelScalar::Rational(integer(2)),
                )))),
            ),
        ];
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let mut source = aggregate(vec![x.clone()], terms.clone());
        source.extend(aggregate(vec![x.complement()], terms));
        let mut algebra = ConstantBudget(Budget {
            nodes: 1,
            ..Budget::default()
        });
        let mut free_budget = MAX_FREE_SPLITS;
        assert!(!zero_by_free_splitting_with_algebra(
            source.clone(),
            &mut free_budget,
            &mut algebra,
            0
        ));
        let mut free_budget = MAX_FREE_SPLITS;
        assert!(zero_by_free_splitting(source, &mut free_budget, 0));
        let mut nonzero = aggregate(
            vec![x.clone()],
            vec![(integer(0), KernelScalar::Rational(integer(1)))],
        );
        nonzero.extend(aggregate(
            vec![x.complement()],
            vec![(integer(0), KernelScalar::Rational(integer(-1)))],
        ));
        let mut free_budget = MAX_FREE_SPLITS;
        assert!(!zero_by_free_splitting(nonzero, &mut free_budget, 0));
    }
}
