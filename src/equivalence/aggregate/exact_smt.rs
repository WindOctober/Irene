//! Complete, bounded QF_BV encoding of a cyclotomic channel difference.
//!
//! Every atom is r * [guard] * zeta^power, optionally times positive sqrt(3).
//! Exponents intentionally wrap at 2^62. Coefficients NEVER wrap: after a
//! common positive denominator, W=bits(sum(abs(numerators)))+1 bounds every
//! signed partial sum. A fresh 61-bit index selects a basis coefficient after
//! zeta^(2^61)=-1 folding. SAT is exactly nonzero; UNSAT is exactly zero for
//! the COMPLETE admitted expression. No free-coordinate search or sampling.
//!
//! sqrt(3) is independent over Q(zeta_2^62): the quadratic subfields of a
//! 2-power cyclotomic field are Q(i), Q(sqrt(2)), Q(sqrt(-2)). Thus the two
//! rational coefficient blocks are independent. Products use sqrt(3)^2=3.

use super::*;

// The small dense operator backend has a separate work budget.
const MAX_WORK: usize = 2_000_000;
use crate::equivalence::smt::{Solver, SolverStatus, run_solver};
use crate::symbolic::PhaseCoefficient;

const ORDER: u64 = 1 << 62;
const HALF: u64 = ORDER / 2;
const MAX_ATOMS: usize = 8192;
const MAX_BITS: u64 = 32768;
const MAX_TEXT: usize = 16 * 1024 * 1024;

mod coefficient_dag;
mod contraction;
mod frontier;
mod guard_groups;
mod regions;
mod schedule;

pub(super) fn frontier_norm(circuit: &crate::ir::Program) -> Option<Vec<(u64, BigRational)>> {
    frontier::norm(circuit)
}

pub(super) fn prefer_frontier(circuit: &crate::ir::Program, paths: usize) -> bool {
    frontier::preferred(circuit, paths)
}

/// Contract a complete coherent scalar first, then take its squared modulus.
/// Reuses the ordinary bound-sum/coefficient arithmetic with no SMT query.
/// No partial contraction, symbolic guard, or radical is accepted as a value.
pub(super) fn closed_norm(t: WorkingTerm) -> Option<Vec<(u64, BigRational)>> {
    let kernel = DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    };
    let mut encoder = Encoder::new(&kernel)?;
    let start = std::time::Instant::now();
    let value = encoder.contract(&t).or_else(|| {
        if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
            eprintln!("unitary trace direct contraction refused paths={} remaining_work={} seconds={:.6}; trying bound sum", t.paths.len(), encoder.work, start.elapsed().as_secs_f64());
        }
        encoder.bound_sum(t)
    });
    let Some(value) = value else {
        if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
            eprintln!(
                "unitary trace bound sum refused remaining_work={} seconds={:.6}",
                encoder.work,
                start.elapsed().as_secs_f64()
            );
        }
        return None;
    };
    let result = encoder.closed_value_norm(value);
    if result.is_none() && std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary trace closed value norm refused remaining_work={}",
            encoder.work
        );
    }
    let result = result?;
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary trace cyclotomic contraction seconds={:.6} norm_terms={} work={}",
            start.elapsed().as_secs_f64(),
            result.len(),
            crate::equivalence::tuning::limits()
                .exact_work
                .saturating_sub(encoder.work)
        );
    }
    Some(result)
}

impl Encoder {
    /// Merge two closed, already canonical coefficient vectors. Equal basis
    /// entries require one rational addition; disjoint tails are transferred
    /// unchanged. This avoids rebuilding a map with zero-initialized entries.
    fn add_closed(&mut self, a: Polynomial, b: Polynomial) -> Option<Polynomial> {
        for values in [&a, &b] {
            if values.len() > MAX_ATOMS
                || values.iter().any(|x| {
                    x.guard != "true"
                        || x.weight == integer(0)
                        || x.weight.numer().bits() > MAX_BITS
                        || x.weight.denom().bits() > MAX_BITS
                        || !matches!(x.power, Power::Constant(p) if p < HALF)
                })
                || !values
                    .windows(2)
                    .all(|w| (&w[0].power, w[0].radical) < (&w[1].power, w[1].radical))
            {
                return None;
            }
        }
        let (mut a, mut b) = (a.into_iter().peekable(), b.into_iter().peekable());
        let mut out = Vec::new();
        while let (Some(x), Some(y)) = (a.peek(), b.peek()) {
            self.charge(1)?;
            match (&x.power, x.radical).cmp(&(&y.power, y.radical)) {
                std::cmp::Ordering::Less => out.push(a.next()?),
                std::cmp::Ordering::Greater => out.push(b.next()?),
                std::cmp::Ordering::Equal => {
                    let mut x = a.next()?;
                    x.weight += b.next()?.weight;
                    if x.weight.numer().bits() > MAX_BITS || x.weight.denom().bits() > MAX_BITS {
                        return None;
                    }
                    if x.weight != integer(0) {
                        out.push(x);
                    }
                }
            }
        }
        out.extend(a);
        out.extend(b);
        (out.len() <= MAX_ATOMS).then_some(out)
    }

    fn closed_value_norm(&mut self, value: Polynomial) -> Option<Vec<(u64, BigRational)>> {
        if value
            .iter()
            .any(|a| a.guard != "true" || !matches!(a.power, Power::Constant(_)))
        {
            return None;
        }
        let mut conjugate = value.clone();
        for atom in &mut conjugate {
            let Power::Constant(p) = atom.power else {
                return None;
            };
            atom.power = Power::Constant((ORDER - p) % ORDER);
        }
        let norm = self.multiply(value, conjugate)?;
        let mut result = Vec::new();
        for atom in norm {
            let Power::Constant(p) = atom.power else {
                return None;
            };
            if atom.guard != "true" || atom.radical {
                return None;
            }
            result.push((p, atom.weight));
        }
        result.sort_by_key(|(p, _)| *p);
        Some(result)
    }
}

/// Keep Boolean selectors available until coefficient lowering. The SMT name
/// is a cache of this exact modular expression, not its only representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
struct PhaseForm {
    constant: u64,
    selectors: BTreeMap<KernelBooleanPolynomial, u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Power {
    Constant(u64),
    Expr(String, u64),
    Structured(String, u64, std::sync::Arc<PhaseForm>),
}
impl Power {
    fn text(&self) -> String {
        match self {
            Self::Constant(n) => format!("(_ bv{n} 62)"),
            Self::Expr(s, _) | Self::Structured(s, _, _) => s.clone(),
        }
    }
    fn step(&self) -> u64 {
        match self {
            Self::Constant(n) => 1u64 << n.trailing_zeros().min(62),
            Self::Expr(_, step) | Self::Structured(_, step, _) => *step,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Atom {
    guard: String,
    power: Power,
    radical: bool,
    weight: BigRational,
}
type Polynomial = Vec<Atom>;

#[derive(Clone)]
struct Encoder {
    coordinates: Vec<KernelVariable>,
    bound: BTreeMap<KernelVariable, bool>,
    definitions: String,
    cache: BTreeMap<(String, String), String>,
    work: usize,
    schedule_attempts: usize,
    guards: BTreeMap<String, KernelBooleanPolynomial>,
}

fn exponent(c: &PhaseCoefficient) -> Option<u64> {
    let r = c.as_rational()? * BigInt::from(ORDER);
    r.is_integer()
        .then(|| r.to_integer().try_into().ok())
        .flatten()
}

fn rational_root(r: &BigRational) -> Option<BigRational> {
    if r < &integer(0) || r.numer().bits() > 4096 || r.denom().bits() > 4096 {
        return None;
    }
    let a = r.numer().sqrt();
    let b = r.denom().sqrt();
    (&a * &a == *r.numer() && &b * &b == *r.denom()).then(|| BigRational::new(a, b))
}

impl Encoder {
    fn new(kernel: &DensityKernel) -> Option<Self> {
        let n = kernel.input_pairs.len();
        let q = kernel.quantum_output_count;
        let c = kernel.classical_output_count;
        if n.checked_add(q)?.checked_mul(2)?.checked_add(c)? > 32768
            || kernel.input_pairs.iter().enumerate().any(|(i, p)| {
                p.ket != KernelVariable::InputKet(i) || p.bra != KernelVariable::InputBra(i)
            })
        {
            return None;
        }
        let coordinates = (0..n)
            .map(KernelVariable::InputKet)
            .chain((0..n).map(KernelVariable::InputBra))
            .chain((0..q).map(KernelVariable::QuantumOutputKet))
            .chain((0..q).map(KernelVariable::QuantumOutputBra))
            .chain((0..c).map(KernelVariable::ClassicalOutput))
            .collect::<Vec<_>>();
        let definitions = (0..coordinates.len())
            .map(|i| format!("(declare-fun u{i} () Bool)\n"))
            .collect();
        Some(Self {
            coordinates,
            bound: BTreeMap::new(),
            definitions,
            cache: BTreeMap::new(),
            work: crate::equivalence::tuning::limits().exact_work,
            schedule_attempts: 0,
            guards: BTreeMap::new(),
        })
    }
    fn charge(&mut self, n: usize) -> Option<()> {
        if n > self.work && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "density exact SMT work refused: need={n} remaining={}",
                self.work
            );
        }
        self.work = self.work.checked_sub(n)?;
        Some(())
    }
    fn probe_work_budget(&self, cap: usize) -> usize {
        self.work.min(cap)
    }
    fn define(&mut self, sort: &str, expression: String) -> Option<String> {
        self.charge(1)?;
        let key = (sort.to_owned(), expression);
        if let Some(name) = self.cache.get(&key) {
            return Some(name.clone());
        }
        if self.definitions.len().checked_add(key.1.len() + 100)? > MAX_TEXT {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density exact SMT text refused: current={} next={} limit={MAX_TEXT}",
                    self.definitions.len(),
                    key.1.len() + 100
                );
            }
            return None;
        }
        let name = format!("v{}", self.cache.len());
        self.definitions
            .push_str(&format!("(define-fun {name} () {sort} {})\n", key.1));
        self.cache.insert(key, name.clone());
        Some(name)
    }
    fn and(&mut self, a: String, b: String) -> Option<String> {
        if a == "false" || b == "false" {
            return Some("false".into());
        }
        if a == "true" || a == b {
            return Some(b);
        }
        if b == "true" {
            return Some(a);
        }
        let ir = self
            .guard_graph(&a)
            .zip(self.guard_graph(&b))
            // This is a structural mirror of an SMT conjunction, not an
            // algebraic elimination step. Preserve factored XAG structure:
            // multiplying materialized polynomial guards here can create 2^n
            // monomials even for n independent equality constraints.
            .map(|(a, b)| KernelBooleanPolynomial::from_graph(a.as_graph().and(&b.as_graph())));
        let name = self.define("Bool", format!("(and {a} {b})"))?;
        if let Some(ir) = ir {
            self.guards.insert(name.clone(), ir);
        }
        Some(name)
    }
    fn not(&mut self, a: String) -> Option<String> {
        match a.as_str() {
            "true" => Some("false".into()),
            "false" => Some("true".into()),
            _ => {
                let ir = self
                    .guard_graph(&a)
                    .map(|p| p.xor(&KernelBooleanPolynomial::one()));
                let name = self.define("Bool", format!("(not {a})"))?;
                if let Some(ir) = ir {
                    self.guards.insert(name.clone(), ir);
                }
                Some(name)
            }
        }
    }
    fn boolean(&mut self, p: &KernelBooleanPolynomial) -> Option<String> {
        let name = self.boolean_inner(p)?;
        if p.variables().iter().all(|v| !v.is_bound_path()) {
            self.guards.insert(name.clone(), p.clone());
        }
        Some(name)
    }
    fn boolean_inner(&mut self, p: &KernelBooleanPolynomial) -> Option<String> {
        if !p.is_algebraic() {
            let (network, variables) =
                crate::symbolic::BooleanPolynomial::graph_network(&[p.as_graph()]);
            let names = variables
                .iter()
                .map(|v| {
                    let v = KernelVariable::from_graph_variable(v);
                    if v.is_bound_path() {
                        self.bound.get(&v).map(bool::to_string)
                    } else {
                        self.coordinates
                            .iter()
                            .position(|x| *x == v)
                            .map(|i| format!("u{i}"))
                    }
                })
                .collect::<Option<Vec<_>>>()?;
            // define() hash-conses the generated gates across all selectors.
            let mut nodes: Vec<String> = Vec::new();
            for &[op, a, b] in &network.nodes {
                let value = match op {
                    0 => (a != 0).to_string(),
                    1 => names[a as usize].clone(),
                    2 => self.define(
                        "Bool",
                        format!("(xor {} {})", nodes[a as usize], nodes[b as usize]),
                    )?,
                    3 => self.and(nodes[a as usize].clone(), nodes[b as usize].clone())?,
                    _ => return None,
                };
                nodes.push(value);
            }
            return Some(nodes[*network.outputs.first()? as usize].clone());
        }
        let mut sum = "false".to_owned();
        for m in p.terms() {
            let product = self.monomial(m)?;
            sum = if sum == "false" {
                product
            } else if product == "false" {
                sum
            } else if sum == product {
                "false".into()
            } else {
                self.define("Bool", format!("(xor {sum} {product})"))?
            };
        }
        Some(sum)
    }
    fn monomial(&mut self, m: &KernelMonomial) -> Option<String> {
        let mut product = "true".to_owned();
        for v in m.variables() {
            self.charge(1)?;
            let value = if v.is_bound_path() {
                self.bound.get(v)?.to_string()
            } else {
                format!("u{}", self.coordinates.iter().position(|x| x == v)?)
            };
            product = self.and(product, value)?;
        }
        Some(product)
    }
    fn plus_power(&mut self, a: Power, b: Power) -> Option<Power> {
        if a == Power::Constant(0) {
            return Some(b);
        }
        if b == Power::Constant(0) {
            return Some(a);
        }
        if let (Some(a), Some(b)) = (a.form(), b.form()) {
            return self.lower_phase_form(a.combine(b, false));
        }
        match (&a, &b) {
            (Power::Constant(a), Power::Constant(b)) => Some(Power::Constant((a + b) % ORDER)),
            (Power::Constant(0), _) => Some(b),
            (_, Power::Constant(0)) => Some(a),
            _ => Some(Power::Expr(
                self.define(
                    "(_ BitVec 62)",
                    format!("(bvadd {} {})", a.text(), b.text()),
                )?,
                a.step().min(b.step()),
            )),
        }
    }
    fn phase(&mut self, p: &KernelPhasePolynomial) -> Option<Power> {
        let mut result = PhaseForm::default();
        for (selector, c) in p.selectors() {
            self.charge(1)?;
            let e = exponent(&c)?; // Check even inactive selectors.
            result.add(selector, e);
        }
        self.lower_phase_form(result)
    }
    fn literal(&mut self, r: BigRational, p: u64, radical: bool) -> Option<Polynomial> {
        self.charge(1)?;
        if r.numer().bits() > 4096 || r.denom().bits() > 4096 {
            return None;
        }
        Some(vec![Atom {
            guard: "true".into(),
            power: Power::Constant(p),
            weight: r,
            radical,
        }])
    }
    fn compact(&mut self, items: Polynomial) -> Option<Polynomial> {
        self.charge(items.len())?;
        let mut map = BTreeMap::new();
        for mut a in items {
            if a.guard == "false" {
                continue;
            }
            if let Power::Constant(p) = &mut a.power
                && *p >= HALF
            {
                *p -= HALF;
                a.weight = -a.weight;
            }
            let value = map
                .entry((a.guard, a.power, a.radical))
                .or_insert_with(|| integer(0));
            *value += a.weight;
            if value.numer().bits() > MAX_BITS || value.denom().bits() > MAX_BITS {
                return None;
            }
        }
        if map.len() > MAX_ATOMS {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density exact SMT atoms refused: compact={} limit={MAX_ATOMS}",
                    map.len()
                );
            }
            return None;
        }
        Some(
            map.into_iter()
                .filter(|(_, r)| *r != integer(0))
                .map(|((guard, power, radical), weight)| Atom {
                    guard,
                    power,
                    radical,
                    weight,
                })
                .collect(),
        )
    }
    fn multiply(&mut self, a: Polynomial, b: Polynomial) -> Option<Polynomial> {
        // Multiplication by a signed unit root permutes the closed power
        // basis. For an already canonical operand it cannot merge entries,
        // so no rational product or coefficient-map reconstruction is needed.
        // Noncanonical/symbolic/radical roots use the ordinary complete path.
        if let [root] = a.as_slice()
            && root.guard == "true"
            && !root.radical
            && (root.weight == integer(1) || root.weight == integer(-1))
            && let Power::Constant(shift) = root.power
            && shift < ORDER
            && b.iter().all(|x| {
                x.guard == "true"
                    && x.weight != integer(0)
                    && x.weight.numer().bits() <= MAX_BITS
                    && x.weight.denom().bits() <= MAX_BITS
                    && matches!(x.power, Power::Constant(p) if p < HALF)
            })
            && b.windows(2)
                .all(|w| (&w[0].power, w[0].radical) < (&w[1].power, w[1].radical))
            && b.len() <= MAX_ATOMS
        {
            self.charge(b.len())?;
            let mut out = b;
            for atom in &mut out {
                let Power::Constant(p) = &mut atom.power else {
                    unreachable!();
                };
                *p = (*p + shift) % ORDER;
                let negative = root.weight < integer(0);
                if (*p >= HALF) ^ negative {
                    atom.weight = -atom.weight.clone();
                }
                *p %= HALF;
            }
            out.sort_by(|a, b| (&a.power, a.radical).cmp(&(&b.power, b.radical)));
            return Some(out);
        }
        self.charge(a.len().checked_mul(b.len())?)?;
        if a.len().checked_mul(b.len())? > MAX_ATOMS {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density exact SMT atoms refused: product={}*{} limit={MAX_ATOMS}",
                    a.len(),
                    b.len()
                );
            }
            return None;
        }
        let mut out = Vec::new();
        for a in &a {
            for b in &b {
                out.push(Atom {
                    guard: self.and(a.guard.clone(), b.guard.clone())?,
                    power: self.plus_power(a.power.clone(), b.power.clone())?,
                    radical: a.radical ^ b.radical,
                    weight: &a.weight
                        * &b.weight
                        * integer(if a.radical && b.radical { 3 } else { 1 }),
                });
            }
        }
        self.compact(out)
    }
    fn scalar(&mut self, s: &KernelScalar, depth: usize) -> Option<Polynomial> {
        self.charge(1)?;
        if depth >= 64 {
            return None;
        }
        match s {
            KernelScalar::Rational(r) => self.literal(r.clone(), 0, false),
            KernelScalar::Neg(a) => {
                let mut a = self.scalar(a, depth + 1)?;
                for x in &mut a {
                    x.weight = -x.weight.clone();
                }
                Some(a)
            }
            KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
                let mut left = self.scalar(a, depth + 1)?;
                let right = self.scalar(b, depth + 1)?;
                if matches!(s, KernelScalar::Mul(..)) {
                    self.multiply(left, right)
                } else {
                    left.extend(right);
                    self.compact(left)
                }
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                let g = self.boolean(condition)?;
                let ng = self.not(g.clone())?;
                // Both branches must be defined and encodable, including dead branches.
                let mut a = self.scalar(when_true, depth + 1)?;
                let mut b = self.scalar(when_false, depth + 1)?;
                for x in &mut a {
                    x.guard = self.and(g.clone(), x.guard.clone())?;
                }
                for x in &mut b {
                    x.guard = self.and(ng.clone(), x.guard.clone())?;
                }
                a.extend(b);
                self.compact(a)
            }
            KernelScalar::Inverse(a) => {
                let KernelScalar::Rational(r) = a.as_ref() else {
                    return None;
                };
                if *r == integer(0) {
                    return None;
                }
                self.literal(r.recip(), 0, false)
            }
            KernelScalar::Sqrt(a) => {
                let KernelScalar::Rational(r) = a.as_ref() else {
                    return None;
                };
                if let Some(v) = rational_root(r) {
                    return self.literal(v, 0, false);
                }
                if let Some(v) = rational_root(&(r / integer(3))) {
                    return self.literal(v, 0, true);
                }
                let v = rational_root(&(r * integer(2)))? / integer(2);
                let mut out = self.literal(v.clone(), ORDER / 8, false)?;
                out.extend(self.literal(-v, 3 * ORDER / 8, false)?);
                Some(out)
            }
            KernelScalar::Sin(a) | KernelScalar::Cos(a) => {
                if !exact_trig::admitted(a, &mut 64) {
                    return None;
                }
                if let Some(normal) = exact_trig::normalize(a, matches!(s, KernelScalar::Sin(_))) {
                    return self.scalar(&normal, depth + 1);
                }
                let p = exponent(&PhaseCoefficient::angle(a.clone(), integer(1)))?;
                let sine = matches!(s, KernelScalar::Sin(_));
                let shift = if sine { 3 * ORDER / 4 } else { 0 };
                let mut out = self.literal(ratio(1, 2), (p + shift) % ORDER, false)?;
                out.extend(self.literal(
                    ratio(if sine { -1 } else { 1 }, 2),
                    (ORDER - p + shift) % ORDER,
                    false,
                )?);
                self.compact(out)
            }
        }
    }
    fn term(&mut self, t: &WorkingTerm) -> Option<Polynomial> {
        let mut guard = "true".to_owned();
        for row in &t.constraints {
            let b = self.boolean(row)?;
            let b = self.not(b)?;
            guard = self.and(guard, b)?;
        }
        let phase = self.phase(&t.phase)?;
        let mut scalar = self.scalar(&t.coefficient, 0)?;
        for a in &mut scalar {
            a.guard = self.and(guard.clone(), a.guard.clone())?;
            a.power = self.plus_power(a.power.clone(), phase.clone())?;
        }
        self.compact(scalar)
    }
    fn aggregate(&mut self, source: &ExactAggregate) -> Option<Polynomial> {
        let mut result = Vec::new();
        for (entry, coefficients) in source {
            for (phase, coefficient) in coefficients {
                result.extend(self.term(&WorkingTerm {
                    constraints: entry.constraints.clone(),
                    paths: BTreeSet::new(),
                    coefficient: coefficient.clone(),
                    phase: phase.clone(),
                })?);
                result = self.compact(result)?;
            }
        }
        Some(result)
    }
    // Binders are summed, NEVER declared as existential coordinates. Refuse
    // the whole formula if a complete sum does not fit the encoding budget.
    fn bound_sum(&mut self, t: WorkingTerm) -> Option<Polynomial> {
        debug_term("SMT-bound-sum", &t);
        self.charge(1)?;
        if let Some(factors) = factor_phase_sums(&t) {
            let mut product = self.literal(integer(1), 0, false)?;
            for factor in factors {
                let next = self.bound_sum(factor)?;
                product = self.multiply(product, next)?;
            }
            return Some(product);
        }
        if (4..=96).contains(&t.paths.len()) && self.schedule_attempts < 8 && self.work >= 5000 {
            self.schedule_attempts += 1;
            let mut trial = self.clone();
            let budget = self.probe_work_budget(crate::equivalence::tuning::limits().schedule_work);
            trial.work = budget;
            let value = trial.scheduled_sum(&t);
            let spent = budget - trial.work;
            self.charge(spent)?;
            if let Some(value) = value {
                trial.work = self.work;
                *self = trial;
                return Some(value);
            }
        }
        if !graph::is_algebraic(&t) {
            if t.paths.is_empty() {
                return self.term(&t);
            }
            // Actual summation work remains bounded; graph construction itself
            // has no ANF expansion budget. Never existentialize these binders.
            self.charge(
                t.constraints
                    .iter()
                    .map(KernelBooleanPolynomial::term_count)
                    .sum::<usize>()
                    + t.phase.term_count()
                    + 1,
            )?;
            let mut result = Vec::new();
            for child in conditioning::split(&t)? {
                let p = match child {
                    Reduction::Zero => vec![],
                    Reduction::Residual => return None,
                    Reduction::Sum(t) => self.bound_sum(*t)?,
                    Reduction::Exact(t) => self.term(&WorkingTerm {
                        constraints: t.constraints,
                        paths: BTreeSet::new(),
                        coefficient: t.coefficient,
                        phase: t.phase,
                    })?,
                };
                result.extend(p);
                result = self.compact(result)?;
            }
            return Some(result);
        }
        if t.paths.is_empty() {
            return self.term(&t);
        }
        if t.paths.len() > 64 {
            return None;
        }
        // Compile BOTH cofactors, reducing each complete summand before the
        // next expansion. This eliminates bound sums, not free-coordinate
        // counterexample search. No successful prefix can yield a verdict.
        let cells = t
            .phase
            .terms()
            .map(|(m, _)| 1 + m.variables().count())
            .sum::<usize>()
            + t.constraints
                .iter()
                .flat_map(KernelBooleanPolynomial::terms)
                .map(|m| 1 + m.variables().count())
                .sum::<usize>()
            + t.paths.len();
        self.charge(cells.checked_mul(2)?)?;
        let mut result = Vec::new();
        for child in conditioning::split(&t)? {
            let p = match child {
                Reduction::Zero => vec![],
                Reduction::Residual => return None,
                Reduction::Exact(t) => self.term(&WorkingTerm {
                    constraints: t.constraints,
                    paths: BTreeSet::new(),
                    coefficient: t.coefficient,
                    phase: t.phase,
                })?,
                Reduction::Sum(t) => self.bound_sum(*t)?,
            };
            result.extend(p);
            result = self.compact(result)?;
        }
        Some(result)
    }
    fn kernel_factors(&mut self, k: &DensityKernel) -> Option<Vec<Polynomial>> {
        let mut result = Vec::new();
        for (i, t) in k.terms.iter().enumerate() {
            if t.quantum_outputs_ket.len() != k.quantum_output_count
                || t.quantum_outputs_bra.len() != k.quantum_output_count
                || t.classical_outputs.len() != k.classical_output_count
                || t.ket_paths
                    .iter()
                    .any(|v| !matches!(v,KernelVariable::PathKet{term,..} if *term==i))
                || t.bra_paths
                    .iter()
                    .any(|v| !matches!(v,KernelVariable::PathBra{term,..} if *term==i))
            {
                return None;
            }
            // Admit the raw weight and each phase BEFORE cancellation or reduction.
            for v in t.ket_paths.iter().chain(&t.bra_paths) {
                self.bound.insert(v.clone(), false);
            }
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density exact SMT admission: paths={} ket_phase={} bra_phase={}",
                    self.bound.len(),
                    t.phase.ket.term_count(),
                    t.phase.bra.term_count()
                );
            }
            self.scalar(&t.weight.ket, 0)?;
            self.scalar(&t.weight.bra, 0)?;
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("density exact SMT admission: scalars accepted");
            }
            self.phase(&t.phase.ket)?;
            self.phase(&t.phase.bra)?;
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("density exact SMT admission: phases accepted");
            }
            let whole = working_term(t);
            for row in &whole.constraints {
                self.boolean(row)?;
            }
            self.bound.clear();
            let p = match reduce_working_term(whole) {
                Reduction::Zero => Vec::new(),
                Reduction::Residual => return None,
                Reduction::Exact(t) => self.term(&WorkingTerm {
                    constraints: t.constraints,
                    paths: BTreeSet::new(),
                    coefficient: t.coefficient,
                    phase: t.phase,
                })?,
                Reduction::Sum(t) => {
                    if k.terms.len() == 1
                        && let Some(factors) = factor_phase_sums(&t)
                    {
                        return factors.into_iter().map(|f| self.bound_sum(f)).collect();
                    }
                    self.bound_sum(*t)?
                }
            };
            result.extend(p);
            result = self.compact(result)?;
        }
        Some(vec![result])
    }
}

fn bv(n: &BigInt, width: u64) -> String {
    let n = if n < &BigInt::from(0) {
        (BigInt::from(1) << width) + n
    } else {
        n.clone()
    };
    format!("(_ bv{n} {width})")
}
fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    while b != BigInt::from(0) {
        let r = a % b.clone();
        a = b;
        b = r;
    }
    a
}

struct Query {
    script: String,
    atoms: Polynomial,
    denominator: BigInt,
    width: u64,
    names: Vec<String>,
    coordinates: Vec<KernelVariable>,
    group_sizes: Vec<usize>,
    rational: Option<Vec<SignedRational>>,
}

/// Signed numerator DAG with a positive STATIC denominator and an absolute
/// bound valid at EVERY Boolean input. Zero extension is never used here.
#[derive(Clone)]
struct SignedRational {
    expression: String,
    denominator: BigInt,
    bound: BigInt,
    width: u64,
}
impl SignedRational {
    fn extend(&self, width: u64) -> Option<String> {
        let extra = width.checked_sub(self.width)?;
        Some(if extra == 0 {
            self.expression.clone()
        } else {
            format!("((_ sign_extend {extra}) {})", self.expression)
        })
    }
}

impl Encoder {
    fn rational_literal(&mut self, n: BigInt, d: BigInt) -> Option<SignedRational> {
        let bound = BigInt::from(n.magnitude().clone());
        let width = (bound.bits() + 1).max(2);
        if width > MAX_BITS || d <= 0.into() || d.bits() > MAX_BITS {
            return None;
        }
        Some(SignedRational {
            expression: bv(&n, width),
            denominator: d,
            bound,
            width,
        })
    }
    fn rational_polynomial(&mut self, p: Polynomial) -> Option<SignedRational> {
        let p = self.compact(p)?;
        if p.iter().any(|a| a.radical || a.power.step() < HALF) {
            return None;
        }
        let mut d = BigInt::from(1);
        for a in &p {
            d = (&d / gcd(d.clone(), a.weight.denom().clone())) * a.weight.denom();
            if d.bits() > MAX_BITS {
                return None;
            }
        }
        let ns = p
            .iter()
            .map(|a| a.weight.numer() * (&d / a.weight.denom()))
            .collect::<Vec<_>>();
        let bound = ns.iter().fold(BigInt::from(0), |s, n| {
            s + BigInt::from(n.magnitude().clone())
        });
        let width = (bound.bits() + 1).max(2);
        if width > MAX_BITS {
            return None;
        }
        let mut values = Vec::new();
        for (a, n) in p.iter().zip(&ns) {
            values.push(self.define(
                &format!("(_ BitVec {width})"),
                format!(
                    "(ite {} (ite (= ((_ extract 61 61) {}) #b0) {} {}) {})",
                    a.guard,
                    a.power.text(),
                    bv(n, width),
                    bv(&(-n), width),
                    bv(&0.into(), width)
                ),
            )?);
        }
        while values.len() > 1 {
            let mut next = Vec::new();
            for pair in values.chunks(2) {
                next.push(if pair.len() == 1 {
                    pair[0].clone()
                } else {
                    self.define(
                        &format!("(_ BitVec {width})"),
                        format!("(bvadd {} {})", pair[0], pair[1]),
                    )?
                });
            }
            values = next;
        }
        Some(SignedRational {
            expression: values.pop().unwrap_or_else(|| bv(&0.into(), width)),
            denominator: d,
            bound,
            width,
        })
    }
    fn rational_multiply(
        &mut self,
        a: SignedRational,
        b: SignedRational,
    ) -> Option<SignedRational> {
        self.charge(1)?;
        let bound = &a.bound * &b.bound;
        let denominator = &a.denominator * &b.denominator;
        if bound == 0.into() {
            return self.rational_literal(0.into(), 1.into());
        }
        let width = (bound.bits() + 1).max(2);
        if width > MAX_BITS || denominator.bits() > MAX_BITS {
            return None;
        }
        let expression = self.define(
            &format!("(_ BitVec {width})"),
            format!("(bvmul {} {})", a.extend(width)?, b.extend(width)?),
        )?;
        Some(SignedRational {
            expression,
            denominator,
            bound,
            width,
        })
    }
    fn rational_difference(
        &mut self,
        a: SignedRational,
        b: SignedRational,
    ) -> Option<SignedRational> {
        let common = gcd(a.denominator.clone(), b.denominator.clone());
        let sa = &b.denominator / &common;
        let sb = &a.denominator / &common;
        let bound = &a.bound * &sa + &b.bound * &sb;
        let denominator = &a.denominator * &sa;
        let width = (bound.bits() + 1).max(2).max(a.width).max(b.width);
        if width > MAX_BITS || denominator.bits() > MAX_BITS {
            return None;
        }
        // A scaling factor can exceed the final width only for a zero bound.
        // Avoid encoding a truncated factor in that case; the term is exactly 0.
        let scale = |x: &SignedRational, n: &BigInt| -> Option<String> {
            if x.bound == 0.into() {
                Some(bv(&0.into(), width))
            } else {
                Some(format!("(bvmul {} {})", x.extend(width)?, bv(n, width)))
            }
        };
        let expression = self.define(
            &format!("(_ BitVec {width})"),
            format!("(bvsub {} {})", scale(&a, &sa)?, scale(&b, &sb)?),
        )?;
        Some(SignedRational {
            expression,
            denominator,
            bound,
            width,
        })
    }
    fn rational_product_query(self, a: Vec<Polynomial>, b: Vec<Polynomial>) -> Option<Query> {
        self.dense_product_query(a, b, 1)
    }
    fn dense_polynomial(&mut self, p: Polynomial, degree: usize) -> Option<Vec<SignedRational>> {
        let stride = HALF / degree as u64;
        if p.iter().any(|a| a.radical || a.power.step() < stride) {
            return None;
        }
        let mut coefficients = Vec::new();
        for j in 0..degree {
            let mut selected = Vec::new();
            for a in &p {
                let mut a = a.clone();
                match &a.power {
                    Power::Constant(n) => {
                        if n % HALF != j as u64 * stride {
                            continue;
                        }
                        a.power = Power::Constant(if *n >= HALF { HALF } else { 0 });
                    }
                    _ => {
                        let equal = self.define(
                            "Bool",
                            format!(
                                "(= (bvand {} (_ bv{} 62)) (_ bv{} 62))",
                                a.power.text(),
                                HALF - 1,
                                j as u64 * stride
                            ),
                        )?;
                        a.guard = self.and(a.guard, equal)?;
                        a.power = Power::Expr(
                            self.define(
                                "(_ BitVec 62)",
                                format!("(bvand {} (_ bv{HALF} 62))", a.power.text()),
                            )?,
                            HALF,
                        );
                    }
                }
                selected.push(a);
            }
            coefficients.push(self.rational_polynomial(selected)?);
        }
        Some(coefficients)
    }
    fn dense_product(
        &mut self,
        factors: Vec<Polynomial>,
        degree: usize,
    ) -> Option<Vec<SignedRational>> {
        let zero = self.rational_literal(0.into(), 1.into())?;
        let mut product = vec![zero.clone(); degree];
        product[0] = self.rational_literal(1.into(), 1.into())?;
        for factor in factors {
            let coefficients = self.dense_polynomial(factor, degree)?;
            let mut next = vec![zero.clone(); degree];
            for (i, a) in product.iter().enumerate() {
                for (j, b) in coefficients.iter().enumerate() {
                    let mut term = self.rational_multiply(a.clone(), b.clone())?;
                    // The basis is powers of a primitive (2*degree)-th root:
                    // X^degree=-1. Nonwrapped products ADD, wrapped ones SUBTRACT.
                    if i + j < degree {
                        term.expression = self.define(
                            &format!("(_ BitVec {})", term.width),
                            format!("(bvneg {})", term.expression),
                        )?;
                    }
                    next[(i + j) % degree] =
                        self.rational_difference(next[(i + j) % degree].clone(), term)?;
                }
            }
            product = next;
        }
        Some(product)
    }
    fn dense_product_query(
        mut self,
        a: Vec<Polynomial>,
        b: Vec<Polynomial>,
        degree: usize,
    ) -> Option<Query> {
        if degree == 0 || degree > 8 || !degree.is_power_of_two() {
            return None;
        }
        let left = self.dense_product(a, degree)?;
        let right = self.dense_product(b, degree)?;
        let mut result = Vec::new();
        let mut nonzero = Vec::new();
        let mut names = (0..self.coordinates.len())
            .map(|i| format!("u{i}"))
            .collect::<Vec<_>>();
        let mut denominator = BigInt::from(1);
        let mut width = 2;
        for (i, (a, b)) in left.into_iter().zip(right).enumerate() {
            let r = self.rational_difference(a, b)?;
            width = width.max(r.width);
            denominator =
                (&denominator / gcd(denominator.clone(), r.denominator.clone())) * &r.denominator;
            if denominator.bits() > MAX_BITS {
                return None;
            }
            self.definitions.push_str(&format!(
                "(define-fun numerator{i} () (_ BitVec {}) {})\n",
                r.width, r.expression
            ));
            nonzero.push(format!(
                "(distinct numerator{i} {})",
                bv(&0.into(), r.width)
            ));
            names.push(format!("numerator{i}"));
            result.push(r);
        }
        let nonzero = if nonzero.len() == 1 {
            nonzero.remove(0)
        } else {
            format!("(or {})", nonzero.join(" "))
        };
        let script = format!(
            "(set-logic QF_BV)\n(set-option :produce-models true)\n{}(assert {nonzero})\n(check-sat)\n",
            self.definitions
        );
        Some(Query {
            script,
            atoms: vec![],
            denominator,
            width,
            names,
            coordinates: self.coordinates,
            group_sizes: vec![],
            rational: Some(result),
        })
    }
}
impl Encoder {
    fn query(self, atoms: Polynomial) -> Option<Query> {
        self.product_query(vec![atoms])
    }
    fn product_query(mut self, groups: Vec<Polynomial>) -> Option<Query> {
        let groups = groups
            .into_iter()
            .map(|p| self.compact(p))
            .collect::<Option<Vec<_>>>()?;
        let group_sizes = groups.iter().map(Vec::len).collect::<Vec<_>>();
        let atoms = groups.into_iter().flatten().collect::<Vec<_>>();
        let mut denominator = BigInt::from(1);
        for a in &atoms {
            let d = a.weight.denom();
            denominator = (&denominator / gcd(denominator.clone(), d.clone())) * d;
            if denominator.bits() > MAX_BITS {
                return None;
            }
        }
        let weights = atoms
            .iter()
            .map(|a| a.weight.numer() * (&denominator / a.weight.denom()))
            .collect::<Vec<_>>();
        let bound = weights.iter().fold(BigInt::from(0), |s, n| {
            s + BigInt::from(n.magnitude().clone())
        });
        let width = (bound.bits() + 1).max(2);
        if width > MAX_BITS {
            return None;
        }
        let mut names = (0..self.coordinates.len())
            .map(|i| format!("u{i}"))
            .collect::<Vec<_>>();
        let mut assertions = String::new();
        let mut offset = 0;
        for (group, len) in group_sizes.iter().enumerate() {
            self.definitions.push_str(&format!("(declare-fun basis{group} () (_ BitVec 61))\n(declare-fun radical{group} () Bool)\n"));
            let mut summands = Vec::new();
            for i in offset..offset + len {
                let a = &atoms[i];
                let n = &weights[i];
                self.definitions.push_str(&format!(
                    "(define-fun p{i} () (_ BitVec 62) {})\n(define-fun g{i} () Bool {})\n",
                    a.power.text(),
                    a.guard
                ));
                names.push(format!("p{i}"));
                names.push(format!("g{i}"));
                let term = format!(
                    "(ite (and g{i} (= radical{group} {}) (= ((_ extract 60 0) p{i}) basis{group})) (ite (= ((_ extract 61 61) p{i}) #b0) {} {}) {})",
                    a.radical,
                    bv(n, width),
                    bv(&(-n), width),
                    bv(&0.into(), width)
                );
                summands.push(self.define(&format!("(_ BitVec {width})"), term)?);
            }
            offset += len;
            while summands.len() > 1 {
                let mut next = Vec::new();
                for pair in summands.chunks(2) {
                    next.push(if pair.len() == 1 {
                        pair[0].clone()
                    } else {
                        self.define(
                            &format!("(_ BitVec {width})"),
                            format!("(bvadd {} {})", pair[0], pair[1]),
                        )?
                    });
                }
                summands = next;
            }
            let sum = summands.pop().unwrap_or_else(|| bv(&0.into(), width));
            assertions.push_str(&format!(
                "(assert (distinct {sum} {}))\n",
                bv(&0.into(), width)
            ));
        }
        let script = format!(
            "(set-logic QF_BV)\n(set-option :produce-models true)\n{}{assertions}(check-sat)\n",
            self.definitions
        );
        Some(Query {
            script,
            atoms,
            denominator,
            width,
            names,
            coordinates: self.coordinates,
            group_sizes,
            rational: None,
        })
    }
}

fn model_values(stdout: &str, names: &[String]) -> Option<BTreeMap<String, String>> {
    let text = stdout.replace(['(', ')'], " ");
    let t = text.split_whitespace().collect::<Vec<_>>();
    let mut out = BTreeMap::new();
    for name in names {
        let positions = t
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == name)
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        if positions.len() != 1 {
            return None;
        }
        let v = *t.get(positions[0] + 1)?;
        if v == "_" {
            return None;
        } // Bitwuzla emits #b/#x, never accept an ambiguous truncated tuple.
        out.insert(name.clone(), v.to_owned());
    }
    Some(out)
}
fn bits(s: &str) -> Option<u64> {
    if let Some(n) = s.strip_prefix("#b") {
        u64::from_str_radix(n, 2).ok()
    } else if let Some(n) = s.strip_prefix("#x") {
        u64::from_str_radix(n, 16).ok()
    } else {
        None
    }
}
fn boolean_value(s: &str) -> Option<bool> {
    match s {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

impl Query {
    fn solve(&self, k: &DensityKernel) -> AggregateComparison {
        let result = run_solver(Solver::Bitwuzla, &self.script);
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "density exact SMT: atoms={} coefficient_bits={} denominator_bits={} status={:?}",
                self.atoms.len(),
                self.width,
                self.denominator.bits(),
                result.status
            );
        }
        match result.status {
            SolverStatus::Unsat => {
                AggregateComparison::SmtEquivalent(crate::equivalence::smt::PortfolioResult {
                    consensus: crate::equivalence::smt::PortfolioConsensus::Unsat,
                    results: vec![result],
                })
            }
            SolverStatus::Sat => {
                let query = format!("{}(get-value ({}))\n", self.script, self.names.join(" "));
                let model = run_solver(Solver::Bitwuzla, &query);
                if model.status != SolverStatus::Sat {
                    return AggregateComparison::Unknown;
                }
                match self.witness(&model.stdout, k) {
                    Some(witness) => AggregateComparison::Different(
                        Box::new(witness),
                        crate::equivalence::smt::PortfolioResult {
                            consensus: crate::equivalence::smt::PortfolioConsensus::Sat,
                            results: vec![model],
                        },
                    ),
                    None => AggregateComparison::Unknown,
                }
            }
            _ => AggregateComparison::Unknown,
        }
    }
    fn witness(&self, stdout: &str, k: &DensityKernel) -> Option<DensityCounterexample> {
        let values = model_values(stdout, &self.names)?;
        let mut factors = Vec::new();
        let mut offset = 0;
        for len in &self.group_sizes {
            let mut rational = BTreeMap::new();
            let mut radical = BTreeMap::new();
            for i in offset..offset + len {
                let a = &self.atoms[i];
                let active = boolean_value(values.get(&format!("g{i}"))?)?;
                let p = bits(values.get(&format!("p{i}"))?)?;
                if p >= ORDER {
                    return None;
                }
                if active {
                    let map = if a.radical {
                        &mut radical
                    } else {
                        &mut rational
                    };
                    *map.entry(p % HALF).or_insert_with(|| integer(0)) += if p >= HALF {
                        -a.weight.clone()
                    } else {
                        a.weight.clone()
                    };
                }
            }
            offset += len;
            rational.retain(|_, r| *r != integer(0));
            radical.retain(|_, r| *r != integer(0));
            if rational.is_empty() && radical.is_empty() {
                return None;
            }
            factors.push(crate::equivalence::DensityExactFactor {
                coefficients: rational.into_iter().collect(),
                sqrt_three_coefficients: radical.into_iter().collect(),
            });
        }
        let first = if let Some(rs) = &self.rational {
            let mut coefficients = Vec::new();
            for (i, r) in rs.iter().enumerate() {
                let text = values.get(&format!("numerator{i}"))?;
                let (digits, base) = if let Some(n) = text.strip_prefix("#b") {
                    (n, 2)
                } else {
                    (text.strip_prefix("#x")?, 16)
                };
                let unsigned = BigInt::parse_bytes(digits.as_bytes(), base)?;
                if unsigned.bits() > r.width {
                    return None;
                }
                let sign = BigInt::from(1) << (r.width - 1);
                let signed = if unsigned >= sign {
                    unsigned - (BigInt::from(1) << r.width)
                } else {
                    unsigned
                };
                if BigInt::from(signed.magnitude().clone()) > r.bound {
                    return None;
                }
                if signed != 0.into() {
                    coefficients.push((
                        i as u64 * (HALF / rs.len() as u64),
                        BigRational::new(signed, r.denominator.clone()),
                    ));
                }
            }
            if coefficients.is_empty() {
                return None;
            }
            crate::equivalence::DensityExactFactor {
                coefficients,
                sqrt_three_coefficients: vec![],
            }
        } else {
            factors.remove(0)
        };

        let mut result = DensityCounterexample {
            ket_inputs: vec![false; k.input_pairs.len()],
            bra_inputs: vec![false; k.input_pairs.len()],
            ket_outputs: vec![false; k.quantum_output_count],
            bra_outputs: vec![false; k.quantum_output_count],
            classical_outputs: vec![false; k.classical_output_count],
            root_of_unity_order: ORDER,
            difference_coefficients: first.coefficients,
            sqrt_three_coefficients: first.sqrt_three_coefficients,
            exact_factors: factors,
        };
        for (i, v) in self.coordinates.iter().enumerate() {
            let target = match v {
                KernelVariable::InputKet(i) => result.ket_inputs.get_mut(*i),
                KernelVariable::InputBra(i) => result.bra_inputs.get_mut(*i),
                KernelVariable::QuantumOutputKet(i) => result.ket_outputs.get_mut(*i),
                KernelVariable::QuantumOutputBra(i) => result.bra_outputs.get_mut(*i),
                KernelVariable::ClassicalOutput(i) => result.classical_outputs.get_mut(*i),
                _ => None,
            }?;
            *target = boolean_value(values.get(&format!("u{i}"))?)?;
        }
        Some(result)
    }
}

pub(super) fn compare(source: &ExactAggregate, k: &DensityKernel) -> AggregateComparison {
    let Some(mut e) = Encoder::new(k) else {
        return AggregateComparison::Unknown;
    };
    let q = e.aggregate(source).and_then(|p| e.query(p));
    q.map_or(AggregateComparison::Unknown, |q| q.solve(k))
}
pub(super) fn compare_raw(left: &DensityKernel, right: &DensityKernel) -> AggregateComparison {
    let result = compare_raw_atoms(left, right);
    if matches!(result, AggregateComparison::Unknown) {
        return coefficient_dag::compare(left, right).unwrap_or(result);
    }
    result
}

fn compare_raw_atoms(left: &DensityKernel, right: &DensityKernel) -> AggregateComparison {
    if left.input_pairs != right.input_pairs
        || left.quantum_output_count != right.quantum_output_count
        || left.classical_output_count != right.classical_output_count
    {
        return AggregateComparison::Unknown;
    }
    let Some(mut e) = Encoder::new(left) else {
        return AggregateComparison::Unknown;
    };
    let mut stage = "left complete sum";
    let query = (|| {
        let mut a = e.kernel_factors(left)?;
        stage = "right complete sum";
        let mut b = e.kernel_factors(right)?;
        let stride = a
            .iter()
            .chain(&b)
            .flatten()
            .fold(HALF, |s, x| s.min(x.power.step()));
        let degree = (HALF / stride) as usize;
        if let Some(proof) = e.prove_factor_products(&a, &b, degree) {
            return Some(Err(proof));
        }
        if let Some(proof) = e.prove_regions(&a, &b) {
            return Some(Err(proof));
        }
        if degree <= 8 && a.iter().chain(&b).flatten().all(|x| !x.radical) {
            stage = "exact coefficient-vector product";
            return if degree == 1 {
                e.rational_product_query(a, b)
            } else {
                e.dense_product_query(a, b, degree)
            }
            .map(Ok);
        }
        stage = "complete product expansion";
        // Cancel no factor: retain every matched factor as an explicit nonzero
        // conjunct. Over the field, C*(A-B)!=0 iff C!=0 AND A-B!=0.
        let mut common = Vec::new();
        let mut i = 0;
        while i < a.len() {
            if let Some(j) = b.iter().position(|p| *p == a[i]) {
                common.push(a.remove(i));
                b.remove(j);
            } else {
                i += 1;
            }
        }
        let mut left = e.literal(integer(1), 0, false)?;
        for p in a {
            left = e.multiply(left, p)?;
        }
        let mut right = e.literal(integer(1), 0, false)?;
        for p in b {
            right = e.multiply(right, p)?;
        }
        for x in &mut right {
            x.weight = -x.weight.clone();
        }
        left.extend(right);
        let mut groups = vec![left];
        groups.extend(common);
        stage = "coefficient encoding";
        e.product_query(groups).map(Ok)
    })();
    if query.is_none() && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("density exact SMT encoding refused: {stage}");
    }
    query.map_or(AggregateComparison::Unknown, |q| match q {
        Ok(q) => q.solve(left),
        Err(proof) => AggregateComparison::SmtEquivalent(proof),
    })
}

impl Encoder {
    /// Prove a product by its COMPLETE independent factors, without expanding
    /// the product or interpreting a failed factor match as channel NEQ.
    fn prove_factor_products(
        &self,
        a: &[Polynomial],
        b: &[Polynomial],
        degree: usize,
    ) -> Option<crate::equivalence::smt::PortfolioResult> {
        if a.is_empty() || a.len() != b.len() || a.len() > 8 {
            return None;
        }
        // Only this sufficient-certificate copy is rephased. The complete
        // fallback query/model continues to describe the ORIGINAL difference.
        let mut encoder = self.clone();
        let mut left = a.to_vec();
        let mut right = b.to_vec();
        encoder.normalize_factor_contents(&mut left, &mut right)?;
        encoder.relative_product_phases(&mut left, &mut right)?;
        encoder.prove_normalized_factors(&left, &right, degree)
    }

    fn prove_normalized_factors(
        &self,
        a: &[Polynomial],
        b: &[Polynomial],
        degree: usize,
    ) -> Option<crate::equivalence::smt::PortfolioResult> {
        let mut results = Vec::new();
        let single_factor = a.len() == 1;
        let mut phase_offset = 0u64;
        let started = std::time::Instant::now();
        // A common one-atom factor is nonzero only on its guard. Outside
        // that guard BOTH complete products are zero, so factor comparisons
        // need only hold on this shared domain. Never assume an unmatched guard.
        let domain: Vec<_> = a
            .iter()
            .zip(b)
            .filter(|(a, b)| a == b && a.len() == 1)
            .map(|(a, _)| format!("(assert {})\n", a[0].guard))
            .collect();
        for (a, b) in a.iter().zip(b) {
            if started.elapsed() >= crate::equivalence::smt::solver_timeout() {
                return None;
            }
            if a == b {
                continue;
            }
            if let Some(proof) = self.prove_guard_groups(a, b, &domain) {
                results.extend(proof.results);
                continue;
            }
            if !single_factor {
                let mut matched = false;
                // Constant unit-phase ratios of independent factors may cancel
                // in the product (not just two minus signs). Check each ratio;
                // only a zero TOTAL offset certifies the complete product.
                let count = if degree <= 8 { degree * 2 } else { 2 };
                for i in 1..count {
                    if started.elapsed() >= crate::equivalence::smt::solver_timeout() {
                        return None;
                    }
                    let offset = ORDER / count as u64 * i as u64;
                    let mut trial = self.clone();
                    let shifted = b
                        .iter()
                        .cloned()
                        .map(|mut atom| {
                            atom.power = trial.plus_power(atom.power, Power::Constant(offset))?;
                            Some(atom)
                        })
                        .collect::<Option<Vec<_>>>()?;
                    if let Some(proof) = trial.prove_guard_groups(a, &shifted, &domain) {
                        phase_offset = (phase_offset + offset) % ORDER;
                        results.extend(proof.results);
                        matched = true;
                        break;
                    }
                }
                if matched {
                    continue;
                }
            }
            // For a single sum the caller's complete fallback is already the
            // whole-factor query. Do not run it twice after a failed grouping.
            if single_factor {
                return None;
            }
            let rational_field = a.iter().chain(b).all(|x| !x.radical);
            let mut q = if degree == 1 && rational_field {
                self.clone()
                    .rational_product_query(vec![a.clone()], vec![b.clone()])
            } else if degree <= 8 && rational_field {
                self.clone()
                    .dense_product_query(vec![a.clone()], vec![b.clone()], degree)
            } else {
                let mut difference = a.clone();
                difference.extend(b.iter().cloned().map(|mut atom| {
                    atom.weight = -atom.weight;
                    atom
                }));
                self.clone().query(difference)
            }?;
            q.script = q
                .script
                .replace("(check-sat)", &format!("{}(check-sat)", domain.join("")));
            let result = run_solver(Solver::Bitwuzla, &q.script);
            if result.status != SolverStatus::Unsat {
                return None;
            }
            results.push(result);
        }
        if phase_offset != 0 {
            return None;
        }
        Some(crate::equivalence::smt::PortfolioResult {
            consensus: crate::equivalence::smt::PortfolioConsensus::Unsat,
            results,
        })
    }
}

#[cfg(test)]
mod tests;
