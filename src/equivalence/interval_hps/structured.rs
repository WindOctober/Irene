//! Structural scalar/phase arithmetic over shared Boolean predicates.
//! No truth tables, floating-point predicate equality, or sampled inputs.
use super::*;
use crate::symbolic::PhaseCoefficient;

type Id = usize;
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Add(Vec<Id>),
    Mul(Vec<Id>),
    Select(BooleanPolynomial, Id, Id),
    Neg(Id),
    Inverse(Id),
    Sqrt(Id),
}
#[derive(Clone)]
enum Node {
    Constant(Complex),
    Expression(Key),
}
struct Dag {
    nodes: Vec<Node>,
    supports: Vec<BTreeSet<Variable>>,
    unique: BTreeMap<Key, Id>,
    trig: BTreeMap<(NumericExpr, bool), Id>,
    rationals: BTreeMap<BigRational, Id>,
    phases: BTreeMap<PhaseCoefficient, Id>,
    cofactors: BTreeMap<(Id, Variable, bool), Id>,
    predicates: BTreeMap<(BooleanPolynomial, Variable, bool), BooleanPolynomial>,
    work: usize,
    start: Instant,
    width: usize,
}
impl Dag {
    fn new() -> Self {
        Self {
            nodes: vec![Node::Constant(Complex::n(0)), Node::Constant(Complex::n(1))],
            supports: vec![BTreeSet::new(), BTreeSet::new()],
            unique: BTreeMap::new(),
            trig: BTreeMap::new(),
            rationals: BTreeMap::new(),
            phases: BTreeMap::new(),
            cofactors: BTreeMap::new(),
            predicates: BTreeMap::new(),
            work: crate::equivalence::tuning::limits().interval_work,
            start: Instant::now(),
            width: 0,
        }
    }
    fn tick(&mut self) -> Option<()> {
        self.work = self.work.checked_sub(1)?;
        // Work and wall time bound growth; a separate allocated-node cap
        // rejected useful contractions independently of their live structure.
        (self.start.elapsed()
            < Duration::from_secs(crate::equivalence::tuning::limits().interval_seconds))
        .then_some(())
    }
    fn constant(&mut self, value: Complex) -> Option<Id> {
        self.tick()?;
        if !(value.re.lo.is_finite()
            && value.re.hi.is_finite()
            && value.im.lo.is_finite()
            && value.im.hi.is_finite())
        {
            return None;
        }
        if value.im.lo == 0 && value.im.hi == 0 && value.re.lo == value.re.hi {
            if value.re.lo == 0 {
                return Some(0);
            }
            if value.re.lo == 1 {
                return Some(1);
            }
        }
        // Non-point intervals are enclosures, NOT canonical numeric values.
        // Distinct sources with identical enclosures must not become equal.
        let id = self.nodes.len();
        self.nodes.push(Node::Constant(value));
        self.supports.push(BTreeSet::new());
        Some(id)
    }
    fn rational(&mut self, r: &BigRational) -> Option<Id> {
        if let Some(id) = self.rationals.get(r) {
            return Some(*id);
        }
        let id = self.constant(Complex::real(Interval::rational(r)?))?;
        self.rationals.insert(r.clone(), id);
        Some(id)
    }
    fn value(&self, id: Id) -> Option<Complex> {
        match &self.nodes[id] {
            Node::Constant(v) => Some(v.clone()),
            _ => None,
        }
    }
    fn expression(&mut self, key: Key) -> Option<Id> {
        self.tick()?;
        if let Some(id) = self.unique.get(&key) {
            return Some(*id);
        }
        let mut vars = BTreeSet::new();
        match &key {
            Key::Add(ids) | Key::Mul(ids) => {
                for i in ids {
                    vars.extend(self.supports[*i].iter().cloned());
                }
            }
            Key::Select(p, a, b) => {
                vars.extend(p.variables());
                vars.extend(self.supports[*a].iter().cloned());
                vars.extend(self.supports[*b].iter().cloned());
            }
            Key::Neg(a) | Key::Inverse(a) | Key::Sqrt(a) => {
                vars.extend(self.supports[*a].iter().cloned())
            }
        }
        self.width = self.width.max(vars.len());
        let id = self.nodes.len();
        self.nodes.push(Node::Expression(key.clone()));
        self.supports.push(vars);
        self.unique.insert(key, id);
        Some(id)
    }
    fn select(&mut self, mut p: BooleanPolynomial, mut a: Id, mut b: Id) -> Option<Id> {
        self.tick()?;
        if p.is_one() {
            return Some(a);
        }
        if p.is_zero() {
            return Some(b);
        }
        if a == b {
            return Some(a);
        }
        // Exact XAG complement normalization aligns opposite branch orders.
        let complement = p.xor(&BooleanPolynomial::one());
        if complement < p {
            p = complement;
            std::mem::swap(&mut a, &mut b);
        }
        if let Node::Expression(Key::Select(q, c, _)) = &self.nodes[a] {
            if *q == p {
                a = *c;
            }
        }
        if let Node::Expression(Key::Select(q, _, d)) = &self.nodes[b] {
            if *q == p {
                b = *d;
            }
        }
        if a == b {
            return Some(a);
        }
        self.expression(Key::Select(p, a, b))
    }
    fn factors(&self, id: Id) -> Vec<Id> {
        match &self.nodes[id] {
            Node::Expression(Key::Mul(ids)) => ids.clone(),
            _ => vec![id],
        }
    }
    fn multiply(&mut self, ids: Vec<Id>) -> Option<Id> {
        self.tick()?;
        let mut flat = vec![];
        for id in ids {
            if id == 0 {
                return Some(0);
            }
            if id != 1 {
                flat.extend(self.factors(id));
            }
        }
        flat.sort_unstable();
        if flat.is_empty() {
            return Some(1);
        }
        if flat.len() == 1 {
            return Some(flat[0]);
        }
        let key = Key::Mul(flat.clone());
        if let Some(id) = self.unique.get(&key) {
            return Some(*id);
        }
        let mut constant = Complex::n(1);
        let mut have = false;
        let mut rest = vec![];
        let mut selections: BTreeMap<BooleanPolynomial, Vec<(Id, Id)>> = BTreeMap::new();
        for id in flat {
            match self.nodes[id].clone() {
                Node::Constant(v) => {
                    constant = constant.mul(&v);
                    have = true;
                }
                Node::Expression(Key::Select(p, a, b)) => {
                    selections.entry(p).or_default().push((a, b))
                }
                _ => rest.push(id),
            }
        }
        for (p, branches) in selections {
            let a = self.multiply(branches.iter().map(|b| b.0).collect())?;
            let b = self.multiply(branches.iter().map(|b| b.1).collect())?;
            let id = self.select(p, a, b)?;
            // Aligning branches can turn a selector into a constant. Fold it
            // now, rather than leaving a variable-free Mul expression behind.
            if let Some(v) = self.value(id) {
                constant = constant.mul(&v);
                have = true;
            } else {
                rest.push(id);
            }
        }
        if have {
            rest.push(self.constant(constant)?);
        }
        if rest.contains(&0) {
            self.unique.insert(key, 0);
            return Some(0);
        }
        rest.retain(|id| *id != 1);
        rest.sort_unstable();
        let id = match rest.len() {
            0 => 1,
            1 => rest[0],
            _ => self.expression(Key::Mul(rest))?,
        };
        self.unique.insert(key, id);
        Some(id)
    }
    fn add(&mut self, a: Id, b: Id) -> Option<Id> {
        self.tick()?;
        if a == 0 {
            return Some(b);
        }
        if b == 0 {
            return Some(a);
        }
        let key = Key::Add(vec![a.min(b), a.max(b)]);
        if let Some(id) = self.unique.get(&key) {
            return Some(*id);
        }
        let id = if let (Some(a), Some(b)) = (self.value(a), self.value(b)) {
            self.constant(a.add(&b))?
        } else if let (
            Node::Expression(Key::Select(p, at, af)),
            Node::Expression(Key::Select(q, bt, bf)),
        ) = (self.nodes[a].clone(), self.nodes[b].clone())
        {
            if p == q {
                let t = self.add(at, bt)?;
                let f = self.add(af, bf)?;
                self.select(p, t, f)?
            } else {
                self.common_sum(a, b, key.clone())?
            }
        } else {
            self.common_sum(a, b, key.clone())?
        };
        self.unique.insert(key, id);
        Some(id)
    }
    fn common_sum(&mut self, a: Id, b: Id, key: Key) -> Option<Id> {
        let fa = self.factors(a);
        let fb = self.factors(b);
        let (mut i, mut j) = (0, 0);
        let (mut common, mut ra, mut rb) = (vec![], vec![], vec![]);
        while i < fa.len() && j < fb.len() {
            if fa[i] == fb[j] {
                common.push(fa[i]);
                i += 1;
                j += 1;
            } else if fa[i] < fb[j] {
                ra.push(fa[i]);
                i += 1;
            } else {
                rb.push(fb[j]);
                j += 1;
            }
        }
        ra.extend_from_slice(&fa[i..]);
        rb.extend_from_slice(&fb[j..]);
        if common.is_empty() {
            return self.expression(key);
        }
        let ra = self.multiply(ra)?;
        let rb = self.multiply(rb)?;
        let sum = self.add(ra, rb)?;
        common.push(sum);
        self.multiply(common)
    }
    fn unary(&mut self, key: Key) -> Option<Id> {
        self.tick()?;
        if let Some(id) = self.unique.get(&key) {
            return Some(*id);
        }
        let child = match key {
            Key::Neg(a) | Key::Inverse(a) | Key::Sqrt(a) => a,
            _ => return None,
        };
        let id = if let Some(a) = self.value(child) {
            // Scalar unary operators are real. Phases enter separately.
            if a.im.lo != 0 || a.im.hi != 0 {
                return None;
            }
            let r = match key {
                Key::Neg(_) => a.re.neg(),
                Key::Inverse(_) => Interval::n(1).div(&a.re)?,
                Key::Sqrt(_) => a.re.sqrt()?,
                _ => return None,
            };
            self.constant(Complex::real(r))?
        } else {
            self.expression(key.clone())?
        };
        self.unique.insert(key, id);
        Some(id)
    }
    fn scalar(&mut self, s: &Scalar) -> Option<Id> {
        let mut todo = vec![(s, false)];
        let mut values = vec![];
        while let Some((s, done)) = todo.pop() {
            self.tick()?;
            if done {
                let b = values.pop()?;
                let id = match s {
                    Scalar::Add(..) => self.add(values.pop()?, b)?,
                    Scalar::Mul(..) => self.multiply(vec![values.pop()?, b])?,
                    Scalar::Neg(..) => self.unary(Key::Neg(b))?,
                    Scalar::Inverse(..) => self.unary(Key::Inverse(b))?,
                    Scalar::Sqrt(..) => self.unary(Key::Sqrt(b))?,
                    Scalar::Select { condition, .. } => {
                        self.select(condition.clone(), values.pop()?, b)?
                    }
                    _ => return None,
                };
                values.push(id);
                continue;
            }
            match s {
                Scalar::Rational(r) => values.push(self.rational(r)?),
                Scalar::Sin(a) | Scalar::Cos(a) => {
                    let key = (a.clone(), matches!(s, Scalar::Sin(_)));
                    let id = if let Some(id) = self.trig.get(&key) {
                        *id
                    } else {
                        let v = number(a, 0)?.trig(key.1).finite()?;
                        let id = self.constant(Complex::real(v))?;
                        self.trig.insert(key, id);
                        id
                    };
                    values.push(id);
                }
                Scalar::Add(a, b) | Scalar::Mul(a, b) => {
                    todo.extend([(s, true), (b, false), (a, false)]);
                }
                Scalar::Neg(a) | Scalar::Inverse(a) | Scalar::Sqrt(a) => {
                    todo.extend([(s, true), (a, false)])
                }
                Scalar::Select {
                    when_true: a,
                    when_false: b,
                    ..
                } => todo.extend([(s, true), (b, false), (a, false)]),
            }
        }
        (values.len() == 1).then(|| values.pop()).flatten()
    }
    fn phase(&mut self, a: &PhaseCoefficient) -> Option<Id> {
        if let Some(id) = self.phases.get(a) {
            return Some(*id);
        }
        let value = crate::equivalence::numeric::phase(a)?;
        let id = self.constant(value)?;
        self.phases.insert(a.clone(), id);
        Some(id)
    }
    fn cofactor(&mut self, id: Id, v: &Variable, bit: bool, depth: usize) -> Option<Id> {
        self.tick()?;
        if depth > 512 {
            return None;
        }
        if !self.supports[id].contains(v) {
            return Some(id);
        }
        let key = (id, v.clone(), bit);
        if let Some(r) = self.cofactors.get(&key) {
            return Some(*r);
        }
        let Node::Expression(node) = self.nodes[id].clone() else {
            return Some(id);
        };
        let result = match node {
            Key::Select(p, a, b) => {
                let pk = (p.clone(), v.clone(), bit);
                let p = if let Some(p) = self.predicates.get(&pk) {
                    p.clone()
                } else {
                    let r = p.substitute(v, &BooleanPolynomial::from(bit));
                    self.predicates.insert(pk, r.clone());
                    r
                };
                if p.is_one() {
                    self.cofactor(a, v, bit, depth + 1)?
                } else if p.is_zero() {
                    self.cofactor(b, v, bit, depth + 1)?
                } else {
                    let a = self.cofactor(a, v, bit, depth + 1)?;
                    let b = self.cofactor(b, v, bit, depth + 1)?;
                    self.select(p, a, b)?
                }
            }
            Key::Mul(ids) => {
                let ids = ids
                    .into_iter()
                    .map(|i| self.cofactor(i, v, bit, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                self.multiply(ids)?
            }
            Key::Add(ids) => {
                let mut r = 0;
                for i in ids {
                    let i = self.cofactor(i, v, bit, depth + 1)?;
                    r = self.add(r, i)?;
                }
                r
            }
            Key::Neg(a) => {
                let a = self.cofactor(a, v, bit, depth + 1)?;
                self.unary(Key::Neg(a))?
            }
            Key::Inverse(a) => {
                let a = self.cofactor(a, v, bit, depth + 1)?;
                self.unary(Key::Inverse(a))?
            }
            Key::Sqrt(a) => {
                let a = self.cofactor(a, v, bit, depth + 1)?;
                self.unary(Key::Sqrt(a))?
            }
        };
        self.cofactors.insert(key, result);
        Some(result)
    }
    fn sum_paths(&mut self, mut factors: Vec<Id>, mut paths: BTreeSet<Variable>) -> Option<Id> {
        while !paths.is_empty() {
            self.tick()?;
            let v = paths
                .iter()
                .min_by_key(|v| {
                    let selected: Vec<_> = factors
                        .iter()
                        .filter(|i| self.supports[**i].contains(v))
                        .collect();
                    let scope: BTreeSet<_> = selected
                        .iter()
                        .flat_map(|i| self.supports[**i].iter())
                        .collect();
                    (scope.len(), selected.len())
                })?
                .clone();
            paths.remove(&v);
            let (selected, mut rest): (Vec<_>, Vec<_>) = factors
                .into_iter()
                .partition(|i| self.supports[*i].contains(&v));
            let product = self.multiply(selected)?;
            let a = self.cofactor(product, &v, false, 0)?;
            let b = self.cofactor(product, &v, true, 0)?;
            rest.push(self.add(a, b)?);
            factors = rest;
        }
        self.multiply(factors)
    }
}

pub(super) fn identity_bound(program: &Program) -> Report {
    let mut dag = Dag::new();
    let mut reason = "admission";
    let mut paths = 0;
    let mut lower_bound = None;
    let answer = (|| -> Option<BigRational> {
        unitary::validate(program).ok()?;
        crate::symbolic::numeric_domains(program).ok()?;
        if !program.numeric_inputs.is_empty() {
            return None;
        }
        let wires = super::super::qubits(program);
        let n = wires.len();
        if n > 4096 {
            return None;
        }
        let mut hps = execute(
            program,
            &ExecutionConfig::all_symbolic(),
            &OutputSelection::new(wires, []),
        )
        .ok()?;
        if hps.components.len() != 1 {
            return None;
        }
        reason = "trace construction";
        let c = normalized_trace_component(hps.components.pop()?, &hps.input)?;
        // Charge contraction time here, not while building the input HPS.
        // The experiment/process deadline still includes the whole analysis.
        dag.start = Instant::now();
        paths = c.path_support.len();
        let pending: BTreeSet<_> = c.path_support.iter().copied().map(Variable::Path).collect();
        let mut factors = vec![];
        let mut scalar_factors = vec![&c.scalar];
        reason = "scalar structure";
        while let Some(s) = scalar_factors.pop() {
            if let Scalar::Mul(a, b) = s {
                scalar_factors.extend([a.as_ref(), b.as_ref()]);
            } else {
                factors.push(dag.scalar(s)?);
            }
        }
        reason = "guard structure";
        for p in &c.guard {
            factors.push(dag.select(p.clone(), 0, 1)?);
        }
        reason = "phase structure";
        for (p, a) in c.phase.selectors() {
            let value = dag.phase(a)?;
            // A half turn is a Boolean sign. Its XOR factors multiply exactly,
            // so do not join every independent local phase into a giant scope.
            // This only exposes existing XOR fanins; AND is never distributed.
            if a.as_rational() == Some(BigRational::new(1.into(), 2.into())) {
                for term in p.xor_terms() {
                    factors.push(dag.select(term, value, 1)?);
                }
            } else {
                factors.push(dag.select(p, value, 1)?);
            }
        }
        reason = "unbound factor coordinates";
        if factors
            .iter()
            .any(|i| !dag.supports[*i].is_subset(&pending))
        {
            return None;
        }
        reason = "structural reduction budget";
        let result = dag.sum_paths(factors, pending)?;
        reason = "residual symbolic amplitude";
        let trace = dag.value(result)?;
        reason = "numerical enclosure";
        let (upper, lower) = trace_bounds(&trace, n)?;
        lower_bound = Some(lower);
        reason = "bounded";
        Some(upper)
    })();
    Report {
        method: "structured",
        precision: PREC,
        bound: answer,
        lower_bound,
        reason,
        paths,
        work: crate::equivalence::tuning::limits().interval_work - dag.work,
        max_width: dag.width,
        nodes: dag.nodes.len(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_scalar_import_is_iterative() {
        let mut s = Scalar::one();
        for _ in 0..200 {
            s = Scalar::Mul(Box::new(s), Box::new(Scalar::one()));
        }
        let mut d = Dag::new();
        let id = d.scalar(&s).unwrap();
        assert_eq!(id, 1);
    }
    #[test]
    fn wide_predicate_stays_shared_and_complements_cancel() {
        let p = (0..100)
            .map(|i| BooleanPolynomial::variable(Variable::Path(i)))
            .fold(BooleanPolynomial::zero(), |p, q| p.xor(&q));
        let mut d = Dag::new();
        let two = d.rational(&BigRational::from_integer(2.into())).unwrap();
        let a = d.select(p.clone(), two, 1).unwrap();
        let b = d.select(p.xor(&BooleanPolynomial::one()), two, 1).unwrap();
        let sum = d.add(a, b).unwrap();
        assert!(d.nodes.len() < 20);
        let value = d.value(sum).unwrap();
        assert_eq!(value.re.lo, 3);
        assert_eq!(value.re.hi, 3);
    }
    #[test]
    fn equal_enclosures_are_not_an_equality_test() {
        let mut d = Dag::new();
        let v = Complex::real(Interval {
            lo: Float::with_val(PREC, 0),
            hi: Float::with_val(PREC, 1),
        });
        let a = d.constant(v.clone()).unwrap();
        let b = d.constant(v).unwrap();
        assert_ne!(a, b);
        let p = BooleanPolynomial::variable(Variable::Path(0));
        let s = d.select(p, a, b).unwrap();
        assert!(d.value(s).is_none());
    }
    #[test]
    fn same_condition_factors_align_without_assignment_enumeration() {
        let mut d = Dag::new();
        let p = BooleanPolynomial::variable(Variable::Path(0));
        let a = d.select(p.clone(), 0, 1).unwrap();
        let b = d.select(p, 1, 0).unwrap();
        assert_eq!(d.multiply(vec![a, b]).unwrap(), 0);
    }
    #[test]
    fn collapsed_selectors_finish_constant_multiplication() {
        let mut d = Dag::new();
        let p = BooleanPolynomial::variable(Variable::Path(0));
        let q = BooleanPolynomial::variable(Variable::Path(1));
        let minus = d.rational(&BigRational::from_integer((-1).into())).unwrap();
        let two = d.rational(&BigRational::from_integer(2.into())).unwrap();
        let a = d.select(p, minus, 1).unwrap();
        let b = d.select(q, minus, 1).unwrap();
        let product = d.multiply(vec![a, a, b, b, two]).unwrap();
        let value = d.value(product).unwrap();
        assert_eq!(value.re.lo, 2);
        assert_eq!(value.re.hi, 2);
    }
    #[test]
    fn half_turn_xor_factors_preserve_all_assignments() {
        let mut d = Dag::new();
        let p = BooleanPolynomial::variable(Variable::Path(0));
        let q = BooleanPolynomial::variable(Variable::Path(1));
        let minus = d.rational(&BigRational::from_integer((-1).into())).unwrap();
        let root = p.xor(&q).xor(&BooleanPolynomial::one());
        let direct = d.select(root.clone(), minus, 1).unwrap();
        let factors = root
            .xor_terms()
            .into_iter()
            .map(|p| d.select(p, minus, 1).unwrap())
            .collect();
        let split = d.multiply(factors).unwrap();
        for a in [false, true] {
            for b in [false, true] {
                let eval = |d: &mut Dag, id| {
                    let id = d.cofactor(id, &Variable::Path(0), a, 0).unwrap();
                    let id = d.cofactor(id, &Variable::Path(1), b, 0).unwrap();
                    d.value(id).unwrap()
                };
                let x = eval(&mut d, direct);
                let y = eval(&mut d, split);
                assert_eq!(x.re.lo, y.re.lo);
                assert_eq!(x.re.hi, y.re.hi);
            }
        }
    }
}
