//! Structural scalar/phase arithmetic over shared Boolean predicates.
//! No truth tables, floating-point predicate equality, or sampled inputs.
use super::*;
use crate::symbolic::PhaseCoefficient;
use hashbrown::{DefaultHashBuilder, HashMap, HashTable};
use smallvec::SmallVec;
use std::hash::BuildHasher;

type Id = usize;
type PredicateId = usize;
type VariableId = usize;
type Support = SmallVec<[VariableId; 4]>;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Key {
    Add(Id, Id),
    Mul(Vec<Id>),
    Select(PredicateId, Id, Id),
    Neg(Id),
    Inverse(Id),
    Sqrt(Id),
}
#[derive(Clone)]
enum Node {
    Constant(usize),
    Expression(Key),
}
struct Predicate {
    expression: BooleanPolynomial,
    support: Support,
    normalized: Option<(PredicateId, bool)>,
}

/// Completed paired restrictions only. A slot belongs to one variable; stale
/// entries cannot be reused when the next elimination round starts.
#[derive(Default)]
struct Cofactors(Vec<(VariableId, [Id; 2])>);
impl Cofactors {
    fn get(&self, id: Id, variable: VariableId) -> Option<[Id; 2]> {
        let (v, pair) = self.0.get(id)?;
        (*v == variable).then_some(*pair)
    }
    fn insert(&mut self, id: Id, variable: VariableId, pair: [Id; 2]) {
        if id >= self.0.len() {
            self.0.resize(id + 1, (usize::MAX, [0; 2]));
        }
        self.0[id] = (variable, pair);
    }
}
struct Dag {
    nodes: Vec<Node>,
    constants: Vec<Complex>,
    supports: Vec<Support>,
    // The canonical key lives in nodes, not a second copy in this table.
    unique: HashTable<Id>,
    hashes: Vec<u64>,
    hasher: DefaultHashBuilder,
    // Operation aliases (e.g. a pre-normalization product -> a constant)
    // belong here, never in the canonical node table.
    computed: HashMap<Key, Id>,
    predicate_ids: BTreeMap<BooleanPolynomial, PredicateId>,
    predicates: Vec<Predicate>,
    variable_ids: BTreeMap<Variable, VariableId>,
    variables: Vec<Variable>,
    trig: BTreeMap<(NumericExpr, bool), Id>,
    rationals: BTreeMap<BigRational, Id>,
    phases: BTreeMap<PhaseCoefficient, Id>,
    cofactors: Cofactors,
    predicate_cofactors: HashMap<(PredicateId, VariableId), [PredicateId; 2]>,
    contractions: HashMap<(Vec<Id>, VariableId), Id>,
    work: usize,
    start: Instant,
    width: usize,
}
impl Dag {
    fn new() -> Self {
        let mut dag = Self {
            nodes: vec![Node::Constant(0), Node::Constant(1)],
            constants: vec![Complex::n(0), Complex::n(1)],
            supports: vec![Support::new(), Support::new()],
            unique: HashTable::new(),
            hashes: vec![0, 0],
            hasher: DefaultHashBuilder::default(),
            computed: HashMap::new(),
            predicate_ids: BTreeMap::new(),
            predicates: vec![],
            variable_ids: BTreeMap::new(),
            variables: vec![],
            trig: BTreeMap::new(),
            rationals: BTreeMap::new(),
            phases: BTreeMap::new(),
            cofactors: Cofactors::default(),
            predicate_cofactors: HashMap::new(),
            contractions: HashMap::new(),
            work: crate::equivalence::tuning::limits().interval_work,
            start: Instant::now(),
            width: 0,
        };
        dag.predicate(BooleanPolynomial::zero());
        dag.predicate(BooleanPolynomial::one());
        dag
    }
    fn variable(&mut self, v: Variable) -> VariableId {
        if let Some(id) = self.variable_ids.get(&v) {
            return *id;
        }
        let id = self.variables.len();
        self.variables.push(v.clone());
        self.variable_ids.insert(v, id);
        id
    }
    fn predicate(&mut self, p: BooleanPolynomial) -> PredicateId {
        if let Some(id) = self.predicate_ids.get(&p) {
            return *id;
        }
        let mut support: Support = p
            .variables()
            .into_iter()
            .map(|v| self.variable(v))
            .collect();
        support.sort_unstable();
        let id = self.predicates.len();
        self.predicates.push(Predicate {
            expression: p.clone(),
            support,
            normalized: None,
        });
        self.predicate_ids.insert(p, id);
        id
    }
    fn normalized_predicate(&mut self, p: PredicateId) -> (PredicateId, bool) {
        if let Some(result) = self.predicates[p].normalized {
            return result;
        }
        let complement = self.predicates[p].expression.xor(&BooleanPolynomial::one());
        let flipped = complement < self.predicates[p].expression;
        let q = self.predicate(complement);
        let canonical = if flipped { q } else { p };
        self.predicates[p].normalized = Some((canonical, flipped));
        self.predicates[q].normalized = Some((canonical, !flipped));
        (canonical, flipped)
    }
    fn tick(&mut self) -> Option<()> {
        if crate::symbolic::deadline::expired() {
            return None;
        }
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
        self.nodes.push(Node::Constant(self.constants.len()));
        self.constants.push(value);
        self.supports.push(Support::new());
        self.hashes.push(0);
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
            Node::Constant(v) => Some(self.constants[*v].clone()),
            _ => None,
        }
    }
    fn expression(&mut self, key: Key) -> Option<Id> {
        self.tick()?;
        let hash = self.hasher.hash_one(&key);
        if let Some(id) = self.unique.find(
            hash,
            |id| matches!(&self.nodes[*id], Node::Expression(existing) if existing == &key),
        ) {
            return Some(*id);
        }
        let mut vars = Support::new();
        match &key {
            Key::Add(a, b) => {
                vars.extend_from_slice(&self.supports[*a]);
                vars.extend_from_slice(&self.supports[*b]);
            }
            Key::Mul(ids) => {
                for i in ids {
                    vars.extend(self.supports[*i].iter().cloned());
                }
            }
            Key::Select(p, a, b) => {
                vars.extend_from_slice(&self.predicates[*p].support);
                vars.extend(self.supports[*a].iter().cloned());
                vars.extend(self.supports[*b].iter().cloned());
            }
            Key::Neg(a) | Key::Inverse(a) | Key::Sqrt(a) => {
                vars.extend(self.supports[*a].iter().cloned())
            }
        }
        vars.sort_unstable();
        vars.dedup();
        self.width = self.width.max(vars.len());
        let id = self.nodes.len();
        self.nodes.push(Node::Expression(key));
        self.supports.push(vars);
        self.hashes.push(hash);
        self.unique.insert_unique(hash, id, |id| self.hashes[*id]);
        Some(id)
    }
    fn select(&mut self, p: BooleanPolynomial, a: Id, b: Id) -> Option<Id> {
        let p = self.predicate(p);
        self.select_id(p, a, b)
    }
    fn select_id(&mut self, p: PredicateId, mut a: Id, mut b: Id) -> Option<Id> {
        self.tick()?;
        if p == 1 {
            return Some(a);
        }
        if p == 0 {
            return Some(b);
        }
        if a == b {
            return Some(a);
        }
        // Exact XAG complement normalization aligns opposite branch orders.
        let (p, flipped) = self.normalized_predicate(p);
        if flipped {
            std::mem::swap(&mut a, &mut b);
        }
        if let Node::Expression(Key::Select(q, c, _)) = &self.nodes[a]
            && *q == p
        {
            a = *c;
        }
        if let Node::Expression(Key::Select(q, _, d)) = &self.nodes[b]
            && *q == p
        {
            b = *d;
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
        if let Some(id) = self.computed.get(&key) {
            return Some(*id);
        }
        let mut constant = Complex::n(1);
        let mut have = false;
        let mut rest = vec![];
        let mut selections: BTreeMap<PredicateId, Vec<(Id, Id)>> = BTreeMap::new();
        for id in flat {
            match &self.nodes[id] {
                Node::Constant(v) => {
                    constant = constant.mul(&self.constants[*v]);
                    have = true;
                }
                Node::Expression(Key::Select(p, a, b)) => {
                    selections.entry(*p).or_default().push((*a, *b))
                }
                _ => rest.push(id),
            }
        }
        for (p, branches) in selections {
            let a = self.multiply(branches.iter().map(|b| b.0).collect())?;
            let b = self.multiply(branches.iter().map(|b| b.1).collect())?;
            let id = self.select_id(p, a, b)?;
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
            self.computed.insert(key, 0);
            return Some(0);
        }
        rest.retain(|id| *id != 1);
        rest.sort_unstable();
        let id = match rest.len() {
            0 => 1,
            1 => rest[0],
            _ => self.expression(Key::Mul(rest))?,
        };
        self.computed.insert(key, id);
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
        let key = Key::Add(a.min(b), a.max(b));
        if let Some(id) = self.computed.get(&key) {
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
                self.select_id(p, t, f)?
            } else {
                self.common_sum(a, b, key.clone())?
            }
        } else {
            self.common_sum(a, b, key.clone())?
        };
        self.computed.insert(key, id);
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
        if let Some(id) = self.computed.get(&key) {
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
        self.computed.insert(key, id);
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
    #[cfg(test)]
    fn cofactor(&mut self, id: Id, v: &Variable, bit: bool, depth: usize) -> Option<Id> {
        let v = self.variable(v.clone());
        Some(self.cofactor_pair(id, v, depth)?[usize::from(bit)])
    }
    fn predicate_pair(&mut self, p: PredicateId, v: VariableId) -> [PredicateId; 2] {
        if self.predicates[p].support.binary_search(&v).is_err() {
            return [p; 2];
        }
        if let Some(pair) = self.predicate_cofactors.get(&(p, v)) {
            return *pair;
        }
        let expression = self.predicates[p].expression.clone();
        let low = expression.substitute(&self.variables[v], &BooleanPolynomial::zero());
        let high = expression.substitute(&self.variables[v], &BooleanPolynomial::one());
        let pair = [self.predicate(low), self.predicate(high)];
        self.predicate_cofactors.insert((p, v), pair);
        pair
    }
    /// Restrict both branches in one DAG walk. This is arithmetic restriction,
    /// not a conversion of the HPS/XAG to a globally ordered decision diagram.
    fn cofactor_pair(&mut self, id: Id, v: VariableId, depth: usize) -> Option<[Id; 2]> {
        self.restrict(id, v, [true; 2], depth)
    }
    fn restrict(
        &mut self,
        id: Id,
        v: VariableId,
        needed: [bool; 2],
        depth: usize,
    ) -> Option<[Id; 2]> {
        self.tick()?;
        if depth > 512 {
            return None;
        }
        if needed == [false; 2] {
            return Some([0; 2]);
        }
        if self.supports[id].binary_search(&v).is_err() {
            return Some([id; 2]);
        }
        if let Some(pair) = self.cofactors.get(id, v) {
            return Some(pair);
        }
        let Node::Expression(node) = self.nodes[id].clone() else {
            return Some([id; 2]);
        };
        let result = match node {
            Key::Select(p, a, b) => {
                let p = self.predicate_pair(p, v);
                // Do not evaluate a branch that this restriction discards:
                // it may be expensive or undefined (e.g. inverse of zero).
                let a = self.restrict(
                    a,
                    v,
                    [needed[0] && p[0] != 0, needed[1] && p[1] != 0],
                    depth + 1,
                )?;
                let b = self.restrict(
                    b,
                    v,
                    [needed[0] && p[0] != 1, needed[1] && p[1] != 1],
                    depth + 1,
                )?;
                [
                    if needed[0] {
                        self.select_id(p[0], a[0], b[0])?
                    } else {
                        0
                    },
                    if needed[1] {
                        self.select_id(p[1], a[1], b[1])?
                    } else {
                        0
                    },
                ]
            }
            Key::Mul(ids) => {
                let mut low = Vec::with_capacity(ids.len());
                let mut high = Vec::with_capacity(ids.len());
                for i in ids {
                    let [a, b] = self.restrict(i, v, needed, depth + 1)?;
                    low.push(a);
                    high.push(b);
                }
                [
                    if needed[0] { self.multiply(low)? } else { 0 },
                    if needed[1] { self.multiply(high)? } else { 0 },
                ]
            }
            Key::Add(a, b) => {
                let a = self.restrict(a, v, needed, depth + 1)?;
                let b = self.restrict(b, v, needed, depth + 1)?;
                [
                    if needed[0] { self.add(a[0], b[0])? } else { 0 },
                    if needed[1] { self.add(a[1], b[1])? } else { 0 },
                ]
            }
            Key::Neg(a) => {
                let a = self.restrict(a, v, needed, depth + 1)?;
                [
                    if needed[0] {
                        self.unary(Key::Neg(a[0]))?
                    } else {
                        0
                    },
                    if needed[1] {
                        self.unary(Key::Neg(a[1]))?
                    } else {
                        0
                    },
                ]
            }
            Key::Inverse(a) => {
                let a = self.restrict(a, v, needed, depth + 1)?;
                [
                    if needed[0] {
                        self.unary(Key::Inverse(a[0]))?
                    } else {
                        0
                    },
                    if needed[1] {
                        self.unary(Key::Inverse(a[1]))?
                    } else {
                        0
                    },
                ]
            }
            Key::Sqrt(a) => {
                let a = self.restrict(a, v, needed, depth + 1)?;
                [
                    if needed[0] {
                        self.unary(Key::Sqrt(a[0]))?
                    } else {
                        0
                    },
                    if needed[1] {
                        self.unary(Key::Sqrt(a[1]))?
                    } else {
                        0
                    },
                ]
            }
        };
        if needed == [true; 2] {
            self.cofactors.insert(id, v, result);
        }
        Some(result)
    }

    /// Fused sum-product, inspired by CUDD's addMMRecur: restrict the operands
    /// and immediately combine the eliminated branches, without first building
    /// their unrestricted product. Keep nontrivial products factored; never
    /// distribute a product over every Add or expand a predicate truth table.
    fn sum_product(&mut self, ids: Vec<Id>, v: VariableId, depth: usize) -> Option<Id> {
        self.tick()?;
        if depth > 512 {
            return None;
        }
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
        let key = (flat.clone(), v);
        if let Some(result) = self.contractions.get(&key) {
            return Some(*result);
        }
        let (dependent, mut independent): (Vec<_>, Vec<_>) = flat
            .into_iter()
            .partition(|id| self.supports[*id].binary_search(&v).is_ok());
        let result = if dependent.is_empty() {
            // Sum_y 1 = 2, including coordinates removed by earlier rewriting.
            self.rational(&BigRational::from_integer(2.into()))?
        } else if dependent.len() == 1 {
            match self.nodes[dependent[0]].clone() {
                Node::Expression(Key::Add(a, b)) => {
                    let a = self.sum_product(vec![a], v, depth + 1)?;
                    let b = self.sum_product(vec![b], v, depth + 1)?;
                    self.add(a, b)?
                }
                Node::Expression(Key::Neg(a)) => {
                    let a = self.sum_product(vec![a], v, depth + 1)?;
                    self.unary(Key::Neg(a))?
                }
                _ => {
                    let [a, b] = self.cofactor_pair(dependent[0], v, depth + 1)?;
                    self.add(a, b)?
                }
            }
        } else {
            let mut low = Vec::with_capacity(dependent.len());
            let mut high = Vec::with_capacity(dependent.len());
            for id in dependent {
                let [a, b] = self.cofactor_pair(id, v, depth + 1)?;
                low.push(a);
                high.push(b);
            }
            let a = self.multiply(low)?;
            let b = self.multiply(high)?;
            self.add(a, b)?
        };
        independent.push(result);
        let result = self.multiply(independent)?;
        self.contractions.insert(key, result);
        Some(result)
    }
    fn sum_paths(&mut self, mut factors: Vec<Id>, paths: BTreeSet<Variable>) -> Option<Id> {
        // Preserve the original Variable ordering as the tie breaker, even
        // though local IDs are assigned in predicate-import order.
        let mut paths: Vec<_> = paths.into_iter().map(|v| self.variable(v)).collect();
        while !paths.is_empty() {
            self.tick()?;
            let v = *paths.iter().min_by_key(|v| {
                let selected: Vec<_> = factors
                    .iter()
                    .filter(|i| self.supports[**i].binary_search(v).is_ok())
                    .collect();
                let scope: BTreeSet<_> = selected
                    .iter()
                    .flat_map(|i| self.supports[**i].iter())
                    .collect();
                (scope.len(), selected.len())
            })?;
            paths.retain(|p| *p != v);
            let (selected, mut rest): (Vec<_>, Vec<_>) = factors
                .into_iter()
                .partition(|i| self.supports[*i].binary_search(&v).is_ok());
            rest.push(self.sum_product(selected, v, 0)?);
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
        // The ordinary contraction allowance starts here. The enclosing
        // short-probe deadline still covers execution and trace construction
        // and is never reset by this local timer.
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
        if factors.iter().any(|i| {
            dag.supports[*i]
                .iter()
                .any(|v| !pending.contains(&dag.variables[*v]))
        }) {
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

pub(super) const TIME_BUDGET_REASON: &str = "HPS time budget";

/// Includes execution, trace simplification and contraction in one deadline.
pub(super) fn identity_bound_with_budget(program: &Program, budget: Duration) -> Report {
    let mut report = Report {
        method: "structured",
        precision: PREC,
        bound: None,
        lower_bound: None,
        reason: TIME_BUDGET_REASON,
        paths: 0,
        work: 0,
        max_width: 0,
        nodes: 0,
    };
    let completed = crate::symbolic::deadline::within(budget, || {
        report = identity_bound(program);
    });
    if completed.is_none() {
        report.bound = None;
        report.lower_bound = None;
        report.reason = TIME_BUDGET_REASON;
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fused_sum_preserves_nonlinear_predicates_and_missing_coordinates() {
        // Independent integer oracle; compare actual values, not node IDs.
        for seed in 0..16 {
            let mut d = Dag::new();
            let vars: Vec<_> = (0..4)
                .map(|i| BooleanPolynomial::variable(Variable::Path(i)))
                .collect();
            let mut factors = vec![];
            let mut oracle = vec![];
            for j in 0..5 {
                let a = (seed + j) % 4;
                let b = (seed + 2 * j + 1) % 4;
                let c = (seed + 3 * j + 2) % 4;
                let p = vars[a].and(&vars[b]).xor(&vars[c]);
                let t = (j as i64 % 3) - 1;
                let f = (seed as i64 % 3) + 1;
                let ti = d.rational(&BigRational::from_integer(t.into())).unwrap();
                let fi = d.rational(&BigRational::from_integer(f.into())).unwrap();
                factors.push(d.select(p, ti, fi).unwrap());
                oracle.push((a, b, c, t, f));
            }
            // Path 9 is absent: summing over it must still double the result.
            let expected: i64 = 2
                * (0..16)
                    .map(|assignment| {
                        oracle
                            .iter()
                            .map(|&(a, b, c, t, f)| {
                                let bit = |i| assignment & (1 << i) != 0;
                                if (bit(a) && bit(b)) ^ bit(c) { t } else { f }
                            })
                            .product::<i64>()
                    })
                    .sum::<i64>();
            let paths = [0, 1, 2, 3, 9].into_iter().map(Variable::Path).collect();
            let id = d.sum_paths(factors, paths).unwrap();
            let value = d.value(id).unwrap();
            assert_eq!(value.re.lo, expected);
            assert_eq!(value.re.hi, expected);
            assert!(value.im.is_zero());
        }
    }

    #[test]
    fn paired_restriction_does_not_evaluate_discarded_inverse() {
        let mut d = Dag::new();
        let y = BooleanPolynomial::variable(Variable::Path(0));
        let indicator = d.select(y.clone(), 1, 0).unwrap();
        let inverse = d.unary(Key::Inverse(indicator)).unwrap();
        let guarded = d.select(y, inverse, 1).unwrap();
        let id = d
            .sum_paths(vec![guarded], BTreeSet::from([Variable::Path(0)]))
            .unwrap();
        let value = d.value(id).unwrap();
        assert_eq!(value.re.lo, 2);
        assert_eq!(value.re.hi, 2);
    }

    #[test]
    fn cofactor_cache_does_not_alias_variables_or_partial_results() {
        let mut d = Dag::new();
        let y = BooleanPolynomial::variable(Variable::Path(0));
        let z = BooleanPolynomial::variable(Variable::Path(1));
        let root = d.select(y.and(&z), 1, 0).unwrap();
        for variable in [0, 1, 0] {
            let v = d.variable(Variable::Path(variable));
            let partial = d.restrict(root, v, [true, false], 0).unwrap();
            assert_eq!(partial[0], 0);
            let pair = d.cofactor_pair(root, v, 0).unwrap();
            assert_eq!(pair[0], 0);
            let other = Variable::Path(1 - variable);
            assert_eq!(d.cofactor(pair[1], &other, false, 0), Some(0));
            assert_eq!(d.cofactor(pair[1], &other, true, 0), Some(1));
        }
    }

    #[test]
    fn fused_sum_keeps_interval_uncertainty() {
        let mut d = Dag::new();
        let x = d
            .constant(Complex::real(Interval {
                lo: Float::with_val(PREC, 1),
                hi: Float::with_val(PREC, 2),
            }))
            .unwrap();
        let p = BooleanPolynomial::variable(Variable::Path(0));
        let y = d.select(p.clone(), x, 1).unwrap();
        let z = d.select(p, 1, x).unwrap();
        let id = d
            .sum_paths(vec![y, z], BTreeSet::from([Variable::Path(0)]))
            .unwrap();
        let value = d.value(id).unwrap();
        assert!(value.re.lo <= 2 && value.re.hi >= 4);
        assert!(value.re.lo < value.re.hi);
    }

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
