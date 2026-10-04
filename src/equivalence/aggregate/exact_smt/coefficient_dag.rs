//! Complete local sums over Q(zeta_8), with rational-valued DAG coefficients.
//! No SMT definitions or expanded phase atoms are generated during contraction.
//! Both bound cofactors are added; free coordinates remain symbolic. Larger
//! fields and unsupported scalars decline this optional certificate route.
use super::*;
mod simplify;

type Id = usize;
type Value = [Id; 4];
const ZERO: Value = [0; 4];
const ONE: Value = [1, 0, 0, 0];

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Constant(BigRational),
    Select(KernelBooleanPolynomial, Id, Id),
    Add(Id, Id),
    Multiply(Id, Id),
    Scale(BigRational, Id),
}

struct Dag {
    nodes: Vec<Node>,
    unique: BTreeMap<Node, Id>,
    work: usize,
    started: std::time::Instant,
    simplify: bool,
    expression_simplify: bool,
    context_enabled: bool,
    context_cache: BTreeMap<(Id, KernelBooleanPolynomial), Id>,
    context_support: BTreeMap<Id, Option<BTreeSet<KernelVariable>>>,
    context_work: usize,
}

impl Dag {
    fn new() -> Self {
        let nodes = vec![Node::Constant(integer(0)), Node::Constant(integer(1))];
        let expression_simplify =
            crate::ablation::permit(crate::ablation::Group::ExpressionSimplify);
        Self {
            unique: nodes
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, n)| (n, i))
                .collect(),
            nodes,
            work: crate::equivalence::tuning::limits().coefficient_work,
            started: std::time::Instant::now(),
            expression_simplify,
            simplify: expression_simplify
                && matches!(
                    std::env::var("IRENE_COEFFICIENT_SIMPLIFY").as_deref(),
                    Ok("light")
                ),
            context_enabled: expression_simplify
                && std::env::var_os("IRENE_DISABLE_COEFFICIENT_CONTEXT").is_none(),
            context_cache: BTreeMap::new(),
            context_support: BTreeMap::new(),
            context_work: crate::equivalence::tuning::limits().context_work,
        }
    }
    fn tick(&mut self) -> Option<()> {
        self.work = self.work.checked_sub(1)?;
        (self.started.elapsed().as_secs() < 120).then_some(())
    }
    fn node(&mut self, n: Node) -> Option<Id> {
        self.tick()?;
        if let Some(&id) = self.unique.get(&n) {
            return Some(id);
        }
        if self.nodes.len() >= crate::equivalence::tuning::limits().coefficient_nodes {
            return None;
        }
        let id = self.nodes.len();
        self.nodes.push(n.clone());
        self.unique.insert(n, id);
        Some(id)
    }
    fn constant(&mut self, r: BigRational) -> Option<Id> {
        if r.numer().bits() > MAX_BITS || r.denom().bits() > MAX_BITS {
            return None;
        }
        self.node(Node::Constant(r))
    }
    fn scaled(&self, a: Id) -> (BigRational, Id) {
        match &self.nodes[a] {
            Node::Constant(r) => (r.clone(), 1),
            Node::Scale(r, v) => (r.clone(), *v),
            _ => (integer(1), a),
        }
    }
    fn scale(&mut self, a: Id, r: BigRational) -> Option<Id> {
        let (s, a) = self.scaled(a);
        let r = r * s;
        if r == integer(0) {
            return Some(0);
        }
        if a == 1 {
            return self.constant(r);
        }
        if r == integer(1) {
            return Some(a);
        }
        if r.numer().bits() > MAX_BITS || r.denom().bits() > MAX_BITS {
            return None;
        }
        self.node(Node::Scale(r, a))
    }
    fn add(&mut self, a: Id, b: Id) -> Option<Id> {
        if a == 0 {
            return Some(b);
        }
        if b == 0 {
            return Some(a);
        }
        if self.simplify
            && let Some(result) = self.simplify_add(a, b)
        {
            return Some(result);
        }
        let (ra, va) = self.scaled(a);
        let (rb, vb) = self.scaled(b);
        if va == vb {
            return self.scale(va, ra + rb);
        }
        // 1-[p] and weighted variants remain selectors, not arithmetic trees.
        if self.expression_simplify
            && va == 1
            && let Some(p) = self.indicator(vb)
        {
            let yes = self.constant(&ra + rb)?;
            let no = self.constant(ra)?;
            return self.select(p, yes, no);
        }
        if self.expression_simplify
            && vb == 1
            && let Some(p) = self.indicator(va)
        {
            let yes = self.constant(ra + &rb)?;
            let no = self.constant(rb)?;
            return self.select(p, yes, no);
        }
        self.node(Node::Add(a.min(b), a.max(b)))
    }
    fn indicator(&self, id: Id) -> Option<KernelBooleanPolynomial> {
        match &self.nodes[id] {
            Node::Select(p, 1, 0) => Some(p.clone()),
            Node::Select(p, 0, 1) => Some(KernelBooleanPolynomial::from_graph(
                p.as_graph().complement(),
            )),
            _ => None,
        }
    }
    fn multiply(&mut self, a: Id, b: Id) -> Option<Id> {
        if a == 0 || b == 0 {
            return Some(0);
        }
        if self.simplify
            && let Some(result) = self.simplify_multiply(a, b)
        {
            return Some(result);
        }
        let (ra, a) = self.scaled(a);
        let (rb, b) = self.scaled(b);
        let base = if self.expression_simplify
            && let (Some(p), Some(q)) = (self.indicator(a), self.indicator(b))
        {
            // Indicator multiplication is Boolean AND, hence idempotent and
            // mutually exclusive guards annihilate before coefficient lowering.
            let p = KernelBooleanPolynomial::from_graph(p.as_graph().and(&q.as_graph()));
            self.select(p, 1, 0)?
        } else if a == 1 {
            b
        } else if b == 1 {
            a
        } else {
            self.node(Node::Multiply(a.min(b), a.max(b)))?
        };
        self.scale(base, ra * rb)
    }
    fn select(&mut self, p: KernelBooleanPolynomial, a: Id, b: Id) -> Option<Id> {
        if p.is_one() || a == b {
            return Some(a);
        }
        if p.is_zero() {
            return Some(b);
        }
        if self.simplify
            && let Some(result) = self.simplify_select(&p, a, b)
        {
            return Some(result);
        }
        self.node(Node::Select(p, a, b))
    }
    fn plus(&mut self, a: Value, b: Value) -> Option<Value> {
        let mut c = ZERO;
        for i in 0..4 {
            c[i] = self.add(a[i], b[i])?;
        }
        Some(c)
    }
    fn times(&mut self, a: Value, b: Value) -> Option<Value> {
        let mut c = ZERO;
        for i in 0..4 {
            for j in 0..4 {
                let mut term = self.multiply(a[i], b[j])?;
                if i + j >= 4 {
                    term = self.scale(term, integer(-1))?;
                }
                c[(i + j) % 4] = self.add(c[(i + j) % 4], term)?;
            }
        }
        Some(c)
    }
    fn phase(&mut self, a: Value, p: KernelBooleanPolynomial, k: usize) -> Option<Value> {
        let mut shifted = ZERO;
        for (i, &v) in a.iter().enumerate() {
            shifted[(i + k) % 4] = self.scale(v, integer(if (i + k) % 8 >= 4 { -1 } else { 1 }))?;
        }
        let mut c = ZERO;
        for i in 0..4 {
            c[i] = self.select(p.clone(), shifted[i], a[i])?;
        }
        Some(c)
    }
    fn scalar(&mut self, s: &KernelScalar, depth: usize) -> Option<Value> {
        self.tick()?;
        if depth >= 64 {
            return None;
        }
        match s {
            KernelScalar::Rational(r) => Some([self.constant(r.clone())?, 0, 0, 0]),
            KernelScalar::Neg(a) => {
                let a = self.scalar(a, depth + 1)?;
                let mut c = ZERO;
                for i in 0..4 {
                    c[i] = self.scale(a[i], integer(-1))?;
                }
                Some(c)
            }
            KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
                let a = self.scalar(a, depth + 1)?;
                let b = self.scalar(b, depth + 1)?;
                if matches!(s, KernelScalar::Add(..)) {
                    self.plus(a, b)
                } else {
                    self.times(a, b)
                }
            }
            KernelScalar::Inverse(a) => {
                let KernelScalar::Rational(r) = a.as_ref() else {
                    return None;
                };
                if *r == integer(0) {
                    return None;
                }
                Some([self.constant(r.recip())?, 0, 0, 0])
            }
            KernelScalar::Sqrt(a) => {
                let KernelScalar::Rational(r) = a.as_ref() else {
                    return None;
                };
                if let Some(v) = rational_root(r) {
                    return Some([self.constant(v)?, 0, 0, 0]);
                }
                let v = rational_root(&(r * integer(2)))? / integer(2);
                Some([0, self.constant(v.clone())?, 0, self.constant(-v)?])
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                // Validate and construct BOTH branches, even for a constant guard.
                let a = self.scalar(when_true, depth + 1)?;
                let b = self.scalar(when_false, depth + 1)?;
                let mut c = ZERO;
                for i in 0..4 {
                    c[i] = self.select(condition.clone(), a[i], b[i])?;
                }
                Some(c)
            }
            _ => None,
        }
    }
    fn leaf(&mut self, t: &WorkingTerm) -> Option<Value> {
        let mut a = self.scalar(&t.coefficient, 0)?;
        for (p, c) in t.phase.selectors() {
            let e = exponent(&c)?;
            if e % (ORDER / 8) != 0 {
                return None;
            }
            a = self.phase(a, p, (e / (ORDER / 8)) as usize)?;
        }
        let guard = crate::symbolic::BooleanPolynomial::and_all(
            t.constraints.iter().map(|p| p.as_graph().complement()),
        );
        let guard = KernelBooleanPolynomial::from_graph(guard);
        for v in &mut a {
            *v = self.select(guard.clone(), *v, 0)?;
        }
        Some(a)
    }
}

struct Table {
    scope: Vec<KernelVariable>,
    values: Vec<Value>,
}
impl Dag {
    fn contract(&mut self, t: &WorkingTerm) -> Option<Value> {
        let empty = || WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        let mut pieces = Vec::new();
        let mut scalar = empty();
        scalar.coefficient = t.coefficient.clone();
        pieces.push(scalar);
        for p in &t.constraints {
            let mut x = empty();
            x.constraints.push(p.clone());
            pieces.push(x);
        }
        for (p, c) in t.phase.selectors() {
            let mut x = empty();
            x.phase.add_boolean(&p, c);
            pieces.push(x);
        }
        let mut tables = Vec::new();
        for piece in pieces {
            self.tick()?;
            let mut vars: BTreeSet<_> = piece
                .constraints
                .iter()
                .flat_map(KernelBooleanPolynomial::variables)
                .collect();
            for (p, _) in piece.phase.selectors() {
                vars.extend(p.variables());
            }
            if !scalar_conditions_within_budget(&piece.coefficient, |p| {
                vars.extend(p.variables());
                true
            }) {
                return None;
            }
            let scope: Vec<_> = vars.intersection(&t.paths).cloned().collect();
            if scope.len() > 6 {
                return None;
            }
            let mut values = Vec::new();
            for bits in 0..1usize << scope.len() {
                let mut x = piece.clone();
                for (j, v) in scope.iter().enumerate() {
                    x.substitute(v, &KernelBooleanPolynomial::from(bits >> j & 1 != 0));
                }
                values.push(self.leaf(&x)?);
            }
            tables.push(Table { scope, values });
        }
        let mut pending = t.paths.clone();
        let mut width = 0;
        while !pending.is_empty() {
            self.tick()?;
            let v = crate::ablation::choose_path(pending.iter(), |v| {
                tables
                    .iter()
                    .filter(|f| f.scope.contains(v))
                    .flat_map(|f| &f.scope)
                    .filter(|w| *w != *v)
                    .collect::<BTreeSet<_>>()
                    .len()
            })?
            .clone();
            pending.remove(&v);
            let (selected, mut rest): (Vec<_>, Vec<_>) =
                tables.into_iter().partition(|f| f.scope.contains(&v));
            let scope: Vec<_> = selected
                .iter()
                .flat_map(|f| &f.scope)
                .filter(|w| **w != v)
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            width = width.max(scope.len());
            if scope.len() > 6 {
                return None;
            }
            let mut values = Vec::new();
            for bits in 0..1usize << scope.len() {
                let mut sum = ZERO;
                for bit in [false, true] {
                    let mut product = ONE;
                    for f in &selected {
                        let mut index = 0;
                        for (j, w) in f.scope.iter().enumerate() {
                            let b = if *w == v {
                                bit
                            } else {
                                bits >> scope.binary_search(w).ok()? & 1 != 0
                            };
                            if b {
                                index |= 1 << j;
                            }
                        }
                        product = self.times(product, f.values[index])?;
                    }
                    sum = self.plus(sum, product)?;
                }
                values.push(sum);
            }
            rest.push(Table { scope, values });
            tables = rest;
        }
        let mut result = ONE;
        for t in tables {
            if !t.scope.is_empty() {
                return None;
            }
            result = self.times(result, *t.values.first()?)?;
        }
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "coefficient DAG contraction: paths={} boundary={width} nodes={}",
                t.paths.len(),
                self.nodes.len()
            );
        }
        Some(result)
    }
    fn sum(&mut self, t: WorkingTerm, depth: usize) -> Option<Value> {
        self.tick()?;
        if depth > 64 {
            return None;
        }
        let t = match reduce_working_term(t) {
            Reduction::Zero => return Some(ZERO),
            Reduction::Residual => return None,
            Reduction::Exact(t) => {
                return self.leaf(&WorkingTerm {
                    paths: BTreeSet::new(),
                    constraints: t.constraints,
                    coefficient: t.coefficient,
                    phase: t.phase,
                });
            }
            Reduction::Sum(t) => *t,
        };
        if let Some(factors) = factor_phase_sums(&t) {
            let mut value = ONE;
            for f in factors {
                let p = self.sum(f, depth + 1)?;
                value = self.times(value, p)?;
            }
            return Some(value);
        }
        if t.paths.is_empty() {
            return self.leaf(&t);
        }
        if t.paths.len() > 96 {
            return None;
        }
        let mut best = t.clone();
        let cost = |t: &WorkingTerm| (t.paths.len(), t.constraints.len(), t.phase.term_count());
        let orders = if crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
            vec![
                schedule::central_order(&t),
                t.paths.iter().cloned().collect(),
                t.paths.iter().rev().cloned().collect(),
            ]
        } else {
            vec![t.paths.iter().cloned().collect()]
        };
        for order in orders {
            let mut current = t.clone();
            for _ in 0..4 {
                self.tick()?;
                let Some(x) = schedule::normalize(&current, &order) else {
                    break;
                };
                let next = match reduce_working_term(x) {
                    Reduction::Zero => return Some(ZERO),
                    Reduction::Exact(x) => {
                        return self.leaf(&WorkingTerm {
                            paths: BTreeSet::new(),
                            constraints: x.constraints,
                            coefficient: x.coefficient,
                            phase: x.phase,
                        });
                    }
                    Reduction::Sum(x) => *x,
                    Reduction::Residual => break,
                };
                if cost(&next) >= cost(&current) {
                    break;
                }
                current = next;
            }
            if cost(&current) < cost(&best) {
                best = current;
            }
        }
        if let Some(value) = self.contract(&best) {
            return Some(value);
        }
        // Complete Shannon fallback, never sample or existentialize a path.
        let v = best.paths.first()?.clone();
        let mut value = ZERO;
        for bit in [false, true] {
            let mut child = best.clone();
            child.substitute(&v, &KernelBooleanPolynomial::from(bit));
            child.paths.remove(&v);
            let x = self.sum(child, depth + 1)?;
            value = self.plus(value, x)?;
        }
        Some(value)
    }
    fn kernel(&mut self, k: &DensityKernel) -> Option<Value> {
        // Admission of the ORIGINAL expression precedes all cancellation.
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
            self.scalar(&t.weight.ket, 0)?;
            self.scalar(&t.weight.bra, 0)?;
            for p in [&t.phase.ket, &t.phase.bra] {
                for (_, c) in p.selectors() {
                    if exponent(&c)? % (ORDER / 8) != 0 {
                        return None;
                    }
                }
            }
        }
        let mut result = ZERO;
        for t in &k.terms {
            let p = self.sum(working_term(t), 0)?;
            result = self.plus(result, p)?;
        }
        Some(result)
    }
    fn query(&self, roots: Value, k: &DensityKernel) -> Option<Query> {
        let mut live = BTreeSet::new();
        let mut pending = roots.to_vec();
        while let Some(id) = pending.pop() {
            if !live.insert(id) {
                continue;
            }
            match &self.nodes[id] {
                Node::Select(_, a, b) | Node::Add(a, b) | Node::Multiply(a, b) => {
                    pending.extend([*a, *b])
                }
                Node::Scale(_, a) => pending.push(*a),
                Node::Constant(_) => (),
            }
        }
        let mut e = Encoder::new(k)?;
        let selectors: BTreeSet<_> = live
            .iter()
            .filter_map(|id| match &self.nodes[*id] {
                Node::Select(p, _, _) => Some(p.clone()),
                _ => None,
            })
            .collect();
        let graphs: Vec<_> = selectors
            .iter()
            .map(KernelBooleanPolynomial::as_graph)
            .collect();
        let (network, variables) = crate::symbolic::BooleanPolynomial::graph_network(&graphs);
        let inputs: Vec<_> = variables
            .iter()
            .map(|v| {
                let v = KernelVariable::from_graph_variable(v);
                if v.is_bound_path() {
                    return None;
                }
                Some(format!("u{}", e.coordinates.iter().position(|w| *w == v)?))
            })
            .collect::<Option<_>>()?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "coefficient DAG live: stored={} reachable={} Boolean_nodes={}",
                self.nodes.len(),
                live.len(),
                network.nodes.len()
            );
        }
        let mut bools: Vec<String> = Vec::new();
        for &[op, a, b] in &network.nodes {
            bools.push(match op {
                0 => (a != 0).to_string(),
                1 => inputs[a as usize].clone(),
                2 | 3 => e.define(
                    "Bool",
                    format!(
                        "({} {} {})",
                        if op == 2 { "xor" } else { "and" },
                        bools[a as usize],
                        bools[b as usize]
                    ),
                )?,
                _ => return None,
            });
        }
        let boolean_names: BTreeMap<_, _> = selectors
            .into_iter()
            .zip(network.outputs.iter().map(|i| bools[*i as usize].clone()))
            .collect();
        let mut values: BTreeMap<Id, SignedRational> = BTreeMap::new();
        for id in &live {
            let value = match &self.nodes[*id] {
                Node::Constant(r) => e.rational_literal(r.numer().clone(), r.denom().clone())?,
                Node::Scale(r, a) => {
                    let c = e.rational_literal(r.numer().clone(), r.denom().clone())?;
                    e.rational_multiply(c, values[a].clone())?
                }
                Node::Multiply(a, b) => {
                    e.rational_multiply(values[a].clone(), values[b].clone())?
                }
                Node::Add(a, b) => {
                    let (a, b) = (&values[a], &values[b]);
                    if a.denominator == b.denominator {
                        let bound = &a.bound + &b.bound;
                        let width = (bound.bits() + 1).max(2).max(a.width).max(b.width);
                        if width > MAX_BITS {
                            return None;
                        }
                        let expression = e.define(
                            &format!("(_ BitVec {width})"),
                            format!("(bvadd {} {})", a.extend(width)?, b.extend(width)?),
                        )?;
                        SignedRational {
                            expression,
                            denominator: a.denominator.clone(),
                            bound,
                            width,
                        }
                    } else {
                        let mut negative = b.clone();
                        negative.expression = e.define(
                            &format!("(_ BitVec {})", negative.width),
                            format!("(bvneg {})", negative.expression),
                        )?;
                        e.rational_difference(a.clone(), negative)?
                    }
                }
                Node::Select(p, a, b) => {
                    if p.variables().iter().any(KernelVariable::is_bound_path) {
                        return None;
                    }
                    let g = &boolean_names[p];
                    let (a, b) = (&values[a], &values[b]);
                    let d = (&a.denominator / gcd(a.denominator.clone(), b.denominator.clone()))
                        * &b.denominator;
                    let ra = &d / &a.denominator;
                    let rb = &d / &b.denominator;
                    let bound = (&a.bound * &ra).max(&b.bound * &rb);
                    let width = (bound.bits() + 1).max(2).max(a.width).max(b.width);
                    if width > MAX_BITS || d.bits() > MAX_BITS {
                        return None;
                    }
                    let arm = |v: &SignedRational, r: &BigInt| -> Option<String> {
                        if v.bound == 0.into() {
                            Some(bv(&0.into(), width))
                        } else if *r == BigInt::from(1) {
                            v.extend(width)
                        } else {
                            Some(format!("(bvmul {} {})", v.extend(width)?, bv(r, width)))
                        }
                    };
                    let expression = e.define(
                        &format!("(_ BitVec {width})"),
                        format!("(ite {g} {} {})", arm(a, &ra)?, arm(b, &rb)?),
                    )?;
                    SignedRational {
                        expression,
                        denominator: d,
                        bound,
                        width,
                    }
                }
            };
            values.insert(*id, value);
        }
        let mut names: Vec<_> = (0..e.coordinates.len()).map(|i| format!("u{i}")).collect();
        let mut rs = Vec::new();
        let mut assertions = Vec::new();
        let mut denominator = BigInt::from(1);
        for (i, id) in roots.iter().enumerate() {
            let r = values[id].clone();
            denominator =
                (&denominator / gcd(denominator.clone(), r.denominator.clone())) * &r.denominator;
            if denominator.bits() > MAX_BITS {
                return None;
            }
            e.definitions.push_str(&format!(
                "(define-fun numerator{i} () (_ BitVec {}) {})\n",
                r.width, r.expression
            ));
            assertions.push(format!(
                "(distinct numerator{i} {})",
                bv(&0.into(), r.width)
            ));
            names.push(format!("numerator{i}"));
            rs.push(r);
        }
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "coefficient DAG lowering: stored={} reachable={} text_bytes={}",
                self.nodes.len(),
                live.len(),
                e.definitions.len()
            );
        }
        Some(Query {
            script: format!(
                "(set-logic QF_BV)\n(set-option :produce-models true)\n{}(assert (or {}))\n(check-sat)\n",
                e.definitions,
                assertions.join(" ")
            ),
            atoms: vec![],
            denominator,
            width: rs.iter().map(|r| r.width).max()?,
            names,
            coordinates: e.coordinates,
            group_sizes: vec![],
            rational: Some(rs),
        })
    }
}

pub(super) fn compare(left: &DensityKernel, right: &DensityKernel) -> Option<AggregateComparison> {
    if left.input_pairs != right.input_pairs
        || left.quantum_output_count != right.quantum_output_count
        || left.classical_output_count != right.classical_output_count
    {
        return None;
    }
    let mut dag = Dag::new();
    let a = dag.kernel(left)?;
    let b = dag.kernel(right)?;
    let mut difference = ZERO;
    for i in 0..4 {
        let minus = dag.scale(b[i], integer(-1))?;
        difference[i] = dag.add(a[i], minus)?;
    }
    let mode = std::env::var("IRENE_COEFFICIENT_SIMPLIFY").unwrap_or_else(|_| "auto".to_owned());
    let mut query = dag.query(difference, left);
    // Keep the original complete query on refusal or an unfavorable rewrite.
    // Compare actual lowered text and safe width, not just arithmetic DAG size:
    // a smaller arithmetic graph can hide a substantially larger Boolean XAG.
    if mode != "baseline"
        && mode != "light"
        && let Some((candidate, roots)) = dag.simplified(difference)
        && let Some(new_query) = candidate.query(roots, left)
        && query.as_ref().is_none_or(|old| {
            new_query.script.len() <= old.script.len() && new_query.width <= old.width
        })
    {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "coefficient light accepted: text_bytes={} width={}",
                new_query.script.len(),
                new_query.width
            );
        }
        query = Some(new_query);
    }
    Some(query?.solve(left))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn empty() -> DensityKernel {
        DensityKernel {
            input_pairs: vec![],
            quantum_output_count: 1,
            classical_output_count: 0,
            terms: vec![],
        }
    }
    fn evaluate(dag: &Dag, roots: Value, bit: bool) -> Vec<BigRational> {
        let mut values: Vec<BigRational> = Vec::new();
        for node in &dag.nodes {
            let value = match node {
                Node::Constant(r) => r.clone(),
                Node::Scale(r, a) => r * &values[*a],
                Node::Add(a, b) => &values[*a] + &values[*b],
                Node::Multiply(a, b) => &values[*a] * &values[*b],
                Node::Select(p, a, b) => {
                    let bval = p
                        .as_graph()
                        .evaluate::<std::convert::Infallible>(|_| Ok(bit))
                        .unwrap();
                    values[if bval { *a } else { *b }].clone()
                }
            };
            values.push(value);
        }
        roots.iter().map(|i| values[*i].clone()).collect()
    }
    #[test]
    fn ablation_retains_coefficient_backend_and_complete_sums() {
        let (_, report) = crate::ablation::run(
            crate::ablation::Config::without(crate::ablation::Group::ALL),
            contraction_matches_independent_complete_atom_sum,
        );
        assert!(
            report
                .counts(crate::ablation::Group::ExpressionSimplify)
                .skipped
                > 0
        );
        assert!(
            report
                .counts(crate::ablation::Group::PathSumPlanning)
                .skipped
                > 0
        );
    }

    #[test]
    fn ablation_disables_enhanced_coefficient_rewrites_only() {
        crate::ablation::run(
            crate::ablation::Config::without([crate::ablation::Group::ExpressionSimplify]),
            || {
                let mut dag = Dag::new();
                assert!(!dag.expression_simplify && !dag.simplify && !dag.context_enabled);
                let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
                let a = dag.select(p.clone(), 1, 0).unwrap();
                let b = dag.select(p.complement(), 1, 0).unwrap();
                let product = dag.multiply(a, b).unwrap();
                assert!(matches!(dag.nodes[product], Node::Multiply(..)));
                assert!(dag.simplified([product, 0, 0, 0]).is_none());
                for bit in [false, true] {
                    assert_eq!(evaluate(&dag, [product, 0, 0, 0], bit), vec![integer(0); 4]);
                }
            },
        );
    }

    #[test]
    fn contraction_matches_independent_complete_atom_sum() {
        let vars: Vec<_> = (0..5)
            .map(|path| {
                if path % 2 == 0 {
                    KernelVariable::PathKet { term: 0, path }
                } else {
                    KernelVariable::PathBra { term: 0, path }
                }
            })
            .collect();
        let p: Vec<_> = vars
            .iter()
            .cloned()
            .map(KernelBooleanPolynomial::variable)
            .collect();
        let qv = KernelVariable::QuantumOutputKet(0);
        let q = KernelBooleanPolynomial::variable(qv.clone());
        for seed in 0..8 {
            let mut phase = KernelPhasePolynomial::default();
            for i in 0..5 {
                phase.add_boolean(
                    &p[i].xor(&q),
                    PhaseCoefficient::rational(ratio((seed + i as i64) % 8, 8)),
                );
                if i > 0 {
                    phase.add_boolean(
                        &p[i - 1].and(&p[i]),
                        PhaseCoefficient::rational(ratio(1, 2)),
                    );
                }
            }
            let t = WorkingTerm {
                paths: vars.iter().cloned().collect(),
                constraints: vec![p[0].xor(&p[1].and(&q))],
                phase,
                coefficient: KernelScalar::Select {
                    condition: p[3].xor(&q),
                    when_true: Box::new(KernelScalar::Rational(ratio(3, 2))),
                    when_false: Box::new(KernelScalar::Rational(ratio(-1, 3))),
                },
            };
            let mut dag = Dag::new();
            let actual = dag.contract(&t).unwrap();
            for bit in [false, true] {
                let mut expected = vec![integer(0); 4];
                let mut e = Encoder::new(&empty()).unwrap();
                for bits in 0..32 {
                    let mut assigned = t.clone();
                    assigned.substitute(&qv, &KernelBooleanPolynomial::from(bit));
                    for (i, v) in vars.iter().enumerate() {
                        assigned.substitute(v, &KernelBooleanPolynomial::from(bits >> i & 1 != 0));
                    }
                    for atom in e.term(&assigned).unwrap() {
                        assert_eq!(atom.guard, "true");
                        assert!(!atom.radical);
                        let Power::Constant(power) = atom.power else {
                            panic!("constant assignment");
                        };
                        let k = (power / (ORDER / 8)) as usize;
                        expected[k % 4] += atom.weight * integer(if k >= 4 { -1 } else { 1 });
                    }
                }
                assert_eq!(
                    evaluate(&dag, actual, bit),
                    expected,
                    "seed={seed} bit={bit}"
                );
            }
        }
    }
    #[test]
    fn roots_radicals_zero_factors_and_smt_bounds_are_exact() {
        let mut dag = Dag::new();
        let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
        let scalar = KernelScalar::Sqrt(Box::new(KernelScalar::Rational(ratio(1, 2))));
        let s = dag.scalar(&scalar, 0).unwrap();
        let ss = dag.times(s, s).unwrap();
        assert_eq!(
            evaluate(&dag, ss, false),
            vec![ratio(1, 2), integer(0), integer(0), integer(0)]
        );
        let root = dag.phase(ONE, KernelBooleanPolynomial::one(), 1).unwrap();
        let mut power = ONE;
        for _ in 0..8 {
            power = dag.times(power, root).unwrap();
        }
        assert_eq!(power, ONE);
        assert_eq!(dag.times(ss, ZERO).unwrap(), ZERO);
        let a = dag.select(p.clone(), 1, 0).unwrap();
        let na = dag.select(p, 0, 1).unwrap();
        assert_eq!(dag.multiply(a, na).unwrap(), 0);
        assert_eq!(dag.multiply(a, a).unwrap(), a);
        let minus_a = dag.scale(a, integer(-1)).unwrap();
        let complement = dag.add(1, minus_a).unwrap();
        assert_eq!(evaluate(&dag, [complement, 0, 0, 0], false)[0], integer(1));
        assert_eq!(evaluate(&dag, [complement, 0, 0, 0], true)[0], integer(0));
        let negative = dag.scale(a, ratio(-3, 7)).unwrap();
        let positive = dag.scale(a, ratio(3, 7)).unwrap();
        assert_eq!(dag.add(negative, positive).unwrap(), 0);
        let q = dag.query([negative, 0, 0, 0], &empty()).unwrap();
        assert_eq!(
            run_solver(Solver::Bitwuzla, &q.script).status,
            SolverStatus::Sat
        );
        assert!(matches!(
            q.solve(&empty()),
            AggregateComparison::Different(..)
        ));
        let q = dag.query(ZERO, &empty()).unwrap();
        assert_eq!(
            run_solver(Solver::Bitwuzla, &q.script).status,
            SolverStatus::Unsat
        );
    }
    #[test]
    fn no_dead_definitions_or_unbound_paths_reach_smt() {
        let mut dag = Dag::new();
        let bound = KernelBooleanPolynomial::variable(KernelVariable::PathKet { term: 0, path: 7 });
        let dead = dag.select(bound, 1, 0).unwrap();
        assert!(dag.query([dead, 0, 0, 0], &empty()).is_none());
        let q = dag.query(ONE, &empty()).unwrap();
        assert!(!q.script.contains("(ite"));
        assert!(!q.script.contains("(_ BitVec 62)"));
        let undefined = KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(KernelScalar::Inverse(Box::new(KernelScalar::Rational(
                integer(0),
            )))),
            when_false: Box::new(KernelScalar::Rational(integer(1))),
        };
        assert!(dag.scalar(&undefined, 0).is_none());
        assert!(
            dag.scalar(
                &KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3)))),
                0
            )
            .is_none()
        );
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(1, 16)),
        );
        assert!(
            dag.leaf(&WorkingTerm {
                paths: BTreeSet::new(),
                constraints: vec![],
                coefficient: KernelScalar::Rational(integer(1)),
                phase
            })
            .is_none()
        );
    }

    #[test]
    fn complete_kernel_route_proves_eq_and_neq_and_refuses_invalid_admission() {
        use crate::equivalence::kernel::{KernelPhaseDifference, KernelWeight};
        let mut left = empty();
        left.quantum_output_count = 0;
        left.terms.push(KernelTerm {
            ket_paths: BTreeSet::from([KernelVariable::PathKet { term: 0, path: 0 }]),
            bra_paths: BTreeSet::new(),
            ket_guard: vec![],
            bra_guard: vec![],
            history_equalities: vec![],
            quantum_outputs_ket: vec![],
            quantum_outputs_bra: vec![],
            classical_outputs: vec![],
            weight: KernelWeight {
                ket: KernelScalar::Rational(integer(1)),
                bra: KernelScalar::Rational(integer(1)),
            },
            phase: KernelPhaseDifference {
                ket: KernelPhasePolynomial::default(),
                bra: KernelPhasePolynomial::default(),
            },
        });
        let mut right = left.clone();
        right.terms[0].ket_paths.clear();
        right.terms[0].weight.ket = KernelScalar::Rational(integer(2));
        assert!(matches!(
            compare(&left, &right),
            Some(AggregateComparison::SmtEquivalent(_))
        ));
        right.terms[0].weight.ket = KernelScalar::Rational(integer(1));
        assert!(matches!(
            compare(&left, &right),
            Some(AggregateComparison::Different(..))
        ));
        right.terms[0].phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(1, 16)),
        );
        right.terms[0].phase.bra = right.terms[0].phase.ket.clone();
        assert!(compare(&right, &right).is_none());
        left.terms[0]
            .quantum_outputs_ket
            .push(KernelBooleanPolynomial::zero());
        assert!(compare(&left, &left).is_none());
    }

    #[test]
    fn lowered_coefficient_dag_matches_exact_values_on_every_free_input() {
        let mut dag = Dag::new();
        let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
        let a = dag.constant(ratio(-11, 3)).unwrap();
        let b = dag.constant(ratio(7, 5)).unwrap();
        let s = dag.select(p, a, b).unwrap();
        let square = dag.multiply(s, s).unwrap();
        let sum = dag.add(square, s).unwrap();
        for bit in [false, true] {
            let x = if bit { ratio(-11, 3) } else { ratio(7, 5) };
            let expected = &x * &x + x;
            let negative = dag.constant(-expected).unwrap();
            let difference = dag.add(sum, negative).unwrap();
            let q = dag.query([difference, 0, 0, 0], &empty()).unwrap();
            let script = q.script.replace(
                "(check-sat)",
                &format!("(assert (= u0 {bit}))\n(check-sat)"),
            );
            assert_eq!(
                run_solver(Solver::Bitwuzla, &script).status,
                SolverStatus::Unsat
            );
        }
    }
}
