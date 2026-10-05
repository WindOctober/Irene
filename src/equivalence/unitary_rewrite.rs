//! Exact, shrinking circuit rewrites before symbolic execution.
//! Candidate discovery is separate from rule/commutation checks. All rewrites
//! preserve the operator exactly, including phase in controlled contexts.
use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    AstIdGenerator, Block, Gate, NumericConstant, NumericExprKind, Program, Qubit, Statement,
    StatementKind, unitary,
};
use crate::symbolic::{PhaseCoefficient, numeric_domains};
use num_rational::BigRational;

pub(super) mod dependency;
mod rules;

#[cfg(feature = "rewrite-experiments")]
mod port;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Strategy {
    /// Only adjacent gates; no commutation search.
    Adjacent,
    Scan,
    Wire,
    #[cfg(feature = "rewrite-experiments")]
    Port,
}

fn parse_strategy(value: Option<&str>) -> Result<Strategy, String> {
    match value {
        // Legacy "off" disables nonlocal search, not exact local rules.
        None | Some("adjacent") | Some("off") => Ok(Strategy::Adjacent),
        Some("scan") => Ok(Strategy::Scan),
        Some("wire") => Ok(Strategy::Wire),
        #[cfg(feature = "rewrite-experiments")]
        Some("port") => Ok(Strategy::Port),
        Some(value) => Err(format!(
            "unsupported IRENE_UNITARY_REWRITE={value:?}; port requires the rewrite-experiments feature"
        )),
    }
}

pub(super) fn strategy() -> Result<Strategy, String> {
    match std::env::var("IRENE_UNITARY_REWRITE") {
        Ok(value) => parse_strategy(Some(&value)),
        Err(std::env::VarError::NotPresent) => parse_strategy(None),
        Err(error) => Err(format!("invalid IRENE_UNITARY_REWRITE: {error}")),
    }
}

const MAX_PASSES: usize = 4;
const LOOKBACK: usize = 256;
const MAX_WORK: usize = 2_000_000;

fn rational(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

#[derive(Clone, Debug)]
struct Op {
    statement: Statement,
    gate: Gate,
    wires: Vec<Qubit>,
    /// Angle divided by its EXACT operator period: 2pi for P, 4pi for R*.
    angle: Option<PhaseCoefficient>,
}

impl Op {
    /// Exact operator identity using 2pi for P/CP and 4pi for rotations.
    /// Numeric domains must be validated before applying this predicate.
    fn is_identity(&self) -> bool {
        self.angle.as_ref().is_some_and(PhaseCoefficient::is_zero)
    }

    fn from(statement: Statement) -> Self {
        let StatementKind::Apply {
            gate,
            qubits,
            parameters,
        } = &statement.kind
        else {
            unreachable!()
        };
        let angle = match gate {
            Gate::Z => Some(PhaseCoefficient::rational(rational(1, 2))),
            Gate::S => Some(PhaseCoefficient::rational(rational(1, 4))),
            Gate::Sdg => Some(PhaseCoefficient::rational(rational(-1, 4))),
            Gate::T => Some(PhaseCoefficient::rational(rational(1, 8))),
            Gate::Tdg => Some(PhaseCoefficient::rational(rational(-1, 8))),
            Gate::P | Gate::Cp => Some(PhaseCoefficient::angle(
                parameters[0].clone(),
                rational(1, 1),
            )),
            Gate::Rx | Gate::Ry | Gate::Rz | Gate::Crx | Gate::Cry | Gate::Crz => Some(
                PhaseCoefficient::angle(parameters[0].clone(), rational(1, 2)),
            ),
            _ => None,
        };
        Self {
            gate: *gate,
            wires: qubits.clone(),
            angle,
            statement,
        }
    }
    fn family(&self) -> Gate {
        match self.gate {
            Gate::Z | Gate::S | Gate::Sdg | Gate::T | Gate::Tdg => Gate::P,
            g => g,
        }
    }
    fn diagonal(&self) -> bool {
        matches!(
            self.gate,
            Gate::Z
                | Gate::S
                | Gate::Sdg
                | Gate::T
                | Gate::Tdg
                | Gate::P
                | Gate::Cp
                | Gate::Rz
                | Gate::Crz
                | Gate::Cz
                | Gate::Ccz
        )
    }
    fn x_controls(&self) -> Option<(&[Qubit], &Qubit)> {
        if matches!(self.gate, Gate::X | Gate::Cx | Gate::Ccx) {
            let (target, controls) = self.wires.split_last()?;
            Some((controls, target))
        } else {
            None
        }
    }
}

/// Sufficient EXACT commutation only; anticommutation up to phase is rejected.
fn commutes(a: &Op, b: &Op) -> bool {
    if !a.wires.iter().any(|q| b.wires.contains(q)) {
        return true;
    }
    if a.diagonal() && b.diagonal() {
        return true;
    }
    if a.family() == b.family() && a.wires == b.wires {
        return true;
    }
    if let (Some((ac, at)), Some((bc, bt))) = (a.x_controls(), b.x_controls()) {
        return !ac.contains(bt) && !bc.contains(at);
    }
    for (d, x) in [(a, b), (b, a)] {
        if d.diagonal()
            && let Some((_, target)) = x.x_controls()
        {
            return !d.wires.contains(target);
        }
    }
    false
}

type WireIndex = BTreeMap<Qubit, Vec<usize>>;

fn predecessors(i: usize, current: &Op, index: &WireIndex, strategy: Strategy) -> Vec<usize> {
    if strategy == Strategy::Scan {
        return (i.saturating_sub(LOOKBACK)..i).rev().collect();
    }
    let mut candidates = BTreeSet::new();
    for q in &current.wires {
        if let Some(entries) = index.get(q) {
            let end = entries.partition_point(|j| *j < i);
            candidates.extend(entries[..end].iter().rev().take(LOOKBACK).copied());
        }
    }
    candidates.into_iter().rev().take(LOOKBACK).collect()
}

fn spend(work: &mut usize) -> bool {
    if *work == 0 {
        return false;
    }
    *work -= 1;
    true
}

/// Rule matching is independent of discovery and crossing validation.
fn exact_candidate(
    slots: &[Option<Op>],
    selected: &[usize],
    ids: &mut AstIdGenerator,
) -> Option<(usize, Option<Op>)> {
    if !matches!(selected.len(), 2 | 3) || !selected.windows(2).all(|w| w[0] < w[1]) {
        return None;
    }
    let ops = selected
        .iter()
        .map(|&i| slots.get(i)?.as_ref())
        .collect::<Option<Vec<_>>>()?;
    let rewrite = rules::exact(&ops, ids)?;
    Some((selected[rewrite.anchor], rewrite.operation))
}

/// Visit existing local triples before pairs can fuse away their boundaries.
/// These are only scheduling hints; the shared matcher still checks each rule.
fn preferred_candidates(slots: &[Option<Op>]) -> Vec<usize> {
    slots
        .windows(3)
        .enumerate()
        .filter_map(|(i, window)| {
            let (Some(a), Some(middle), Some(b)) = (&window[0], &window[1], &window[2]) else {
                return None;
            };
            rules::TRIPLES
                .contains(&(a.family(), middle.family(), b.family()))
                .then_some(i + 2)
        })
        .collect()
}

/// Move both endpoints towards the replacement anchor only across gates that
/// commute exactly with BOTH. Discovery supplies all possibly crossed gates;
/// disjoint wires may be omitted. This check is shared with the live DAG.
fn crossings_legal(
    slots: &[Option<Op>],
    selected: &[usize],
    crossed: impl IntoIterator<Item = usize>,
    work: &mut usize,
) -> bool {
    let (Some(a), Some(b)) = (
        slots[selected[0]].as_ref(),
        slots[*selected.last().unwrap()].as_ref(),
    ) else {
        return false;
    };
    a.wires == b.wires
        && crossed
            .into_iter()
            .filter(|i| !selected.contains(i))
            .all(|i| {
                slots[i]
                    .as_ref()
                    .is_none_or(|op| spend(work) && commutes(a, op) && commutes(b, op))
            })
}

fn apply_candidate(
    slots: &mut [Option<Op>],
    selected: &[usize],
    index: &WireIndex,
    ids: &mut AstIdGenerator,
    work: &mut usize,
) -> bool {
    let Some((kept, replacement)) = exact_candidate(slots, selected, ids) else {
        return false;
    };
    let (first, last) = (selected[0], *selected.last().unwrap());
    let mut crossed = BTreeSet::new();
    for q in &slots[first].as_ref().unwrap().wires {
        if let Some(entries) = index.get(q) {
            let start = entries.partition_point(|i| *i <= first);
            let end = entries.partition_point(|i| *i < last);
            crossed.extend(entries[start..end].iter().copied());
        }
    }
    if !crossings_legal(slots, selected, crossed, work) {
        return false;
    }
    for &i in selected {
        slots[i] = None;
    }
    slots[kept] = replacement;
    true
}

fn reduce_run(
    run: Vec<Statement>,
    strategy: Strategy,
    ids: &mut AstIdGenerator,
    work: &mut usize,
) -> Vec<Statement> {
    let mut slots: Vec<_> = run
        .into_iter()
        .map(Op::from)
        .filter(|op| !op.is_identity())
        .map(Some)
        .collect();
    for _ in 0..MAX_PASSES {
        let mut index = WireIndex::new();
        for (i, op) in slots.iter().enumerate() {
            if let Some(op) = op {
                for q in &op.wires {
                    index.entry(q.clone()).or_default().push(i);
                }
            }
        }
        let mut changed = false;
        #[cfg(feature = "rewrite-experiments")]
        if strategy == Strategy::Port {
            for selected in port::candidates(&slots) {
                if !spend(work) {
                    break;
                }
                changed |= apply_candidate(&mut slots, &selected, &index, ids, work);
            }
        } else {
            changed |= sweep(&mut slots, &index, strategy, ids, work);
        }
        #[cfg(not(feature = "rewrite-experiments"))]
        {
            changed |= sweep(&mut slots, &index, strategy, ids, work);
        }
        if !changed || *work == 0 {
            break;
        }
        slots.retain(Option::is_some);
    }
    slots.into_iter().flatten().map(|op| op.statement).collect()
}

fn sweep(
    slots: &mut [Option<Op>],
    index: &WireIndex,
    strategy: Strategy,
    ids: &mut AstIdGenerator,
    work: &mut usize,
) -> bool {
    let mut changed = false;
    // Track live positions so adjacent search never crosses a live intervening
    // operation and does not repeatedly walk long runs of deleted slots.
    let mut live: BTreeSet<_> = slots
        .iter()
        .enumerate()
        .filter_map(|(i, op)| op.as_ref().map(|_| i))
        .collect();
    let preferred = preferred_candidates(slots);
    for i in preferred.into_iter().chain(0..slots.len()) {
        let Some(current) = slots[i].as_ref() else {
            continue;
        };
        let previous = if strategy == Strategy::Adjacent {
            live.range(..i).rev().take(2).copied().collect()
        } else {
            predecessors(i, current, index, strategy)
        };
        let mut middle = None;
        for j in previous {
            if !spend(work) {
                return changed;
            }
            let (Some(a), Some(b)) = (&slots[j], &slots[i]) else {
                continue;
            };
            let selected = if let Some(k) = middle {
                vec![j, k, i]
            } else {
                vec![j, i]
            };
            let crossing = commutes(a, b);
            if apply_candidate(slots, &selected, index, ids, work) {
                for &k in &selected {
                    if slots[k].is_none() {
                        live.remove(&k);
                    }
                }
                changed = true;
                break;
            }
            if strategy == Strategy::Adjacent || !crossing {
                if middle.is_some() {
                    break;
                }
                middle = Some(j);
                if slots[i].as_ref().is_none_or(|o| !rules::can_end_triple(o)) {
                    break;
                }
            }
        }
    }
    changed
}

fn reduce_block(block: &mut Block, strategy: Strategy, ids: &mut AstIdGenerator, work: &mut usize) {
    let mut out = vec![];
    let mut run = vec![];
    for mut statement in std::mem::take(&mut block.statements) {
        if matches!(statement.kind, StatementKind::Apply { .. }) {
            run.push(statement);
            continue;
        }
        out.extend(reduce_run(std::mem::take(&mut run), strategy, ids, work));
        if let StatementKind::Scope(inner) = &mut statement.kind {
            reduce_block(inner, strategy, ids, work);
        }
        out.push(statement);
    }
    out.extend(reduce_run(run, strategy, ids, work));
    block.statements = out;
}

/// May optimize one side independently: keeps declarations, classical writes,
/// scopes, full operator phase, and the caller's input/output interface.
pub(super) fn preprocess(source: &Program) -> Option<Program> {
    // analyze validates configuration before any optional proof route.
    preprocess_with(source, strategy().ok()?)
}

pub(super) fn preprocess_with(source: &Program, strategy: Strategy) -> Option<Program> {
    let start = std::time::Instant::now();
    if unitary::validate(source).is_err() || numeric_domains(source).is_err() {
        return None;
    }
    let mut candidate = source.clone();
    let mut ids = AstIdGenerator::starting_at(source.ast_id_bound());
    let mut work = MAX_WORK;
    reduce_block(&mut candidate.body, strategy, &mut ids, &mut work);
    let before = source.operation_count();
    let after = candidate.operation_count();
    if std::env::var_os("IRENE_REWRITE_STATS").is_some() {
        eprintln!(
            "unitary_rewrite strategy={strategy:?} gates={before}->{after} work={} elapsed_us={}",
            MAX_WORK - work,
            start.elapsed().as_micros()
        );
    }
    (after < before).then_some(candidate)
}

#[cfg(test)]
pub(super) mod tests;
