//! Read-only, opt-in snapshots of the live Boolean expressions in HPS checkpoints.
//! ANF expansion is deliberately an OFFLINE operation (see scripts/representation_stats.py).
//! Byte counts describe the packed snapshot buffers, NOT Rust Arc/BTreeSet heap usage or RSS.
use super::*;
use crate::symbolic::{Component, Scalar};
use std::cell::RefCell;
use std::fs::OpenOptions;
use std::os::unix::fs::FileTypeExt;
use std::io::{self, BufWriter, Write};
use std::marker::PhantomData;
use std::path::Path;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Config {
    /// Sample every N statement/summary checkpoints; final HPS checkpoints are always sampled.
    pub every: usize,
    pub max_nodes: usize,
    pub max_edges: usize,
    pub max_roots: usize,
    pub max_snapshots: usize,
    pub max_file_bytes: usize,
}
impl Default for Config {
    fn default() -> Self {
        Self {
            every: 32,
            max_nodes: 100_000,
            max_edges: 500_000,
            max_roots: 100_000,
            max_snapshots: 10_000,
            max_file_bytes: 256 * 1024 * 1024,
        }
    }
}

/// Nodes are [kind, a, b]: constant, input(register,index), path(index), XOR, AND.
/// XOR/AND use a start/length pair into edges. Children precede their parents.
#[derive(Debug)]
pub struct Snapshot {
    pub nodes: Vec<[u64; 3]>,
    pub edges: Vec<u64>,
    pub roots: Vec<u64>,
}
impl Snapshot {
    pub fn packed_bytes(&self) -> usize {
        self.nodes.len() * 24 + (self.edges.len() + self.roots.len()) * 8
    }
    /// Actual requested buffer capacity of THIS snapshot. Excludes Vec headers,
    /// allocator metadata, traversal workspace and the original symbolic graph.
    pub fn buffer_bytes(&self) -> usize {
        self.nodes.capacity() * 24 + (self.edges.capacity() + self.roots.capacity()) * 8
    }
    pub fn capture(roots: &[BooleanPolynomial], config: &Config) -> Result<Self, &'static str> {
        if roots.len() > config.max_roots {
            return Err("root_limit");
        }
        let mut result = Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            roots: Vec::new(),
        };
        let mut ids = HashMap::new();
        // Pointer identity counts actual sharing, not merely equivalent expressions.
        for root in roots {
            let mut pending = vec![(root, false)];
            while let Some((p, ready)) = pending.pop() {
                if ids.contains_key(&p.key()) {
                    continue;
                }
                if !ready {
                    if ids.len() + pending.len() >= config.max_nodes + config.max_edges {
                        return Err("traversal_limit");
                    }
                    pending.push((p, true));
                    if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                        if xs.len() > config.max_edges {
                            return Err("edge_limit");
                        }
                        pending.extend(xs.iter().rev().map(|x| (x, false)));
                    }
                    continue;
                }
                if result.nodes.len() >= config.max_nodes {
                    return Err("node_limit");
                }
                let row = match p.expression() {
                    Expression::Constant(v) => [0, u64::from(*v), 0],
                    Expression::Variable(Variable::Input(q)) => {
                        [1, q.register.0 as u64, q.index as u64]
                    }
                    Expression::Variable(Variable::Path(y)) => [2, *y as u64, 0],
                    Expression::Xor(xs) | Expression::And(xs) => {
                        if result.edges.len() + xs.len() > config.max_edges {
                            return Err("edge_limit");
                        }
                        let start = result.edges.len();
                        result.edges.extend(xs.iter().map(|p| ids[&p.key()]));
                        [
                            if matches!(p.expression(), Expression::Xor(_)) {
                                3
                            } else {
                                4
                            },
                            start as u64,
                            xs.len() as u64,
                        ]
                    }
                };
                ids.insert(p.key(), result.nodes.len() as u64);
                result.nodes.push(row);
            }
            result.roots.push(ids[&root.key()]);
        }
        Ok(result)
    }
}

struct Recorder {
    writer: BufWriter<std::fs::File>,
    config: Config,
    seen: usize,
    sampled: usize,
    written: usize,
    skipped: usize,
    bytes: usize,
    error: Option<io::Error>,
}
thread_local! { static ACTIVE: RefCell<Option<Recorder>> = const { RefCell::new(None) }; }

/// Synchronous, thread-local observation scope. Does not propagate into worker threads.
/// Existing destinations are never overwritten. Explicit finish marks a complete trace;
/// a killed process or dropped session has no completion footer.
pub struct Session {
    finished: bool,
    _thread_bound: PhantomData<Rc<()>>,
}
impl Session {
    pub fn start(path: impl AsRef<Path>, mut config: Config) -> io::Result<Self> {
        // Opt-in full capture. Host/process limits belong to the experiment
        // runner; no checkpoint or output-size truncation occurs in this mode.
        if std::env::var("IRENE_REPRESENTATION_STATS_UNCAPPED").as_deref() == Ok("1") {
            let limit = usize::MAX / 4;
            config.max_nodes = limit;
            config.max_edges = limit;
            config.max_roots = limit;
            config.max_snapshots = limit;
            config.max_file_bytes = limit;
        }
        if config.every == 0 || config.max_nodes == 0 || config.max_file_bytes < 1024 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid statistics budget",
            ));
        }
        ACTIVE.with(|active| {
            if active.borrow().is_some() {
                return Err(io::Error::new(io::ErrorKind::AlreadyExists, "statistics session already active"));
            }
            // An explicitly supplied FIFO allows streaming compression. Existing
            // regular files are still never overwritten, including in FIFO mode.
            let file = if std::env::var("IRENE_REPRESENTATION_STATS_FIFO").as_deref() == Ok("1") {
                if !std::fs::symlink_metadata(path.as_ref())?.file_type().is_fifo() {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "statistics destination is not a FIFO"));
                }
                OpenOptions::new().write(true).open(path)?
            } else {
                OpenOptions::new().write(true).create_new(true).open(path)?
            };
            let mut writer = BufWriter::new(file);
            writeln!(writer, "{{\"type\":\"header\",\"schema_version\":1,\"scope\":\"hps_checkpoint_boolean_roots\",\"every\":{},\"storage\":\"packed_u64_snapshot_not_source_heap_or_rss\"}}", config.every)?;
            *active.borrow_mut() = Some(Recorder { writer, config, seen: 0, sampled: 0,
                written: 0, skipped: 0, bytes: 256, error: None });
            Ok(Self { finished: false, _thread_bound: PhantomData })
        })
    }
    pub fn finish(mut self) -> io::Result<()> {
        self.finished = true;
        ACTIVE.with(|active| {
            let mut r = active.borrow_mut().take().expect("active statistics session");
            if let Some(e) = r.error { return Err(e); }
            writeln!(r.writer, "{{\"type\":\"end\",\"checkpoints_seen\":{},\"checkpoints_sampled\":{},\"snapshots\":{},\"skipped\":{}}}", r.seen, r.sampled, r.written, r.skipped)?;
            r.writer.flush()
        })
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        if !self.finished {
            ACTIVE.with(|active| {
                active.borrow_mut().take();
            });
        }
    }
}

/// Existing experiment workers may opt in without changing their verifier call
/// or benchmark interface. Explicit Session scopes take precedence over the env.
pub(crate) fn run_if_requested<T>(operation: impl FnOnce() -> T) -> T {
    if ACTIVE.with(|active| active.borrow().is_some()) {
        return operation();
    }
    let Some(path) = std::env::var_os("IRENE_REPRESENTATION_STATS") else {
        return operation();
    };
    let every = match std::env::var("IRENE_REPRESENTATION_STATS_EVERY") {
        Ok(value) => match value.parse::<usize>() {
            Ok(value) if value > 0 => value,
            _ => {
                eprintln!(
                    "representation statistics disabled: invalid IRENE_REPRESENTATION_STATS_EVERY"
                );
                return operation();
            }
        },
        Err(std::env::VarError::NotPresent) => Config::default().every,
        Err(_) => {
            eprintln!("representation statistics disabled: non-Unicode sampling interval");
            return operation();
        }
    };
    let session = match Session::start(
        path,
        Config {
            every,
            ..Config::default()
        },
    ) {
        Ok(session) => session,
        Err(error) => {
            eprintln!("representation statistics disabled: {error}");
            return operation();
        }
    };
    let result = operation();
    if let Err(error) = session.finish() {
        eprintln!("representation statistics incomplete: {error}");
    }
    result
}

fn scalar_roots(scalar: &Scalar, roots: &mut Vec<BooleanPolynomial>, limit: usize) -> bool {
    let mut todo = vec![scalar];
    let mut work = 0;
    while let Some(s) = todo.pop() {
        work += 1;
        if work > limit || roots.len() >= limit {
            return false;
        }
        match s {
            Scalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                roots.push(condition.clone());
                todo.extend([when_true.as_ref(), when_false.as_ref()]);
            }
            Scalar::Add(a, b) | Scalar::Mul(a, b) => todo.extend([a.as_ref(), b.as_ref()]),
            Scalar::Sqrt(a) | Scalar::Neg(a) | Scalar::Inverse(a) => todo.push(a),
            _ => (),
        }
    }
    true
}

/// Observation only: no factored()/normalize()/ANF calls and no changes to components.
pub(crate) fn observe(stage: &'static str, components: &[Component], force: bool) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(r) = active.as_mut() else { return; };
        if r.error.is_some() { return; }
        r.seen += 1;
        if !force && (r.seen - 1) % r.config.every != 0 { return; }
        r.sampled += 1;
        if r.written >= r.config.max_snapshots || r.bytes >= r.config.max_file_bytes {
            r.skipped += 1; return;
        }
        let mut roots = Vec::new();
        let mut complete = true;
        for c in components {
            // Avoid an unbounded root list even when the observed state is large.
            for p in c.guard.iter().chain(c.output.quantum.values()).chain(c.output.classical.values())
                .chain(c.output.history.iter().map(|h| h.value())) {
                if roots.len() >= r.config.max_roots { complete = false; break; }
                roots.push(p.clone());
            }
            if !complete { break; }
            for (p, _) in c.phase.selectors() {
                if roots.len() >= r.config.max_roots { complete = false; break; }
                roots.push(p);
            }
            if !complete || !scalar_roots(&c.scalar, &mut roots, r.config.max_roots) { complete = false; break; }
        }
        let snapshot = if complete { Snapshot::capture(&roots, &r.config) } else { Err("root_limit") };
        let line = match snapshot {
            Ok(s) => format!("{{\"type\":\"snapshot\",\"checkpoint\":{},\"stage\":\"{}\",\"xag_nodes\":{},\"xag_edges\":{},\"xag_packed_bytes\":{},\"xag_buffer_bytes\":{},\"nodes\":{:?},\"edges\":{:?},\"roots\":{:?}}}\n", r.seen, stage, s.nodes.len(), s.edges.len(), s.packed_bytes(), s.buffer_bytes(), s.nodes, s.edges, s.roots),
            Err(reason) => {
                r.skipped += 1;
                let line = format!("{{\"type\":\"skipped\",\"checkpoint\":{},\"reason\":\"{}\"}}\n", r.seen, reason);
                if let Err(e) = r.writer.write_all(line.as_bytes()) { r.error = Some(e); }
                r.bytes += line.len(); return;
            }
        };
        if r.bytes + line.len() > r.config.max_file_bytes { r.skipped += 1; return; }
        if let Err(e) = r.writer.write_all(line.as_bytes()) { r.error = Some(e); return; }
        r.bytes += line.len(); r.written += 1;
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn counts_shared_roots_once_and_edges_separately() {
        let a = BooleanPolynomial::variable(Variable::Path(0));
        let b = BooleanPolynomial::variable(Variable::Path(1));
        let f = a.xor(&b);
        let s = Snapshot::capture(&[f.clone(), f], &Config::default()).unwrap();
        assert_eq!(s.nodes.len(), 3);
        assert_eq!(s.edges.len(), 2);
        assert_eq!(s.roots, vec![2, 2]);
        assert_eq!(s.packed_bytes(), 104);
        assert!(s.buffer_bytes() >= s.packed_bytes());
    }
    #[test]
    fn limited_snapshot_is_not_a_partial_graph() {
        let a = BooleanPolynomial::variable(Variable::Path(0));
        let b = BooleanPolynomial::variable(Variable::Path(1));
        assert_eq!(
            Snapshot::capture(
                &[a.xor(&b)],
                &Config {
                    max_nodes: 1,
                    ..Config::default()
                }
            )
            .unwrap_err(),
            "node_limit"
        );
    }
}
