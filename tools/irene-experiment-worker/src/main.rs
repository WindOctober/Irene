use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::Path;

use irene::equivalence::{
    Analysis, Counterexample, DensityCounterexample, Endpoint, EquivalenceConfig, InputPair,
    NumericInputPair, OutputPair, PortfolioConsensus, PortfolioResult, Solver, SolverResult,
    SolverStatus, Verdict, analyze,
};
use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{ClassicalBit, Program, Qubit};
use irene::utils::load_openqasm_source;
use serde::Deserialize;
use serde_json::{Value, json};

const MAX_SOLVER_STREAM_BYTES: usize = 16 * 1024;

#[derive(Deserialize)]
struct Case {
    left_abs: String,
    right_abs: String,
    #[serde(default)]
    input_pairs: Vec<String>,
    #[serde(default)]
    numeric_input_pairs: Vec<String>,
    #[serde(default)]
    output_pairs: Vec<String>,
}

fn main() {
    let started = std::time::Instant::now();
    // One observation scope covers preprocessing, exact analysis and numerical
    // follow-up alike. It does not change any of those verification routes.
    let statistics = env::var_os("IRENE_REPRESENTATION_STATS").and_then(|path| {
        let every = env::var("IRENE_REPRESENTATION_STATS_EVERY")
            .ok().and_then(|v| v.parse().ok()).unwrap_or(32);
        match irene::symbolic::representation_stats::Session::start(path,
            irene::symbolic::representation_stats::Config { every, ..Default::default() }) {
            Ok(session) => Some(session),
            Err(error) => { eprintln!("representation statistics disabled: {error}"); None }
        }
    });
    let mut ablation_report = None;
    let result = irene::ablation::Config::from_env().and_then(|config| {
        let (result, report) = irene::ablation::run(config, || {
            env::args()
                .nth(1)
                .ok_or_else(|| "expected a normalized case JSON path".to_owned())
                .and_then(run_case)
        });
        ablation_report = Some(report);
        result
    });
    let mut payload = match result {
        Ok(result) => result,
        Err(message) => json!({
            "results": [{
                "variant": "symbolic",
                "status": "error",
                "verdict": null,
                "message": message,
            }]
        }),
    };
    // Include input loading, parsing, symbolic execution, analysis and result
    // construction. Process startup and final stdout transport are excluded;
    // the benchmark runner records process-level wall time separately.
    let elapsed = started.elapsed().as_secs_f64();
    if let Some(results) = payload.get_mut("results").and_then(Value::as_array_mut) {
        for result in results {
            result["tool_time_sec"] = json!(elapsed);
            if let Some(report) = &ablation_report {
                result["ablation"] = json!({
                    // Matches the schema-2 ablation reports of the recorded campaigns.
                    "schema_version": 2,
                    "disabled": report.config.disabled().iter().map(|g| g.name()).collect::<Vec<_>>(),
                    "groups": irene::ablation::Group::ALL.into_iter().map(|g| {
                        let c = report.counts(g);
                        (g.name(), json!({"enabled":report.config.enabled(g),"admitted":c.admitted,"skipped":c.skipped}))
                    }).collect::<BTreeMap<_,_>>()
                });
            }
        }
    }
    if let Some(session) = statistics {
        if let Err(error) = session.finish() {
            eprintln!("representation statistics incomplete: {error}");
        }
    }
    println!("RESULT_JSON={payload}");
}

fn run_case(case_file: String) -> Result<Value, String> {
    let case: Case =
        serde_json::from_str(&fs::read_to_string(&case_file).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let left = parse_program(Path::new(&case.left_abs))?;
    let right = parse_program(Path::new(&case.right_abs))?;
    if env::var_os("IRENE_INSPECT_UNITARY").is_some() {
        return Ok(json!({
            "left_unitary": irene::ir::unitary::validate(&left).is_ok(),
            "right_unitary": irene::ir::unitary::validate(&right).is_ok(),
            "left_gates": left.operation_count(),
            "right_gates": right.operation_count(),
        }));
    }
    let config = EquivalenceConfig {
        input_pairs: case
            .input_pairs
            .iter()
            .map(|pair| {
                let (left_spec, right_spec) = pair_sides(pair)?;
                Ok(InputPair {
                    left: resolve_endpoint(&left, left_spec)?,
                    right: resolve_endpoint(&right, right_spec)?,
                })
            })
            .collect::<Result<_, String>>()?,
        numeric_input_pairs: case
            .numeric_input_pairs
            .iter()
            .map(|pair| {
                let (left_name, right_name) = pair
                    .split_once('=')
                    .ok_or_else(|| format!("invalid numeric input pair: {pair}"))?;
                let left_id = left
                    .numeric_inputs
                    .iter()
                    .find(|input| input.name == left_name)
                    .map(|input| input.id)
                    .ok_or_else(|| format!("unknown left numeric input: {left_name}"))?;
                let right_id = right
                    .numeric_inputs
                    .iter()
                    .find(|input| input.name == right_name)
                    .map(|input| input.id)
                    .ok_or_else(|| format!("unknown right numeric input: {right_name}"))?;
                Ok(NumericInputPair {
                    left: left_id,
                    right: right_id,
                })
            })
            .collect::<Result<_, String>>()?,
        output_pairs: case
            .output_pairs
            .iter()
            .map(|pair| {
                let (left_spec, right_spec) = pair_sides(pair)?;
                Ok(OutputPair {
                    left: resolve_endpoint(&left, left_spec)?,
                    right: resolve_endpoint(&right, right_spec)?,
                })
            })
            .collect::<Result<_, String>>()?,
    };
    let mut metadata = json!(null);
    let mode = env::var("IRENE_DAG_MODE").unwrap_or_else(|_| "dag_interval".into());
    if mode != "off" {
        use irene::equivalence::dependency_miter::{self as dag, Mode, Options};
        let chosen = match mode.as_str() {
            "wire" => Mode::Wire,
            "dag" | "dag_interval" => Mode::Dag,
            "dag_schedule" => Mode::DagScheduled,
            _ => return Err(format!("invalid IRENE_DAG_MODE={mode}")),
        };
        let order = env::var("IRENE_DAG_ORDER")
            .unwrap_or_else(|_| (1u64 << 62).to_string())
            .parse::<u64>()
            .map_err(|e| e.to_string())?;
        if !order.is_power_of_two() || order < 8 {
            return Err("invalid exact phase order".into());
        }
        let options = Options {
            mode: chosen,
            exact_order: order,
            diamond_tolerance: (mode == "dag_interval")
                .then(|| num_rational::BigRational::new(1.into(), 1_000_000_000_000i64.into())),
        };
        if let Some(c) = dag::candidate(&left, &right, &config, &options) {
            let s = &c.statistics;
            metadata = json!({"mode":mode,"gates_before":s.before,"gates_after":s.after,
                "removed_h":s.removed_h,"exact_rewrites":s.exact_rewrites,
                "exact_identity_gates":s.exact_identity_gates,
                "approximate_pairs":s.approximate_pairs,"approximate_blocks":s.approximate_blocks,
                "approximate_single_gates":s.approximate_single_gates,
                "eligible_angles":s.eligible_angles,
                "error_bound":s.diamond_error.to_string(),"preprocess_us":s.elapsed_us,
                "work":s.work,"exact_order":order});
            if env::var_os("IRENE_DAG_INSPECT").is_some() {
                return Ok(json!({"dependency_miter":metadata,
                    "empty":c.circuit.body.statements.is_empty(),"exact":c.is_exact()}));
            }
            metadata["execution_route"] = json!("reduced_miter_only");
            if c.circuit.body.statements.is_empty() {
                return Ok(
                    json!({"results":[{"variant":"symbolic","status":"completed",
                    "verdict":if c.is_exact(){"eq"}else{"approx_eq"},
                    "exact_verdict":if c.is_exact(){"eq"}else{"unknown"},
                    "native_result":if c.is_exact(){"DependencyMiterExact"}else{"DependencyMiterDiamondBound"},
                    "tolerance_metric":"channel_diamond_distance",
                    "diamond_tolerance":"1/1000000000000",
                    "dependency_miter":metadata,"solver_queries":[],"kernel_terms":[0,0]}]}),
                );
            }
            // The admitted, simplified miter IS the analysis input. Its HPS/
            // kernel pipeline has the outer case limit, not a 30-second child
            // limit; an inconclusive result does not restart the original pair.
            let reduced_config = EquivalenceConfig::positional(&c.circuit, &c.identity)
                .ok_or_else(|| "invalid reduced miter interface".to_owned())?;
            let start = std::time::Instant::now();
            let analysis =
                analyze(&c.circuit, &c.identity, &reduced_config).map_err(|e| e.to_string())?;
            metadata["analysis_seconds"] = json!(start.elapsed().as_secs_f64());
            let mut result = serialize_reduced_analysis(&analysis, c.is_exact());
            if analysis.verdict == Verdict::Unknown
                && env::var("IRENE_HPS_INTERVAL").as_deref() != Ok("0")
            {
                let start = std::time::Instant::now();
                let numerical = irene::equivalence::interval_hps::identity_bound(&c.circuit);
                let total = numerical.bound.as_ref().map(|b| b + &s.diamond_error);
                let lower = numerical.corrected_lower_bound(&s.diamond_error);
                let proves_neq = lower
                    .as_ref()
                    .is_some_and(|b| b > &num_rational::BigRational::from_integer(0.into()));
                let tolerance =
                    num_rational::BigRational::new(1.into(), 1_000_000_000_000i64.into());
                metadata["interval_hps"] = json!({"reason":numerical.reason,
                    "residual_lower_bound":numerical.lower_bound.as_ref().map(ToString::to_string),
                    "total_lower_bound":lower.as_ref().map(ToString::to_string),
                    "residual_bound":numerical.bound.as_ref().map(ToString::to_string),
                    "total_bound":total.as_ref().map(ToString::to_string),
                    "paths":numerical.paths,"work":numerical.work,"nodes":numerical.nodes,
                    "max_width":numerical.max_width,"seconds":start.elapsed().as_secs_f64()});
                if total.as_ref().is_some_and(|b| b <= &tolerance) {
                    let row = &mut result["results"][0];
                    row["verdict"] = json!("approx_eq");
                    // Exact non-equality can coexist with tolerance equivalence.
                    row["exact_verdict"] = json!(if proves_neq { "neq" } else { "unknown" });
                    row["native_result"] = json!("HpsIntervalDiamondBound");
                    row["tolerance_metric"] = json!("channel_diamond_distance");
                    row["diamond_tolerance"] = json!(tolerance.to_string());
                } else if proves_neq {
                    let row = &mut result["results"][0];
                    row["verdict"] = json!("neq");
                    row["exact_verdict"] = json!("neq");
                    row["native_result"] = json!("HpsIntervalDiamondLowerBound");
                    row["tolerance_metric"] = json!("channel_diamond_distance");
                    row["diamond_tolerance"] = json!(tolerance.to_string());
                }
                result["results"][0]["certified_nonzero_distance"] = json!(proves_neq);
                result["results"][0]["certified_exceeds_tolerance"] =
                    json!(lower.as_ref().is_some_and(|b| b > &tolerance));
            }
            result["results"][0]["dependency_miter"] = metadata;
            return Ok(result);
        }
    }
    if env::var_os("IRENE_DAG_INSPECT").is_some() {
        return Ok(json!({"dependency_miter":metadata}));
    }
    let analysis = analyze(&left, &right, &config).map_err(|e| e.to_string())?;
    let mut result = serialize_analysis(&analysis);
    result["results"][0]["dependency_miter"] = metadata;
    Ok(result)
}

fn serialize_reduced_analysis(analysis: &Analysis, exact: bool) -> Value {
    let mut result = serialize_analysis(analysis);
    let row = &mut result["results"][0];
    // Witness coordinates belong to miter vs identity, not the original pair.
    row["miter_counterexample"] = row["counterexample"].take();
    row["miter_density_counterexample"] = row["density_counterexample"].take();
    row["residual_verdict"] = row["verdict"].clone();
    row["exact_verdict"] = if exact {
        row["verdict"].clone()
    } else {
        json!("unknown")
    };
    if !exact {
        row["verdict"] = json!(if analysis.verdict == Verdict::Equivalent {
            "approx_eq"
        } else {
            "unknown"
        });
        row["tolerance_metric"] = json!("channel_diamond_distance");
        row["diamond_tolerance"] = json!("1/1000000000000");
    }
    result
}

fn serialize_analysis(analysis: &Analysis) -> Value {
    let verdict = match analysis.verdict {
        Verdict::Equivalent => "eq",
        Verdict::NotEquivalent => "neq",
        Verdict::Unknown => "unknown",
    };
    json!({
        "results": [{
            "variant": "symbolic",
            "status": "completed",
            "verdict": verdict,
            "native_result": format!("{:?}", analysis.evidence),
            "counterexample": analysis.counterexample.as_ref().map(serialize_counterexample),
            "density_counterexample": analysis.density_counterexample.as_ref().map(serialize_density_counterexample),
            "kernel_terms": [analysis.kernel_terms.0, analysis.kernel_terms.1],
            "solver_queries": analysis.solver_queries.iter().map(serialize_solver_query).collect::<Vec<_>>(),
        }]
    })
}

fn serialize_counterexample(counterexample: &Counterexample) -> Value {
    json!({
        "ket_inputs": counterexample.ket_inputs,
        "bra_inputs": counterexample.bra_inputs,
    })
}

fn serialize_density_counterexample(witness: &DensityCounterexample) -> Value {
    let mut value = json!({
        "ket_inputs": witness.ket_inputs,
        "bra_inputs": witness.bra_inputs,
        "ket_outputs": witness.ket_outputs,
        "bra_outputs": witness.bra_outputs,
        "classical_outputs": witness.classical_outputs,
        "root_of_unity_order": witness.root_of_unity_order.to_string(),
        "difference_coefficients": witness.difference_coefficients.iter().map(|(power, coefficient)| {
            json!({"power": power.to_string(), "coefficient": coefficient.to_string()})
        }).collect::<Vec<_>>(),
    });
    if !witness.exact_factors.is_empty() {
        value["certificate_kind"] = json!("cyclotomic_exact_product_v1");
        value["exact_factors"] = json!(witness.exact_factors.iter().map(|f| json!({
            "coefficients": f.coefficients.iter().map(|(power,c)| json!({"power":power.to_string(),"coefficient":c.to_string()})).collect::<Vec<_>>(),
            "sqrt_three_coefficients": f.sqrt_three_coefficients.iter().map(|(power,c)| json!({"power":power.to_string(),"coefficient":c.to_string()})).collect::<Vec<_>>(),
        })).collect::<Vec<_>>());
    }
    if !witness.sqrt_three_coefficients.is_empty() {
        if witness.exact_factors.is_empty() {
            value["certificate_kind"] = json!("cyclotomic_sqrt_three_exact_v1");
        }
        value["sqrt_three_coefficients"] = json!(
            witness
                .sqrt_three_coefficients
                .iter()
                .map(|(power, coefficient)| {
                    json!({"power": power.to_string(), "coefficient": coefficient.to_string()})
                })
                .collect::<Vec<_>>()
        );
    }
    value
}

fn serialize_solver_query(query: &PortfolioResult) -> Value {
    json!({
        "consensus": consensus_name(query.consensus),
        "solvers": query.results.iter().map(serialize_solver_result).collect::<Vec<_>>(),
    })
}

fn serialize_solver_result(result: &SolverResult) -> Value {
    let (stdout, stdout_truncated) = bounded_stream(&result.stdout);
    let (stderr, stderr_truncated) = bounded_stream(&result.stderr);
    let model = (result.status == SolverStatus::Sat)
        .then(|| extract_boolean_model(&result.stdout))
        .flatten();
    json!({
        "solver": solver_name(result.solver),
        "status": solver_status_name(result.status),
        "duration_sec": result.duration.as_secs_f64(),
        "stdout": stdout,
        "stdout_bytes": result.stdout.len(),
        "stdout_truncated": stdout_truncated,
        "stderr": stderr,
        "stderr_bytes": result.stderr.len(),
        "stderr_truncated": stderr_truncated,
        "model": model,
    })
}

fn consensus_name(consensus: PortfolioConsensus) -> &'static str {
    match consensus {
        PortfolioConsensus::Sat => "Sat",
        PortfolioConsensus::Unsat => "Unsat",
        PortfolioConsensus::Inconclusive => "Inconclusive",
    }
}

fn solver_name(solver: Solver) -> &'static str {
    match solver {
        Solver::Z3 => "Z3",
        Solver::Cvc5 => "Cvc5",
        Solver::Bitwuzla => "Bitwuzla",
    }
}

fn solver_status_name(status: SolverStatus) -> &'static str {
    match status {
        SolverStatus::Sat => "Sat",
        SolverStatus::Unsat => "Unsat",
        SolverStatus::Unknown => "Unknown",
        SolverStatus::Timeout => "Timeout",
        SolverStatus::Unavailable => "Unavailable",
        SolverStatus::Error => "Error",
    }
}

fn bounded_stream(stream: &str) -> (&str, bool) {
    if stream.len() <= MAX_SOLVER_STREAM_BYTES {
        return (stream, false);
    }
    let mut end = MAX_SOLVER_STREAM_BYTES;
    while !stream.is_char_boundary(end) {
        end -= 1;
    }
    (&stream[..end], true)
}

/// Extracts Irene's canonical `x0..xN`/`z0..zN` Boolean `get-value` reply.
///
/// The solver stream itself is bounded in persisted results. Keeping this
/// compact exact model separately ensures that each SAT solver's witness can
/// still be replayed even when its raw output exceeded that bound.
fn extract_boolean_model(stdout: &str) -> Option<Value> {
    let tokens = stdout
        .replace(['(', ')'], " ")
        .split_whitespace()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let mut ket = BTreeMap::new();
    let mut bra = BTreeMap::new();
    for pair in tokens.windows(2) {
        let value = match pair[1].as_str() {
            "true" => true,
            "false" => false,
            _ => continue,
        };
        let Some((namespace, index)) = parse_model_name(&pair[0]) else {
            continue;
        };
        match namespace {
            'x' => {
                ket.insert(index, value);
            }
            'z' => {
                bra.insert(index, value);
            }
            _ => unreachable!("parse_model_name accepts only x and z"),
        }
    }

    let ket_inputs = dense_boolean_values(ket)?;
    if ket_inputs.is_empty() {
        return None;
    }
    let bra_inputs = if bra.is_empty() {
        None
    } else {
        Some(dense_boolean_values(bra)?)
    };
    Some(json!({
        "ket_inputs": ket_inputs,
        "bra_inputs": bra_inputs,
    }))
}

fn parse_model_name(name: &str) -> Option<(char, usize)> {
    let mut characters = name.chars();
    let namespace = characters.next()?;
    if !matches!(namespace, 'x' | 'z') {
        return None;
    }
    let index = characters.as_str().parse().ok()?;
    Some((namespace, index))
}

fn dense_boolean_values(values: BTreeMap<usize, bool>) -> Option<Vec<bool>> {
    values
        .into_iter()
        .enumerate()
        .map(|(expected, (index, value))| (index == expected).then_some(value))
        .collect()
}

fn parse_program(path: &Path) -> Result<Program, String> {
    let source = load_openqasm_source(path).map_err(|error| error.to_string())?;
    match source.version.major {
        2 => openqasm2::parse_str(&source.text, path.to_string_lossy().as_ref())
            .map_err(|error| error.to_string()),
        3 => openqasm3::parse_str(&source.text, path.to_string_lossy().as_ref())
            .map_err(|error| error.to_string()),
        major => Err(format!("unsupported OpenQASM major version {major}")),
    }
}

fn pair_sides(pair: &str) -> Result<(&str, &str), String> {
    pair.split_once('=')
        .ok_or_else(|| format!("invalid endpoint pair: {pair}"))
}

fn resolve_endpoint(program: &Program, specification: &str) -> Result<Endpoint, String> {
    let (kind, cell) = specification
        .split_once(':')
        .ok_or_else(|| format!("invalid endpoint: {specification}"))?;
    let (name, index) = indexed_cell(cell)?;
    match kind {
        "quantum" => {
            let register = program
                .quantum_registers
                .iter()
                .find(|register| register.name == name)
                .ok_or_else(|| format!("unknown quantum register: {name}"))?;
            if index >= register.width {
                return Err(format!(
                    "quantum endpoint is out of bounds: {specification}"
                ));
            }
            Ok(Endpoint::Quantum(Qubit {
                register: register.id,
                index,
            }))
        }
        "classical" => {
            let register = program
                .classical_registers
                .iter()
                .find(|register| register.name == name)
                .ok_or_else(|| format!("unknown classical register: {name}"))?;
            if index >= register.width {
                return Err(format!(
                    "classical endpoint is out of bounds: {specification}"
                ));
            }
            Ok(Endpoint::Classical(ClassicalBit {
                register: register.id,
                index,
            }))
        }
        _ => Err(format!("invalid endpoint kind: {kind}")),
    }
}

fn indexed_cell(cell: &str) -> Result<(&str, usize), String> {
    let cell = cell
        .strip_suffix(']')
        .ok_or_else(|| format!("invalid indexed endpoint: {cell}"))?;
    let (name, index) = cell
        .split_once('[')
        .ok_or_else(|| format!("invalid indexed endpoint: {cell}"))?;
    let index = index
        .parse()
        .map_err(|_| format!("invalid endpoint index: {index}"))?;
    Ok((name, index))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use irene::equivalence::Evidence;

    use super::*;

    #[test]
    fn density_witness_serializes_exact_coefficients_and_all_coordinates() {
        let witness = DensityCounterexample {
            ket_inputs: vec![true],
            bra_inputs: vec![false],
            ket_outputs: vec![false, true],
            bra_outputs: vec![true, false],
            classical_outputs: vec![true],
            root_of_unity_order: 1 << 62,
            sqrt_three_coefficients: vec![],
            exact_factors: vec![],
            difference_coefficients: vec![
                (0, "-1/2".parse().unwrap()),
                ((1 << 61) - 1, "3/4".parse().unwrap()),
            ],
        };
        assert_eq!(
            serialize_density_counterexample(&witness),
            json!({
                "ket_inputs": [true], "bra_inputs": [false],
                "ket_outputs": [false, true], "bra_outputs": [true, false],
                "classical_outputs": [true], "root_of_unity_order": "4611686018427387904",
                "difference_coefficients": [
                    {"power": "0", "coefficient": "-1/2"},
                    {"power": "2305843009213693951", "coefficient": "3/4"},
                ],
            })
        );
    }

    #[test]
    fn exact_product_preserves_both_radical_components() {
        let witness = DensityCounterexample {
            ket_inputs: vec![],
            bra_inputs: vec![],
            ket_outputs: vec![],
            bra_outputs: vec![],
            classical_outputs: vec![],
            root_of_unity_order: 1 << 62,
            difference_coefficients: vec![(0, "1/2".parse().unwrap())],
            sqrt_three_coefficients: vec![(1, "-3/4".parse().unwrap())],
            exact_factors: vec![irene::equivalence::DensityExactFactor {
                coefficients: vec![(2, "5/7".parse().unwrap())],
                sqrt_three_coefficients: vec![(3, "-2".parse().unwrap())],
            }],
        };
        let value = serialize_density_counterexample(&witness);
        assert_eq!(value["certificate_kind"], "cyclotomic_exact_product_v1");
        assert_eq!(
            value["sqrt_three_coefficients"],
            json!([
                {"power": "1", "coefficient": "-3/4"}
            ])
        );
        assert_eq!(
            value["exact_factors"],
            json!([{
                "coefficients": [{"power": "2", "coefficient": "5/7"}],
                "sqrt_three_coefficients": [{"power": "3", "coefficient": "-2"}]
            }])
        );
    }

    #[test]
    fn analysis_serializes_exact_counterexample_vectors() {
        let analysis = Analysis {
            verdict: Verdict::NotEquivalent,
            evidence: Evidence::PhaseCounterexample,
            counterexample: Some(Counterexample {
                ket_inputs: vec![true, false, true],
                bra_inputs: Some(vec![false, true, false]),
            }),
            density_counterexample: None,
            solver_queries: Vec::new(),
            kernel_terms: (2, 3),
        };

        let result = &serialize_analysis(&analysis)["results"][0];
        assert_eq!(
            result["counterexample"],
            json!({
                "ket_inputs": [true, false, true],
                "bra_inputs": [false, true, false],
            })
        );
    }

    #[test]
    fn output_counterexample_serializes_absent_bra_as_null() {
        let counterexample = Counterexample {
            ket_inputs: vec![false, true],
            bra_inputs: None,
        };

        assert_eq!(
            serialize_counterexample(&counterexample),
            json!({
                "ket_inputs": [false, true],
                "bra_inputs": null,
            })
        );
    }

    #[test]
    fn solver_result_keeps_exact_model_beyond_bounded_stream() {
        let stdout = format!(
            "sat\n{}\n((x0 true) (x1 false) (z0 false) (z1 true))\n",
            "diagnostic ".repeat(MAX_SOLVER_STREAM_BYTES)
        );
        let result = SolverResult {
            solver: Solver::Z3,
            status: SolverStatus::Sat,
            stdout: stdout.clone(),
            stderr: "warning".to_owned(),
            duration: Duration::from_millis(125),
        };

        let serialized = serialize_solver_result(&result);
        assert_eq!(serialized["solver"], "Z3");
        assert_eq!(serialized["status"], "Sat");
        assert_eq!(serialized["stdout_bytes"], stdout.len());
        assert_eq!(serialized["stdout_truncated"], true);
        assert!(serialized["stdout"].as_str().unwrap().len() <= MAX_SOLVER_STREAM_BYTES);
        assert_eq!(
            serialized["model"],
            json!({
                "ket_inputs": [true, false],
                "bra_inputs": [false, true],
            })
        );
    }

    #[test]
    fn stream_bound_never_splits_utf8() {
        let stream = format!("{}é", "a".repeat(MAX_SOLVER_STREAM_BYTES - 1));
        let (bounded, truncated) = bounded_stream(&stream);

        assert!(truncated);
        assert_eq!(bounded.len(), MAX_SOLVER_STREAM_BYTES - 1);
        assert!(bounded.is_char_boundary(bounded.len()));
    }

    #[test]
    fn incomplete_model_is_not_reported_as_replayable() {
        assert_eq!(extract_boolean_model("sat\n((x0 true) (x2 false))\n"), None);
        assert_eq!(extract_boolean_model("sat\n"), None);
    }
}
