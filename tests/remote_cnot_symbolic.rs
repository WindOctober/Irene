use std::fs;
use std::path::{Path, PathBuf};

use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, Program, Qubit, Register};
use irene::symbolic::optimize::simplify;
use irene::symbolic::{
    ExecutionConfig, HistoryEntry, HybridMemory, HybridPathSum, PhasePolynomial, Scalar, execute,
};
use num_rational::BigRational;

fn benchmark_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benchmarks/openqasm3-programs/programs/remote-cnot")
        .join(name)
}

fn parse(path: &Path) -> Program {
    let source = fs::read_to_string(path).unwrap();
    openqasm3::parse_str(&source, path.to_string_lossy().as_ref()).unwrap()
}

fn symbolic_data_inputs(program: &Program) -> ExecutionConfig {
    let q = program
        .quantum_registers
        .iter()
        .find(|register| register.name == "q")
        .unwrap();
    ExecutionConfig::with_symbolic_inputs([
        Qubit {
            register: q.id,
            index: 0,
        },
        Qubit {
            register: q.id,
            index: 3,
        },
    ])
}

fn register_cell(registers: &[Register], id: irene::ir::SymbolId, index: usize) -> String {
    let register = registers.iter().find(|register| register.id == id).unwrap();
    format!("{}[{index}]", register.name)
}

fn qubit_name(program: &Program, qubit: &Qubit) -> String {
    register_cell(&program.quantum_registers, qubit.register, qubit.index)
}

fn bit_name(program: &Program, bit: &ClassicalBit) -> String {
    register_cell(&program.classical_registers, bit.register, bit.index)
}

fn print_memory(program: &Program, memory: &HybridMemory) {
    println!("  quantum:");
    for (qubit, value) in &memory.quantum {
        println!("    {} = {value}", qubit_name(program, qubit));
    }
    if !memory.classical.is_empty() {
        println!("  classical:");
        for (bit, value) in &memory.classical {
            println!("    {} = {value}", bit_name(program, bit));
        }
    }
    if !memory.history.is_empty() {
        println!("  history:");
        for (index, entry) in memory.history.iter().enumerate() {
            match entry {
                HistoryEntry::Write { target, value } => {
                    println!("    {index}: write {} = {value}", bit_name(program, target));
                }
                HistoryEntry::Discard { value } => {
                    println!("    {index}: discard {value}");
                }
            }
        }
    }
}

fn print_state(label: &str, program: &Program, state: &HybridPathSum) {
    println!("\n===== {label} =====");
    println!("input:");
    print_memory(program, &state.input);
    for (index, component) in state.components.iter().enumerate() {
        println!("component {index}:");
        let guard = component
            .guard
            .iter()
            .map(|equation| format!("({equation} = 0)"))
            .collect::<Vec<_>>()
            .join(" ∧ ");
        println!(
            "  guard   = {}",
            if guard.is_empty() { "1" } else { &guard }
        );
        println!("  scalar  = {}", component.scalar);
        println!("  support = {:?}", component.path_support);
        println!("  phase   = {}", component.phase);
        print_memory(program, &component.output);
    }
}

#[test]
fn executes_and_prints_remote_cnot_states() {
    let left = parse(&benchmark_file("left.qasm"));
    let right = parse(&benchmark_file("right.qasm"));

    let left_state = execute(&left, &symbolic_data_inputs(&left)).unwrap();
    let right_state = execute(&right, &symbolic_data_inputs(&right)).unwrap();

    print_state("unitary routed CNOT", &left, &left_state);
    print_state("measurement-based remote CNOT", &right, &right_state);

    let simplified_left = simplify(left_state);
    let simplified_right = simplify(right_state);

    assert_eq!(simplified_left.components.len(), 1);
    assert_eq!(simplified_right.components.len(), 4);
    for component in &simplified_right.components {
        assert!(component.guard.is_empty());
        assert!(component.path_support.is_empty());
        assert_eq!(component.phase, PhasePolynomial::zero());
        assert_eq!(
            component.scalar,
            Scalar::rational(BigRational::new(1.into(), 2.into()))
        );
    }

    print_state("simplified unitary routed CNOT", &left, &simplified_left);
    print_state(
        "simplified measurement-based remote CNOT",
        &right,
        &simplified_right,
    );
}
