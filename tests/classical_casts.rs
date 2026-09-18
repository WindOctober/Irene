mod common;

use common::unitary::assert_fresh_ids;
use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, Program, Qubit};
use irene::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, SymbolicError, Variable, execute,
};

fn parse(body: &str) -> Program {
    let p = openqasm3::parse_str(&format!("OPENQASM 3.0; {body}"), "casts.qasm").unwrap();
    assert_fresh_ids(&p);
    p
}

fn word(body: &str, name: &str) -> u64 {
    let p = parse(body);
    let r = p
        .classical_registers
        .iter()
        .find(|r| r.name == name)
        .unwrap();
    let cells: Vec<_> = (0..r.width)
        .map(|index| ClassicalBit {
            register: r.id,
            index,
        })
        .collect();
    let hps = execute(
        &p,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], cells.clone()),
    )
    .unwrap();
    assert!(!hps.components.is_empty());
    let values: Vec<u64> = hps
        .components
        .iter()
        .map(|component| {
            cells
                .iter()
                .enumerate()
                .map(|(i, cell)| {
                    let b = &component.output.classical[cell];
                    assert!(b.is_zero() || b.is_one());
                    u64::from(b.is_one()) << i
                })
                .sum()
        })
        .collect();
    assert!(values.iter().all(|v| *v == values[0]));
    values[0]
}

#[test]
fn same_width_casts_preserve_bits_and_signed_interpretation() {
    for width in 1..=5 {
        for value in 0..(1_u64 << width) {
            let signed = if value & (1 << (width - 1)) != 0 {
                value as i64 - (1 << width)
            } else {
                value as i64
            };
            let prefix = format!(
                "bit[{width}] b=\"{value:0width$b}\";",
                width = width as usize
            );
            assert_eq!(
                word(
                    &format!(
                        "{prefix} uint[{width}] u=uint[{width}](b); bit[{width}] r=bit[{width}](int[{width}](u));"
                    ),
                    "r"
                ),
                value
            );
            assert_eq!(
                word(
                    &format!("{prefix} bool r=(int[{width}](b)=={signed});"),
                    "r"
                ),
                1
            );
            assert_eq!(
                word(
                    &format!("const int[{width}] n={signed}; uint[{width}] r=uint[{width}](n);"),
                    "r"
                ),
                value
            );
            assert_eq!(
                word(
                    &format!("const int[{width}] n={signed}; bool r=(n<0);"),
                    "r"
                ),
                u64::from(signed < 0)
            );
        }
    }
}

#[test]
fn default_integer_casts_use_32_bits_without_bit_level_permissions() {
    for (source, expected) in [
        ("const int n=-1; uint r=uint(n);", u64::from(u32::MAX)),
        ("uint u=4294967295; bool r=(int(u)==-1);", 1),
        ("const int[32] n=-2147483648; bool r=(int(n)<0);", 1),
        (
            "const int n=-1; uint[32] r=uint[32](n);",
            u64::from(u32::MAX),
        ),
    ] {
        assert_eq!(word(source, "r"), expected, "{source}");
    }
}

#[test]
fn bool_casts_test_nonzero_instead_of_only_the_low_bit() {
    for value in 0..16 {
        let expected = u64::from(value != 0);
        assert_eq!(
            word(&format!("uint[4] a={value}; bool r=bool(a);"), "r"),
            expected
        );
        assert_eq!(
            word(&format!("const uint[4] a={value}; bool r=bool(a);"), "r"),
            expected
        );
        assert_eq!(
            word(&format!("bit[4] a=\"{value:04b}\"; bool r=bool(a);"), "r"),
            expected
        );
    }
    assert_eq!(word("const int[4] a=-8; bool r=bool(a);", "r"), 1);
    assert_eq!(word("bool a=true; bit r=bit(a);", "r"), 1);
    assert_eq!(word("bit a=false; bool r=bool(a);", "r"), 0);
}

#[test]
fn static_integer_conditions_keep_lexical_scope_and_loop_values() {
    assert_eq!(
        word("const int n=-1; bool r=false; if(n<0) { r=true; }", "r"),
        1
    );
    assert_eq!(
        word(
            "const int n=-1; bool r=false; if(true) { const int n=1; r=(n>0); } r=r&&(n<0);",
            "r"
        ),
        1
    );
    assert_eq!(
        word("uint[3] r=0; for int i in [0:2] { if(i==1) { r=4; } }", "r"),
        4
    );
    assert_eq!(word("const uint[4] n=15; bool r=(n==15);", "r"), 1);
}

#[test]
fn casts_retain_measurement_dependence() {
    let p =
        parse("qubit[3] q; bit[3] b; measure q -> b; uint[3] u=uint[3](b); bit[3] r=bit[3](u);");
    let r = p
        .classical_registers
        .iter()
        .find(|r| r.name == "r")
        .unwrap();
    let cells: Vec<_> = (0..3)
        .map(|index| ClassicalBit {
            register: r.id,
            index,
        })
        .collect();
    let hps = execute(
        &p,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new([], cells.clone()),
    )
    .unwrap();
    assert!(!hps.components.is_empty());
    for component in &hps.components {
        for (index, cell) in cells.iter().enumerate() {
            assert_eq!(
                component.output.classical[cell],
                BooleanPolynomial::variable(Variable::Input(Qubit {
                    register: p.quantum_registers[0].id,
                    index
                }))
            );
        }
    }
}

#[test]
fn casts_do_not_initialize_their_sources() {
    for source in [
        "uint[4] a; bool r=bool(a);",
        "bit[4] a; uint[4] r=uint[4](a);",
    ] {
        let p = parse(source);
        let r = p.classical_registers.last().unwrap();
        let cells = (0..r.width).map(|index| ClassicalBit {
            register: r.id,
            index,
        });
        assert!(
            matches!(
                execute(
                    &p,
                    &ExecutionConfig::zero(),
                    &OutputSelection::new([], cells)
                ),
                Err(SymbolicError::UninitializedClassical(_))
            ),
            "{source}"
        );
    }
}

#[test]
fn unsupported_conversions_and_type_mismatches_are_rejected() {
    for source in [
        "bit[32] b; uint r=uint(b);",
        "uint[4] a=1; uint r=uint(a);",
        "uint[4] a=1; uint[3] r=uint[3](a);",
        "uint[4] a=1; uint[5] r=uint[5](a);",
        "uint[4] a=1; bit[3] r=bit[3](a);",
        "uint a=1; bit[32] r=bit[32](a);",
        "const int a=-1; bit[32] r=bit[32](a);",
        "uint[32] a=1; uint r=~uint(a);",
        "uint[32] a=1; uint r=(uint(a)<<1);",
        "const int a=-1; const uint b=1; bool r=(a==b);",
        "uint a=1; uint[32] b=1; bool r=(a==b);",
        "const uint[3] a=7; bool r=(a==8);",
        "const int[3] a=-4; bool r=(a==-5);",
        "uint[4] a=1; bool[1] r=bool[1](a);",
        "uint[4] a=1; bool r=(int[0](a)==0);",
        "uint[4] n=4; uint[4] a=1; bool r=(int[n](a)==0);",
        "uint[4] a=1; bool r=(a==true);",
    ] {
        assert!(
            openqasm3::parse_str(&format!("OPENQASM 3.0; {source}"), "invalid-cast.qasm").is_err(),
            "{source}"
        );
    }
}
