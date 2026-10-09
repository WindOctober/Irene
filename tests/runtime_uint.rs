mod common;

use common::unitary::assert_fresh_ids;
use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, Program, Qubit};
use irene::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, SymbolicError, Variable, execute,
};

fn parse(body: &str) -> Program {
    let p = openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "runtime-uint.qasm",
    )
    .unwrap();
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
    let mut answers = Vec::new();
    for c in &hps.components {
        let mut value = 0;
        for (i, bit) in cells.iter().enumerate() {
            let b = &c.output.classical[bit];
            assert!(b.is_zero() || b.is_one());
            value |= u64::from(b.is_one()) << i;
        }
        answers.push(value);
    }
    assert!(answers.iter().all(|v| *v == answers[0]));
    answers[0]
}

#[test]
fn fixed_width_storage_and_constant_initializers() {
    for (source, expected) in [
        ("const int n=4; uint[n] a=3; uint[n] b=a; a=b;", 3),
        ("uint a=4294967295;", u64::from(u32::MAX)),
        ("uint[64] a=18446744073709551615; a>>=63;", 1),
        ("const uint[8] v=3; uint[4] a=v+1;", 4),
        ("const uint[3] n=7; uint[3] a=n+1;", 0),
        ("uint[4] a=3; a[3]=true;", 11),
        ("uint[4] a=3; if(true) { uint[4] a=8; a=1; }", 3),
        (
            "const int n=10; uint[n] a=1; for uint i in [0:n-1] a<<=1;",
            0,
        ),
    ] {
        assert_eq!(word(source, "a"), expected, "{source}");
    }
}

#[test]
fn shifts_use_the_complete_old_word_and_zero_fill() {
    for width in 1..=4 {
        let mask = (1u64 << width) - 1;
        for value in 0..=mask {
            for shift in 0..=width + 1 {
                for (op, expected) in [("<<", (value << shift) & mask), (">>", value >> shift)] {
                    for update in [format!("a {op}= {shift};"), format!("a=a {op} {shift};")] {
                        let source = format!("uint[{width}] a={value}; {update}");
                        assert_eq!(word(&source, "a"), expected, "{source}");
                    }
                }
            }
        }
    }
    assert_eq!(word("uint[4] a=3; a ^= (a << 1);", "a"), 5);
    assert_eq!(word("uint[4] a=9; a |= (a >> 1);", "a"), 13);
}

#[test]
fn bitwise_updates_match_small_unsigned_words() {
    for width in 1..=4 {
        let mask = (1u64 << width) - 1;
        for a in 0..=mask {
            assert_eq!(word(&format!("uint[{width}] a={a}; a=~a;"), "a"), mask ^ a);
            for b in 0..=mask {
                for (op, expected) in [("&", a & b), ("|", a | b), ("^", a ^ b)] {
                    for update in [format!("a {op}= b;"), format!("a=a {op} b;")] {
                        assert_eq!(
                            word(
                                &format!("uint[{width}] a={a}; uint[{width}] b={b}; {update}"),
                                "a"
                            ),
                            expected
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn comparisons_preserve_unsigned_order() {
    for a in 0..8 {
        for b in 0..8 {
            for (op, expected) in [
                ("==", a == b),
                ("!=", a != b),
                ("<", a < b),
                ("<=", a <= b),
                (">", a > b),
                (">=", a >= b),
            ] {
                assert_eq!(
                    word(
                        &format!("uint[3] a={a}; uint[3] b={b}; bool r=(a {op} b);"),
                        "r"
                    ),
                    u64::from(expected)
                );
                assert_eq!(
                    word(&format!("uint[3] a={a}; bool r=(a {op} {b});"), "r"),
                    u64::from(expected)
                );
            }
        }
    }
}

#[test]
fn measured_values_remain_symbolic_through_word_assignment() {
    let p = parse("qubit q; uint[3] a=0; measure q -> a[0]; a <<= 2;");
    let r = &p.classical_registers[0];
    let cells: Vec<_> = (0..3)
        .map(|index| ClassicalBit {
            register: r.id,
            index,
        })
        .collect();
    let q = Qubit {
        register: p.quantum_registers[0].id,
        index: 0,
    };
    let hps = execute(
        &p,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new([q.clone()], cells.clone()),
    )
    .unwrap();
    assert!(!hps.components.is_empty());
    for c in &hps.components {
        assert!(c.output.classical[&cells[0]].is_zero());
        assert!(c.output.classical[&cells[1]].is_zero());
        assert_eq!(
            c.output.classical[&cells[2]],
            BooleanPolynomial::variable(Variable::Input(q.clone()))
        );
    }
    for initial in [0, 1] {
        let prep = if initial == 1 { "x q;" } else { "" };
        assert_eq!(
            word(
                &format!("qubit q; {prep} bit b=measure q; uint[3] a=0; if(b) a=1; a<<=2;"),
                "a"
            ),
            initial * 4
        );
    }
}

#[test]
fn reads_of_uninitialized_bits_are_not_hidden_by_shifts() {
    for source in [
        "uint[4] a; a <<= 4;",
        "uint[4] a; a[0]=true; a >>= 1;",
        "uint[4] a; uint[4] b=a;",
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
fn rejects_dynamic_widths_lossy_assignments_and_unsupported_operations() {
    for source in [
        "uint n=4; uint[n] a=1;",
        "input uint n; uint[n] a=1;",
        "uint[0] a;",
        "uint[65] a;",
        "uint[-1] a;",
        "for uint n in [1:2] { uint[n] a=1; }",
        "uint[4] a=16;",
        "uint[4] a=-1;",
        "uint[4] a=1; uint[3] b=a;",
        "uint[4] a=1; a<<=-1;",
        "uint[4] a=1; uint[4] s=1; a<<=s;",
        "uint[4] a=1; a+=16;",
        "uint[4] a=1; a=a*2;",
        "uint[4] a=1; uint[3] b=1; a+=b;",
        "uint[4] a=1; bit[4] b=a;",
        "uint[4] a=1; a[4]=true;",
        "uint a=1; a<<=1;",
        "uint a=1; a=~a;",
        "uint a=1; a[0]=true;",
        "uint[4] a=1; uint[3] b=1; a^=b;",
        "uint[4] a=1; uint[4] b=int[4](a);",
    ] {
        assert!(
            openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {source}"),
                "invalid-uint.qasm"
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn add_subtract_wrap_and_use_the_complete_old_word() {
    for width in 1..=4 {
        let modulus = 1u64 << width;
        for a in 0..modulus {
            for b in 0..modulus {
                for (op, expected) in [("+", (a + b) % modulus), ("-", (a + modulus - b) % modulus)]
                {
                    for update in [
                        format!("a {op}= b;"),
                        format!("a=a {op} b;"),
                        format!("a=a {op} {b};"),
                    ] {
                        assert_eq!(
                            word(
                                &format!("uint[{width}] a={a}; uint[{width}] b={b}; {update}"),
                                "a"
                            ),
                            expected
                        );
                    }
                }
            }
        }
    }
    assert_eq!(word("uint[8] a=255; a+=1; a-=1;", "a"), 255);
    assert_eq!(word("uint[8] a=3; a=a+(a+1);", "a"), 7);
    assert_eq!(word("uint[8] a=3; a=1-a;", "a"), 254);
    assert_eq!(word("uint a=4294967295; a+=1;", "a"), 0);
}

#[test]
fn addition_does_not_hide_reads_of_uninitialized_storage() {
    let p = parse("uint[4] a; a+=1;");
    assert!(matches!(
        execute(&p, &ExecutionConfig::zero(), &OutputSelection::new([], [])),
        Err(SymbolicError::UninitializedClassical(_))
    ));
}
