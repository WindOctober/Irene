use super::*;
fn parse(width: usize, gates: &str) -> Program {
    crate::frontend::openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[{width}] q; {gates}"),
        "frontier-test",
    )
    .unwrap()
}
fn encoder() -> Encoder {
    Encoder::new(&DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    })
    .unwrap()
}
fn coefficients(p: &Polynomial) -> [BigRational; 4] {
    let mut out = std::array::from_fn(|_| integer(0));
    for atom in p {
        assert_eq!(atom.guard, "true");
        assert!(!atom.radical);
        let Power::Constant(p) = atom.power else {
            panic!("unclosed power");
        };
        assert_eq!(p % (ORDER / 8), 0);
        out[(p / (ORDER / 8)) as usize] += &atom.weight;
    }
    out
}

#[test]
fn complete_frontier_matches_independent_integer_eighth_root_matrices() {
    // Independent test-only integer arithmetic: a shared denominator2^h,
    // zeta^4=-1, H=(zeta-zeta^3)/2 times the signed Hadamard matrix.
    // Every basis column is computed, including the untouched spectator.
    for seed in 0..12 {
        let mut exact = vec![[0i64; 4]; 64];
        for i in 0..8 {
            exact[i * 8 + i][0] = 1;
        }
        let mut denominator = 1i64;
        let mut gates = String::new();
        let mut state = seed + 19u64;
        let shift = |a: [i64; 4], exponent: usize| {
            let mut b = [0; 4];
            for (i, c) in a.into_iter().enumerate() {
                b[(i + exponent) % 4] += if (i + exponent) % 8 >= 4 { -c } else { c };
            }
            b
        };
        for _ in 0..18 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let gate = (state >> 32) % 7;
            gates.push_str(match gate {
                0 => "h q[0];",
                1 => "t q[0];",
                2 => "tdg q[1];",
                3 => "x q[1];",
                4 => "y q[0];",
                5 => "cx q[0],q[1];",
                _ => "swap q[0],q[1];",
            });
            let mut next = vec![[0i64; 4]; 64];
            for row in 0..8 {
                for col in 0..8 {
                    let value = exact[row * 8 + col];
                    let mut add = |out: usize, v: [i64; 4]| {
                        for i in 0..4 {
                            next[out * 8 + col][i] += v[i];
                        }
                    };
                    match gate {
                        0 => {
                            let a = shift(value, 1);
                            let b = shift(value, 3);
                            let v = std::array::from_fn(|i| a[i] - b[i]);
                            add(row & !1, v);
                            add(row | 1, if row & 1 == 0 { v } else { v.map(|c| -c) });
                        }
                        1 => add(row, shift(value, if row & 1 != 0 { 1 } else { 0 })),
                        2 => add(row, shift(value, if row & 2 != 0 { 7 } else { 0 })),
                        3 => add(row ^ 2, value),
                        4 => add(row ^ 1, shift(value, if row & 1 == 0 { 2 } else { 6 })),
                        5 => add(row ^ if row & 1 != 0 { 2 } else { 0 }, value),
                        _ => add((row & !3) | ((row & 1) << 1) | ((row & 2) >> 1), value),
                    }
                }
            }
            if gate == 0 {
                denominator *= 2;
            }
            exact = next;
        }
        let (d, actual) = matrix(&parse(3, &gates), &mut encoder()).unwrap();
        assert_eq!(d, 8);
        for (i, entry) in actual.iter().enumerate() {
            assert_eq!(
                coefficients(entry),
                exact[i].map(|n| BigRational::new(n.into(), denominator.into())),
                "seed={seed} entry={i} gates={gates}"
            );
        }
    }
}

#[test]
fn frontier_norm_retains_global_relative_phase_and_coherent_cancellation() {
    for gates in [
        "h q[0]; h q[0];",
        "h q[0]; z q[0]; h q[0]; x q[0];",
        "x q[0]; y q[0]; z q[0];",
        "h q[0]; t q[0]; tdg q[0]; h q[0];",
    ] {
        assert_eq!(
            norm(&parse(2, gates)),
            Some(vec![(0, integer(1))]),
            "{gates}"
        );
    }
    for gates in ["z q[1];", "h q[0]; z q[0]; h q[0];", "crz(2*pi) q[0],q[1];"] {
        assert_eq!(norm(&parse(2, gates)), Some(vec![]), "{gates}");
    }
    assert_eq!(
        norm(&parse(2, "t q[1];")),
        Some(vec![
            (0, ratio(1, 2)),
            (ORDER / 8, ratio(1, 4)),
            (3 * ORDER / 8, ratio(-1, 4))
        ])
    );
    let a = matrix(&parse(2, "h q[0]; cx q[0],q[1];"), &mut encoder())
        .unwrap()
        .1;
    let b = matrix(&parse(2, "cx q[0],q[1]; h q[0];"), &mut encoder())
        .unwrap()
        .1;
    assert!(a != b);
}

#[test]
fn frontier_refuses_unsupported_coefficients_nonunitary_and_budgets() {
    for gates in [
        "p(pi/3) q[0];",
        "p(0.1) q[0];",
        "rx(0.1) q[0];",
        "reset q[0];",
        "bit c; c=measure q[0];",
    ] {
        assert_eq!(norm(&parse(2, gates)), None, "{gates}");
    }
    assert_eq!(norm(&parse(11, "h q[0];")), None);
    let mut e = encoder();
    e.work = 0;
    assert!(matrix(&parse(2, "h q[0];"), &mut e).is_none());
    assert_eq!(
        norm(&parse(6, &"h q[0];".repeat(MAX_TABLE_STEPS / 4096 + 1))),
        None
    );
}

#[test]
fn exact_frontier_admits_ten_coherent_wires() {
    // Full-input trace: a Z on the last wire has zero trace, including all
    // nine spectators. This is not an initialized-state or sampled check.
    assert_eq!(norm(&parse(10, "z q[9];")), Some(vec![]));
}

#[test]
fn frontier_preference_counts_actual_blocks_without_relaxing_admission() {
    let circuit = parse(
        5,
        &format!("h q[0]; {} h q[0];", "t q[0]; tdg q[0];".repeat(64)),
    );
    let (_, cells, gate_steps) = table_cost(&circuit).unwrap();
    let block_steps = cells * blocks(&circuit).unwrap().len();
    assert!(block_steps < (1 << 17) && (1 << 17) < gate_steps);
    assert!(preferred(&circuit, 17));
    assert!(!preferred(&circuit, 8));
    assert_eq!(norm(&circuit), Some(vec![(0, integer(1))]));
    let over = parse(6, &"t q[0];".repeat(MAX_TABLE_STEPS / 4096 + 1));
    assert!(!preferred(&over, usize::MAX));
    assert!(!preferred(&parse(11, "h q[0];"), usize::MAX));
    assert!(!preferred(&parse(2, "reset q[0];"), usize::MAX));
}

#[test]
fn frontier_block_operand_remapping_matches_complete_toffoli_matrix() {
    for gates in ["ccx q[2],q[0],q[1];", "h q[1]; ccz q[2],q[0],q[1]; h q[1];"] {
        let (d, actual) = matrix(&parse(4, gates), &mut encoder()).unwrap();
        assert_eq!(d, 16);
        for input in 0..d {
            let output = input ^ if input & 5 == 5 { 2 } else { 0 };
            for row in 0..d {
                assert_eq!(
                    coefficients(&actual[row * d + input]),
                    [
                        integer(i64::from(row == output)),
                        integer(0),
                        integer(0),
                        integer(0)
                    ]
                );
            }
        }
    }
}

#[test]
fn signed_unit_root_products_preserve_radicals_and_noncanonical_sums() {
    for sign in [-1, 1] {
        for shift in 0..8 {
            let mut e = encoder();
            let root = e
                .literal(integer(sign), shift * (ORDER / 8), false)
                .unwrap();
            let mut value = Vec::new();
            for p in 0..4 {
                for radical in [false, true] {
                    value.extend(
                        e.literal(ratio(p as i64 + 1, 3), p * (ORDER / 8), radical)
                            .unwrap(),
                    );
                }
            }
            let fast = e.multiply(root.clone(), value.clone()).unwrap();
            // Split a unit root into two half roots to force the ordinary
            // generic convolution, including duplicate-result compaction.
            let mut halves = e
                .literal(ratio(sign, 2), shift * (ORDER / 8), false)
                .unwrap();
            halves.extend(halves.clone());
            assert!(fast == e.multiply(halves, value.clone()).unwrap());
            let mut noncanonical = value.clone();
            noncanonical.extend(value);
            let actual = e.multiply(root, noncanonical).unwrap();
            let mut expected = fast.clone();
            expected.extend(fast);
            assert!(actual == e.compact(expected).unwrap());
        }
    }
}
