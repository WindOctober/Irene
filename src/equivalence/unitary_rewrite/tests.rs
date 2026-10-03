use super::*;
use crate::frontend::openqasm3;

#[test]
fn explicitly_unavailable_strategies_do_not_silently_select_off() {
    assert_eq!(parse_strategy(None), Ok(Strategy::Off));
    assert_eq!(parse_strategy(Some("wire")), Ok(Strategy::Wire));
    assert!(parse_strategy(Some("wrie")).is_err());
    assert!(parse_strategy(Some("")).is_err());
    assert!(parse_strategy(Some("port")).is_err());
}

#[test]
fn commuting_control_phase_is_a_native_candidate() {
    let source = parse("cx q[0], q[1]; t q[0]; cx q[0], q[1];");
    for strategy in [Strategy::Scan, Strategy::Wire] {
        assert_eq!(
            preprocess_with(&source, strategy)
                .expect("must match")
                .operation_count(),
            1
        );
    }
}

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
        "rewrite-test",
    )
    .unwrap()
}
fn strategies() -> Vec<Strategy> {
    vec![Strategy::Scan, Strategy::Wire]
}

// Independent exact dense operator evaluation in Q(zeta_16), zeta^8=-1.
// Test angles are rational multiples of pi. Every basis column is evaluated,
// retaining global phase (stronger than equality of channels).
type Cell = [i128; 8];
fn shift(a: Cell, k: i64) -> Cell {
    let mut b = [0; 8];
    for (i, c) in a.into_iter().enumerate() {
        let e = (i as i64 + k).rem_euclid(16) as usize;
        b[e % 8] += if e >= 8 { -c } else { c };
    }
    b
}
fn add(a: Cell, b: Cell) -> Cell {
    std::array::from_fn(|i| a[i] + b[i])
}
fn neg(a: Cell) -> Cell {
    a.map(|v| -v)
}
fn number(e: &crate::ir::NumericExpr) -> BigRational {
    use NumericExprKind::*;
    match &e.kind {
        Rational(r) => r.clone(),
        Constant(NumericConstant::Pi) => rational(1, 1),
        Neg(a) => -number(a),
        Add(a, b) => number(a) + number(b),
        Sub(a, b) => number(a) - number(b),
        Mul(a, b) => number(a) * number(b),
        Div(a, b) => number(a) / number(b),
        _ => panic!("test only supports pi-multiple angles"),
    }
}
fn matrix(p: &Program) -> Vec<[BigRational; 8]> {
    let mut data = vec![[0; 8]; 64];
    for i in 0..8 {
        data[i * 8 + i][0] = 1;
    }
    let mut denominator = 1i128;
    fn flatten<'a>(b: &'a Block, out: &mut Vec<&'a Statement>) {
        for s in &b.statements {
            match &s.kind {
                StatementKind::Scope(b) => flatten(b, out),
                StatementKind::Apply { .. } => out.push(s),
                _ => {}
            }
        }
    }
    let mut statements = vec![];
    flatten(&p.body, &mut statements);
    for s in statements {
        let StatementKind::Apply {
            gate,
            parameters,
            qubits,
        } = &s.kind
        else {
            unreachable!()
        };
        let q = qubits.iter().map(|q| q.index).collect::<Vec<_>>();
        let target = *q.last().unwrap();
        let rotation = matches!(gate, Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry);
        let factor = if *gate == Gate::H || rotation { 2 } else { 1 };
        let k = if parameters.is_empty() {
            0
        } else {
            let n = number(&parameters[0])
                * rational(
                    if matches!(gate, Gate::P | Gate::Cp) {
                        8
                    } else {
                        4
                    },
                    1,
                );
            assert_eq!(n.denom(), &1.into());
            i64::try_from(n.numer()).unwrap()
        };
        let mut next = vec![[0; 8]; 64];
        for row in 0..8 {
            let bit = (row >> target) & 1;
            let controls = q[..q.len() - 1].iter().all(|i| (row >> i) & 1 != 0);
            for col in 0..8 {
                let v = data[row * 8 + col];
                let mut put = |out: usize, w| {
                    next[out * 8 + col] = add(next[out * 8 + col], w);
                };
                match gate {
                    Gate::H => {
                        let w = add(shift(v, 2), neg(shift(v, 6)));
                        put(row & !(1 << target), w);
                        put(row | (1 << target), if bit == 0 { w } else { neg(w) });
                    }
                    Gate::X | Gate::Cx | Gate::Ccx => {
                        put(if controls { row ^ (1 << target) } else { row }, v)
                    }
                    Gate::Y | Gate::Cy => {
                        if controls {
                            put(row ^ (1 << target), shift(v, if bit == 0 { 4 } else { 12 }));
                        } else {
                            put(row, v);
                        }
                    }
                    Gate::Swap => put(
                        if (row >> q[0]) & 1 != bit {
                            row ^ (1 << q[0]) ^ (1 << target)
                        } else {
                            row
                        },
                        v,
                    ),
                    Gate::Z | Gate::Cz | Gate::Ccz => {
                        put(row, shift(v, if controls && bit != 0 { 8 } else { 0 }))
                    }
                    Gate::S | Gate::Sdg | Gate::T | Gate::Tdg => {
                        let e = match gate {
                            Gate::S => 4,
                            Gate::Sdg => -4,
                            Gate::T => 2,
                            _ => -2,
                        };
                        put(row, shift(v, if bit == 0 { 0 } else { e }));
                    }
                    Gate::P | Gate::Cp => {
                        put(row, shift(v, if controls && bit != 0 { k } else { 0 }))
                    }
                    Gate::Rz | Gate::Crz => put(
                        row,
                        shift(
                            v,
                            if controls {
                                if bit == 0 { -k } else { k }
                            } else {
                                0
                            },
                        ),
                    ),
                    Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry => {
                        if !controls {
                            put(row, v.map(|x| 2 * x));
                        } else {
                            put(row, add(shift(v, k), shift(v, -k)));
                            let off = if matches!(gate, Gate::Rx | Gate::Crx) {
                                add(shift(v, -k), neg(shift(v, k)))
                            } else {
                                let w = add(shift(v, k + 12), neg(shift(v, -k + 12)));
                                if bit == 0 { w } else { neg(w) }
                            };
                            put(row ^ (1 << target), off);
                        }
                    }
                }
            }
        }
        data = next;
        denominator *= factor;
    }
    data.into_iter()
        .map(|c| c.map(|n| BigRational::new(n.into(), denominator.into())))
        .collect()
}

#[test]
fn rules_preserve_complete_operators_including_controlled_phase() {
    let cases = [
        "h q[0]; x q[1]; h q[0];",
        "h q[0]; x q[0]; h q[0];",
        "h q[0]; z q[0]; h q[0];",
        "h q[1]; cx q[0],q[1]; h q[1];",
        "h q[2]; ccx q[0],q[1],q[2]; h q[2];",
        "h q[2]; ccz q[0],q[1],q[2]; h q[2];",
        "cx q[0],q[1]; cx q[0],q[2]; cx q[0],q[1];",
        "cx q[0],q[1]; t q[0]; cx q[0],q[1];",
        "t q[0]; s q[0]; tdg q[0];",
        "rx(pi/4) q[0]; rx(-pi/4) q[0];",
        "ry(pi/2) q[0]; ry(pi/2) q[0];",
        "rz(pi) q[0]; rz(pi) q[0];",
        "crx(pi) q[0],q[1]; crx(pi) q[0],q[1];",
        "cry(pi) q[0],q[1]; cry(pi) q[0],q[1];",
        "crz(pi) q[0],q[1]; crz(pi) q[0],q[1];",
        "cp(pi/2) q[0],q[1]; cp(3*pi/2) q[0],q[1];",
        "h q[0]; cx q[1],q[0]; h q[0]; t q[0]; h q[0]; cz q[1],q[0]; h q[0];",
    ];
    for strategy in strategies() {
        for body in cases {
            let p = parse(body);
            let reduced = preprocess_with(&p, strategy).unwrap_or_else(|| p.clone());
            assert_eq!(matrix(&p), matrix(&reduced), "{strategy:?}: {body}");
            assert!(reduced.operation_count() <= p.operation_count());
            let mut seen = BTreeSet::new();
            reduced.visit_ast_ids(|id| assert!(seen.insert(id)));
        }
    }
}

#[test]
fn generated_contexts_do_not_turn_commutation_into_anticommutation() {
    let gates = [
        "h q[0];",
        "x q[0];",
        "y q[0];",
        "z q[0];",
        "t q[0];",
        "tdg q[0];",
        "cx q[0],q[1];",
        "cx q[1],q[0];",
        "cz q[1],q[0];",
        "swap q[0],q[1];",
        "h q[1];",
        "ccx q[0],q[1],q[2];",
        "crx(pi) q[0],q[1];",
    ];
    for seed in 0..24u64 {
        let mut state = seed + 1;
        let mut body = String::new();
        for _ in 0..20 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            body.push_str(gates[(state >> 32) as usize % gates.len()]);
        }
        let source = parse(&body);
        let expected = matrix(&source);
        for strategy in strategies() {
            let p = preprocess_with(&source, strategy).unwrap_or_else(|| source.clone());
            assert_eq!(matrix(&p), expected, "{strategy:?}: {body}");
        }
    }
}

#[test]
fn every_claimed_commutation_in_the_gate_catalogue_is_exact() {
    let gates = [
        "h q[0];",
        "h q[1];",
        "x q[0];",
        "x q[1];",
        "y q[0];",
        "z q[0];",
        "s q[0];",
        "tdg q[1];",
        "cx q[0],q[1];",
        "cx q[1],q[0];",
        "cx q[0],q[2];",
        "cy q[0],q[1];",
        "cz q[0],q[1];",
        "swap q[0],q[1];",
        "ccx q[0],q[1],q[2];",
        "ccx q[0],q[2],q[1];",
        "ccz q[0],q[1],q[2];",
        "rx(pi/4) q[0];",
        "ry(pi/4) q[0];",
        "rz(pi/4) q[0];",
        "p(pi/4) q[0];",
        "cp(pi/4) q[0],q[1];",
        "crx(pi/4) q[0],q[1];",
        "cry(pi/4) q[0],q[1];",
        "crz(pi/4) q[0],q[1];",
    ];
    let ops = gates.map(|g| Op::from(parse(g).body.statements[0].clone()));
    for a in &ops {
        for b in &ops {
            if commutes(a, b) {
                let mut p = parse("");
                p.body.statements = vec![a.statement.clone(), b.statement.clone()];
                let expected = matrix(&p);
                p.body.statements.reverse();
                assert_eq!(
                    matrix(&p),
                    expected,
                    "{:?} {:?}: {:?} {:?}",
                    a.gate,
                    a.wires,
                    b.gate,
                    b.wires
                );
            }
        }
    }
}

#[test]
fn operator_period_is_four_pi_for_controlled_rotations() {
    for g in ["crx", "cry", "crz"] {
        let source = parse(&format!("{g}(pi) q[0],q[1]; {g}(pi) q[0],q[1];"));
        for strategy in strategies() {
            let p = preprocess_with(&source, strategy).unwrap();
            assert_eq!(p.operation_count(), 1);
            assert_ne!(matrix(&p), matrix(&parse("")));
        }
    }
}

#[test]
fn source_domains_and_nonunitary_operations_cannot_be_hidden() {
    for body in [
        "h q[0]; h q[0]; reset q[0];",
        "bit c; c=measure q[0]; h q[0]; h q[0];",
        "bit c=0; if(c) h q[0];",
    ] {
        let p = parse(body);
        for strategy in strategies() {
            assert!(preprocess_with(&p, strategy).is_none(), "{body}");
        }
    }
    let mut bad = parse("h q[0]; h q[0];");
    if let StatementKind::Apply { qubits, .. } = &mut bad.body.statements[0].kind {
        qubits[0].index = 99;
    }
    assert!(preprocess_with(&bad, Strategy::Wire).is_none());
    let mut bad = parse("rx(pi) q[0]; rx(-pi) q[0];");
    let mut ids = AstIdGenerator::starting_at(bad.ast_id_bound());
    let one = ids.node(NumericExprKind::Rational(rational(1, 1)));
    let zero = ids.node(NumericExprKind::Rational(rational(0, 1)));
    let bad_angle = ids.node(NumericExprKind::Div(Box::new(one), Box::new(zero)));
    let second = ids.clone_numeric_expr(&bad_angle);
    let negative = ids.node(NumericExprKind::Neg(Box::new(second)));
    for (statement, angle) in bad.body.statements.iter_mut().zip([bad_angle, negative]) {
        if let StatementKind::Apply { parameters, .. } = &mut statement.kind {
            parameters[0] = angle;
        }
    }
    for strategy in strategies() {
        assert!(preprocess_with(&bad, strategy).is_none());
    }
}

#[test]
fn classical_writes_scopes_and_declarations_are_retained() {
    let p = parse("bit c=1; def pair(qubit a) { h a; h a; } pair(q[0]); x q[1]; x q[1];");
    for strategy in strategies() {
        let out = preprocess_with(&p, strategy).unwrap();
        assert_eq!(out.classical_registers, p.classical_registers);
        assert_eq!(out.quantum_registers, p.quantum_registers);
        assert!(matches!(
            out.body.statements[0].kind,
            StatementKind::Assign { .. }
        ));
        assert_eq!(matrix(&out), matrix(&p));
    }
}

#[test]
fn wire_index_skips_irrelevant_gates_beyond_the_scan_window() {
    let body = format!("h q[0]; {} h q[0];", "x q[1]; z q[1];".repeat(200));
    let source = parse(&body);
    let scan = preprocess_with(&source, Strategy::Scan).unwrap_or_else(|| source.clone());
    let wire = preprocess_with(&source, Strategy::Wire).unwrap();
    assert_eq!(source.operation_count() - wire.operation_count(), 2);
    assert_eq!(scan.operation_count(), source.operation_count());
}
