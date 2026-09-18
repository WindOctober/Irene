use irene::frontend::openqasm2;
use irene::ir::{Block, NumericExprKind, StatementKind};

fn values(block: &Block, out: &mut Vec<String>) {
    for s in &block.statements {
        match &s.kind {
            StatementKind::Scope(b) => values(b, out),
            StatementKind::Apply { parameters, .. } => {
                for p in parameters {
                    match &p.kind {
                        NumericExprKind::Rational(r) => out.push(r.to_string()),
                        _ => panic!("expected an exact rational"),
                    }
                }
            }
            _ => {}
        }
    }
}
#[test]
fn scientific_literals_are_exact() {
    for (literal, expected) in [
        ("5.e-05", "1/20000"),
        ("5.E+2", "500"),
        ("5.0e-05", "1/20000"),
        ("5e-5", "1/20000"),
        (".5e-4", "1/20000"),
        ("0.e+10", "0"),
    ] {
        let p = openqasm2::parse_str(
            &format!("OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; rz({literal}) q[0];"),
            "test",
        )
        .unwrap();
        let mut actual = Vec::new();
        values(&p.body, &mut actual);
        assert_eq!(actual, vec![expected], "{literal}");
    }
    for literal in ["5.e-", "5.e+", "5.e", "5.e-05foo", "5.e--05"] {
        assert!(
            openqasm2::parse_str(
                &format!("OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; rz({literal}) q[0];"),
                "test"
            )
            .is_err(),
            "{literal}"
        );
    }
}
