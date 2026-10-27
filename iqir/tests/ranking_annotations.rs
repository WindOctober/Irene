use iqir::annotation::{AnnotationKind, AnnotationPayload, TerminationKind};

#[test]
fn ranking_proof_is_a_typed_boolean_loop_clause() {
    let p = iqir::frontend::parse_str(
        "OPENQASM 3; int n=2; qubit q;\n@saria.ranking_function n\n@saria.ranking_proof n >= 0\n@saria.ranking_proof q == |0>\nwhile(n>0){n-=1;}",
        "region.qasm",
    ).unwrap();
    assert_eq!(
        p.annotations
            .values()
            .flatten()
            .filter(|a| a.kind == AnnotationKind::RankingProof)
            .count(),
        2
    );
    for value in ["n", "1.0", "q"] {
        let s = format!(
            "OPENQASM 3; int n=2; qubit q;\n@saria.ranking_proof {value}\nwhile(n>0){{n-=1;}}"
        );
        assert!(iqir::frontend::parse_str(&s, "bad-region.qasm").is_err());
    }
    assert!(iqir::frontend::parse_str(
        "OPENQASM 3; int n=2;\n@saria.ranking_proof true\nn-=1;",
        "bad-region.qasm"
    )
    .is_err());
}

#[test]
fn integer_ranking_and_positive_mode_are_typed_loop_annotations() {
    let p = iqir::frontend::parse_str(
        "OPENQASM 3; int[32] n=100;\n@saria.ranking_function n - 1\n@saria.terminates positive_probability\nwhile(n>0){n-=1;}",
        "rank.qasm",
    ).unwrap();
    let a: Vec<_> = p.annotations.values().flatten().collect();
    assert!(a.iter().any(|a| a.kind == AnnotationKind::RankingFunction));
    assert!(
        a.iter()
            .any(|a| a.payload
                == AnnotationPayload::Termination(TerminationKind::PositiveProbability))
    );
    for rank in ["true", "1.0", "\\real(n)"] {
        let s =
            format!("OPENQASM 3; int n=2;\n@saria.ranking_function {rank}\nwhile(n>0){{n-=1;}}");
        assert!(iqir::frontend::parse_str(&s, "bad.qasm").is_err());
    }
}
