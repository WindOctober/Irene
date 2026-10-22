use iqir::frontend;

fn parse(source: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(&format!("OPENQASM 3; {source}"), "casts.qasm")
        .map_err(|e| e.to_string())
}

#[test]
fn bit_casts_and_lossless_widening_have_dense_ids() {
    for source in [
        "bit[4] b; int[4] n=int[4](b);",
        "bit[4] b; int[32] n=int[32](uint[4](b));",
        "bit[4] b; int[32] n=int[32](int[4](b));",
        "bit[64] b; int[64] n=int[64](b);",
        "bit[1] b; int[1] n=int[1](b);",
        "int[8] n=-2; int[32] m=int[32](n);",
        "bit[4] b; uint[4] n=uint[4](b); int[32] m=int[32](n);",
        "int[32] n=int[32](2);",
    ] {
        let p = parse(source).unwrap_or_else(|e| panic!("{source}: {e}"));
        let mut ids = vec![];
        p.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort();
        assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>(), "{source}");
    }
}

#[test]
fn unsupported_or_illegal_conversions_are_not_silently_reinterpreted() {
    for source in [
        "bit[4] b; int[32] n=int[32](b);",
        "bit[4] b; int[2] n=int[2](b);",
        "bit[4] b; int[4] n=int[4](uint[4](b));",
        "int[8] a=-1; uint[16] b=uint[16](a);",
        "int[32] a=1; int[8] b=int[8](a);",
        "bit[65] b; int[65] n=int[65](b);",
    ] {
        assert!(parse(source).is_err(), "unexpected success: {source}");
    }
}

#[test]
fn cross_width_bit_casts_are_rejected_in_values_and_conditions() {
    for source in [
        "bit[4] b; uint[32] n=uint[32](b);",
        "bit[4] b; uint[2] n=uint[2](b);",
        "bit[4] b; int[32] n=0; n=int[32](b);",
        "bit[4] b; bool flag=int[32](b)==0;",
        "bit[4] b; if(uint[32](b)==0) {}",
        "bit[4] b=\"1111\"; int[32] n=int[32](b);",
    ] {
        let error = parse(source).expect_err(source);
        assert!(
            error.contains("matching its bit width"),
            "{source}: {error}"
        );
    }
}
