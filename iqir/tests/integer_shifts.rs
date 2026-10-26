use iqir::{ScalarType, frontend};

#[test]
fn integer_shift_edges_and_wrapping() {
    let unsigned = ScalarType::Int {
        width: 8,
        signed: false,
    };
    assert_eq!(unsigned.checked_integer_shift(true, 200, 1), Ok(144));
    assert_eq!(unsigned.checked_integer_shift(false, 255, 2), Ok(63));
    for n in [8, 64, i128::MAX] {
        assert_eq!(unsigned.checked_integer_shift(true, 255, n), Ok(0));
        assert_eq!(unsigned.checked_integer_shift(false, 255, n), Ok(0));
    }
    assert!(unsigned.checked_integer_shift(true, 1, -1).is_err());
    let signed = ScalarType::Int {
        width: 32,
        signed: true,
    };
    assert_eq!(signed.checked_integer_shift(true, 1, 8), Ok(256));
    assert_eq!(signed.checked_integer_shift(false, 7, 1), Ok(3));
    assert!(signed.checked_integer_shift(true, 1, 31).is_err());
    assert!(signed.checked_integer_shift(false, -3, 1).is_err());
}

#[test]
fn shifts_keep_scalar_storage_and_dense_ast_ids() {
    for body in [
        "int[32] n=0; for int idx in [8:-1:0] { n += 1 << (8-idx); }",
        "uint[8] n=255; uint[8] m=n >> 2; n <<= 3; n >>= 8;",
        "uint[8] n=255; const uint[8] c=255; const uint[8] d=c<<1; n >>= 2;",
        "uint[1] n=1; n<<=64;",
    ] {
        let p =
            frontend::parse_str_with_options(&format!("OPENQASM 3; {body}"), "shift.qasm", true)
                .unwrap();
        assert!(p.classical_registers.is_empty(), "{body}");
        let mut ids = vec![];
        p.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort();
        assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    }
}

#[test]
fn shifts_fail_closed_outside_the_supported_subset() {
    for body in [
        "int[32] n=1<<31;",
        "int[32] n=(-3)>>1;",
        "uint[8] n=1; n<<=-1;",
        "uint[8] n=1; uint[8] k; n<<=k;",
        "float[64] n=1.0; n<<=1;",
    ] {
        assert!(
            frontend::parse_str_with_options(&format!("OPENQASM 3; {body}"), "shift.qasm", true)
                .is_err(),
            "{body}"
        );
    }
}
