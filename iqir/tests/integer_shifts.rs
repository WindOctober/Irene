use iqir::ScalarType;

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
