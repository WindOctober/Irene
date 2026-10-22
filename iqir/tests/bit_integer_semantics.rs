use iqir::{
    AstIdGenerator, ClassicalBit, ClassicalExprKind as B, ScalarExpr, ScalarExprData,
    ScalarExprKind as E, ScalarType as T, ScalarValue as V, SymbolId,
};

fn bits(ids: &mut AstIdGenerator, width: u32, signed: bool, raw: u64) -> ScalarExpr {
    let bits = (0..width)
        .map(|i| ids.node(B::Bool(raw & (1u64 << i) != 0)))
        .collect();
    ids.node(ScalarExprData {
        ty: T::Int { width, signed },
        kind: E::FromBits(bits),
    })
}

#[test]
fn all_small_patterns_and_64_bit_edges_have_exact_values() {
    let mut ids = AstIdGenerator::default();
    for width in 1..=8 {
        for raw in 0..(1u64 << width) {
            for signed in [false, true] {
                let expected = if signed && raw >= 1 << (width - 1) {
                    raw as i128 - (1i128 << width)
                } else {
                    raw as i128
                };
                let value = bits(&mut ids, width, signed, raw);
                assert_eq!(value.constant_value(), Ok(Some(V::Integer(expected))));
                let wide = ids.node(ScalarExprData {
                    ty: T::Int { width: 64, signed },
                    kind: E::IntWiden(Box::new(value)),
                });
                assert_eq!(wide.constant_value(), Ok(Some(V::Integer(expected))));
            }
        }
    }
    for (signed, raw, expected) in [
        (false, u64::MAX, u64::MAX as i128),
        (true, u64::MAX, -1),
        (true, 1u64 << 63, i64::MIN as i128),
        (true, i64::MAX as u64, i64::MAX as i128),
    ] {
        assert_eq!(
            bits(&mut ids, 64, signed, raw).constant_value(),
            Ok(Some(V::Integer(expected)))
        );
    }
}

#[test]
fn widening_admission_matches_range_containment() {
    let bounds = |width: u32, signed: bool| {
        if signed {
            (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
        } else {
            (0, (1i128 << width) - 1)
        }
    };
    for src in 1..=64 {
        for dst in 1..=64 {
            for ss in [false, true] {
                for ds in [false, true] {
                    let (lo, hi) = bounds(src, ss);
                    let (dlo, dhi) = bounds(dst, ds);
                    assert_eq!(
                        T::Int {
                            width: dst,
                            signed: ds
                        }
                        .losslessly_contains(T::Int {
                            width: src,
                            signed: ss
                        }),
                        dlo <= lo && hi <= dhi
                    );
                }
            }
        }
    }
}

#[test]
fn unknown_bits_keep_their_storage_dependencies_when_cloned() {
    let mut ids = AstIdGenerator::default();
    let bit = ClassicalBit {
        register: SymbolId(7),
        index: 0,
    };
    let read = ids.node(B::Bit(bit.clone()));
    let value = ids.node(ScalarExprData {
        ty: T::Int {
            width: 1,
            signed: false,
        },
        kind: E::FromBits(vec![read]),
    });
    let value = ids.node(ScalarExprData {
        ty: T::Int {
            width: 32,
            signed: true,
        },
        kind: E::IntWiden(Box::new(value)),
    });
    assert_eq!(value.constant_value(), Ok(None));
    let copy = ids.clone_scalar_expr(&value);
    assert_eq!(copy.constant_value(), Ok(None));
    let mut before = vec![];
    let mut after = vec![];
    value.visit_ids(&mut |id| before.push(id));
    copy.visit_ids(&mut |id| after.push(id));
    assert_eq!(before.len(), 3);
    assert_eq!(after.len(), 3);
    assert!(before.iter().all(|id| !after.contains(id)));
    let E::IntWiden(inner) = &copy.kind.kind else {
        panic!()
    };
    let E::FromBits(reads) = &inner.kind.kind else {
        panic!()
    };
    assert_eq!(reads[0].kind, B::Bit(bit));
}

#[test]
fn malformed_bit_casts_and_lossy_widening_fail_closed() {
    let mut ids = AstIdGenerator::default();
    let mut value = bits(&mut ids, 4, false, 15);
    value.kind.ty = T::Int {
        width: 8,
        signed: false,
    };
    assert!(value.constant_value().is_err());
    value.kind.ty = T::Float { width: 64 };
    assert!(value.constant_value().is_err());
    let value = bits(&mut ids, 4, false, 15);
    let lossy = ids.node(ScalarExprData {
        ty: T::Int {
            width: 4,
            signed: true,
        },
        kind: E::IntWiden(Box::new(value)),
    });
    assert!(lossy.constant_value().is_err());
}
