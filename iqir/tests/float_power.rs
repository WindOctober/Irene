use iqir::{AstIdGenerator, ScalarArithmetic, ScalarExprData, ScalarExprKind, ScalarType, ScalarValue};

fn power(base: ScalarValue, exponent: f64, ty: ScalarType) -> ScalarValue {
    let mut ids = AstIdGenerator::default();
    let left = ids.node(ScalarExprData { ty, kind: base.expression() });
    let exponent = if ty.width() == 32 { ScalarValue::Float32((exponent as f32).to_bits()) }
        else { ScalarValue::Float64(exponent.to_bits()) };
    let right = ids.node(ScalarExprData { ty, kind: exponent.expression() });
    ids.node(ScalarExprData { ty, kind: ScalarExprKind::Binary {
        op: ScalarArithmetic::Pow, left: Box::new(left), right: Box::new(right),
    }}).constant_value().unwrap().unwrap()
}

#[test]
fn special_power_matches_one_round_including_zero_infinity_and_nan_profile() {
    for width in [32,64] {
        let ty = ScalarType::Float { width };
        for bits in [0, 1, 0x8000_0000_0000_0000, 0x3ff0_0000_0000_0001,
            0x3fb9_9999_9999_999a, 0x7fef_ffff_ffff_ffff, 0x7ff0_0000_0000_0000,
            0xfff0_0000_0000_0000, 0x7ff8_0000_0000_1234, 0xfff8_0000_0000_4567] {
            let v = f64::from_bits(bits);
            let base = if width==32 { ScalarValue::Float32((v as f32).to_bits()) } else { ScalarValue::Float64(bits) };
            for exponent in [0.0,1.0,2.0,-1.0] {
                let expected = if v.is_nan() && exponent != 0.0 { ScalarValue::power_nan(ty).unwrap() }
                    else if width == 32 {
                        let v=v as f32;
                        ScalarValue::Float32((if exponent==0.0 {1.0} else if exponent==1.0 {v}
                            else if exponent==2.0 {v*v} else {1.0/v}).to_bits())
                    } else { ScalarValue::Float64((if exponent==0.0 {1.0} else if exponent==1.0 {v}
                        else if exponent==2.0 {v*v} else {1.0/v}).to_bits()) };
                assert_eq!(power(base,exponent,ty), expected, "{width}: {base:?} ^ {exponent}");
            }
        }
    }
}
