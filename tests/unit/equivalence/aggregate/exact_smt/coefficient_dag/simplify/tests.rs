use super::*;
#[test]
fn guarded_context_cancels_actual_add_shape_without_changing_shared_functions() {
    let mut d = Dag::new();
    d.simplify = false;
    let p: Vec<_> = (0..4)
        .map(|i| KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(i)))
        .collect();
    let abc = p[0].and(&p[1]).and(&p[2]);
    let ac = d
        .select(
            p[1].and(&p[2])
                .complement()
                .and(&p[0].and(&p[1]).complement()),
            1,
            0,
        )
        .unwrap();
    let abc = d.select(abc, 1, 0).unwrap();
    let minus = d.scale(abc, integer(-1)).unwrap();
    let a = d.add(ac, minus).unwrap();
    let b = d.select(p[1].and(&p[0].xor(&p[2])), 1, 0).unwrap();
    let b = d.scale(b, integer(-1)).unwrap();
    let bd = d.select(p[1].and(&p[3]), 1, 0).unwrap();
    let not_bd = d.select(p[1].and(&p[3]).complement(), 1, 0).unwrap();
    let not_b = d.select(p[1].complement(), 1, 0).unwrap();
    let x = d.multiply(bd, a).unwrap();
    let x = d.scale(x, integer(-1)).unwrap();
    let y = d.multiply(not_bd, b).unwrap();
    let sum = d.add(x, y).unwrap();
    let n = d.multiply(not_b, sum).unwrap();
    let x = d.multiply(not_bd, a).unwrap();
    let y = d.multiply(bd, b).unwrap();
    let sum = d.add(x, y).unwrap();
    let m = d.multiply(not_b, sum).unwrap();
    let roots = [n, m, a, b];
    let (out, rs) = d.simplified(roots).unwrap();
    assert_eq!(rs[0], 0);
    assert_eq!(out.indicator(rs[1]), Some(p[1].complement()));
    for bits in 0..16 {
        assert_eq!(eval(&d, roots, bits), eval(&out, rs, bits));
    }
    // These real local coefficients are also orthogonal/normalized.
    // Keep the semantic regression even before a rewrite recognizes it.
    let ab = d.multiply(a, b).unwrap();
    let aa = d.multiply(a, a).unwrap();
    let bb = d.multiply(b, b).unwrap();
    let norm = d.add(aa, bb).unwrap();
    let (out, rs) = d.simplified([ab, norm, 0, 0]).unwrap();
    eprintln!(
        "coefficient identities reduced: AB=0 {} A2+B2=1 {}",
        rs[0] == 0,
        rs[1] == 1
    );
    for bits in 0..16 {
        assert_eq!(
            eval(&out, rs, bits),
            vec![integer(0), integer(1), integer(0), integer(0)]
        );
    }
}
#[test]
fn nonlinear_guard_does_not_supply_unproved_literal_assignments() {
    let mut d = Dag::new();
    d.simplify = true;
    let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
    let q = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(1));
    let x = d.select(p.clone(), 1, 0).unwrap();
    let not_both = p.and(&q).complement();
    let r = d.conditioned(x, &not_both);
    // ! (p AND q) does NOT imply !p. For p=1,q=0 the value stays 1.
    assert_eq!(eval(&d, [r, 0, 0, 0], 1)[0], integer(1));
    let positive = d.conditioned(x, &p);
    let negative = d.conditioned(x, &p.complement());
    assert_eq!(positive, 1);
    assert_eq!(negative, 0);
    assert_eq!(eval(&d, [x, 0, 0, 0], 1)[0], integer(1));
    d.context_work = 0;
    assert_eq!(d.conditioned(x, &q), x);
    // A mid-traversal refusal must not return a partially specialized root.
    let y = d.select(q.clone(), 1, 0).unwrap();
    let sum = d.node(Node::Add(x, y)).unwrap();
    let both = p.and(&q);
    d.context_work = 1;
    assert_eq!(d.conditioned(sum, &both), sum);
    // A fresh context can still prove both literals of a conjunction.
    d.context_work = 100;
    let g = p.and(&q.complement());
    assert_eq!(d.conditioned(sum, &g), 1);
}
fn eval(d: &Dag, roots: Value, bits: usize) -> Vec<BigRational> {
    let mut values: Vec<BigRational> = Vec::new();
    for n in &d.nodes {
        values.push(match n {
            Node::Constant(r) => r.clone(),
            Node::Add(a, b) => &values[*a] + &values[*b],
            Node::Multiply(a, b) => &values[*a] * &values[*b],
            Node::Scale(r, a) => r * &values[*a],
            Node::Select(p, a, b) => {
                let bit = p
                    .as_graph()
                    .evaluate::<std::convert::Infallible>(|v| {
                        let KernelVariable::QuantumOutputKet(i) =
                            KernelVariable::from_graph_variable(v)
                        else {
                            panic!("unexpected variable")
                        };
                        Ok(bits >> i & 1 != 0)
                    })
                    .unwrap();
                values[if bit { *a } else { *b }].clone()
            }
        });
    }
    roots.iter().map(|id| values[*id].clone()).collect()
}
#[test]
fn sign_indicator_and_nested_cancellation() {
    let mut d = Dag::new();
    d.simplify = true;
    let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
    let q = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(1));
    let a = d.sign_node(p.clone()).unwrap();
    let b = d.sign_node(q.clone()).unwrap();
    let ab = d.multiply(a, b).unwrap();
    assert_eq!(d.sign(ab), Some(p.xor(&q)));
    assert_eq!(d.multiply(a, a), Some(1));
    let i = d.select(p.clone(), 1, 0).unwrap();
    let product = d.multiply(i, a).unwrap();
    assert_eq!(product, d.scale(i, integer(-1)).unwrap());
    let sum = d.add(a, b).unwrap();
    let minus_a = d.scale(a, integer(-1)).unwrap();
    let residual = d.add(sum, minus_a).unwrap();
    for bits in 0..4 {
        assert_eq!(
            eval(&d, [residual, 0, 0, 0], bits),
            eval(&d, [b, 0, 0, 0], bits)
        );
    }
    let two = d.constant(integer(2)).unwrap();
    let three = d.constant(integer(3)).unwrap();
    let f = d.select(p.clone(), two, three).unwrap();
    let sum = d.add(f, b).unwrap();
    let minus_f = d.scale(f, integer(-1)).unwrap();
    assert_eq!(d.add(sum, minus_f), Some(b));
    let inner = d.select(p.clone(), a, b).unwrap();
    let outer = d.select(p.clone(), inner, 0).unwrap();
    assert_eq!(outer, d.select(p, a, 0).unwrap());
}
#[test]
fn rewrites_preserve_every_assignment_of_generated_dags() {
    for seed in 0..8u64 {
        let mut state = seed + 31;
        let mut d = Dag::new();
        d.simplify = false;
        let ps: Vec<_> = (0..3)
            .map(|i| KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(i)))
            .collect();
        let minus = d.constant(integer(-1)).unwrap();
        let frac = d.constant(ratio(2, 3)).unwrap();
        let mut nodes = vec![0, 1, minus, frac];
        for p in &ps {
            nodes.push(d.select(p.clone(), minus, 1).unwrap());
            nodes.push(d.select(p.clone(), 1, 0).unwrap());
        }
        for step in 0..80 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let a = nodes[(state >> 24) as usize % nodes.len()];
            let b = nodes[(state >> 40) as usize % nodes.len()];
            let id = match step % 4 {
                0 => d.add(a, b),
                1 => d.multiply(a, b),
                2 => d.select(ps[step % 3].clone(), a, b),
                _ => d.scale(a, ratio((step % 5) as i64 - 2, 3)),
            }
            .unwrap();
            nodes.push(id);
        }
        let roots: Value = nodes[nodes.len() - 4..].try_into().unwrap();
        let (light, result) = d.simplified(roots).unwrap();
        for bits in 0..8 {
            assert_eq!(
                eval(&d, roots, bits),
                eval(&light, result, bits),
                "seed={seed} bits={bits}"
            );
        }
    }
}
