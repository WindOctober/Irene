use super::*;
#[test]
fn invalid_graphs_and_exhausted_budgets_return_no_rewrite() {
    let malformed = Network {
        inputs: 0,
        nodes: vec![[2, 0, 0]],
        outputs: vec![0],
    };
    assert!(normalize(&malformed, Order::Forward, 100, 100).is_none());
    let original = Network {
        inputs: 2,
        nodes: vec![[1, 0, 0], [1, 1, 0], [3, 0, 1]],
        outputs: vec![2],
    };
    assert!(normalize(&original, Order::Forward, 100, 4).is_none());
    assert!(normalize(&original, Order::Forward, 3, 100).is_none());
    let n = normalize(&original, Order::Forward, 100, 100).unwrap();
    assert_eq!(evaluate(&n, 0), vec![false]);
    assert_eq!(evaluate(&n, 3), vec![true]);
}
fn evaluate(n: &Network, assignment: u64) -> Vec<bool> {
    let mut v = vec![];
    for &[op, a, b] in &n.nodes {
        v.push(match op {
            0 => a != 0,
            1 => assignment & (1 << a) != 0,
            2 => v[a as usize] ^ v[b as usize],
            3 => v[a as usize] & v[b as usize],
            _ => unreachable!(),
        });
    }
    n.outputs.iter().map(|&i| v[i as usize]).collect()
}
#[test]
fn exhaustive_small_graphs_preserve_all_outputs_and_orders() {
    let mut seed = 73u64;
    for _ in 0..100 {
        let mut b = Builder::default();
        b.network.inputs = 5;
        for i in 0..5 {
            b.node(1, i, 0);
        }
        b.node(0, 0, 0);
        b.node(0, 1, 0);
        for _ in 0..60 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let len = b.network.nodes.len() as u64;
            let a = (seed % len) as u32;
            let c = ((seed >> 17) % len) as u32;
            let root = b.node(2 + ((seed >> 41) & 1) as u32, a, c);
            b.network.outputs.push(root);
        }
        for order in [Order::Forward, Order::Reverse] {
            let normalized = normalize(&b.network, order, 1_000_000, 50_000).unwrap();
            for assignment in 0..32 {
                assert_eq!(
                    evaluate(&b.network, assignment),
                    evaluate(&normalized, assignment)
                );
            }
        }
        for &root in &b.network.outputs {
            let mut single = b.network.clone();
            single.outputs = vec![root];
            let mut work = 100_000;
            let result = affine(&single, &mut work, 10_000).unwrap();
            let constant = evaluate(&single, 0)[0];
            let inputs: Vec<_> = (0..5)
                .filter(|i| evaluate(&single, 1 << i)[0] != constant)
                .collect();
            let is_affine = (0..32).all(|assignment| {
                let expected = inputs
                    .iter()
                    .fold(constant, |v, i| v ^ (assignment & (1 << i) != 0));
                evaluate(&single, assignment)[0] == expected
            });
            assert_eq!(result.is_some(), is_affine);
            if let Some((c, vars)) = result {
                assert_eq!(c, constant);
                assert_eq!(
                    vars.into_iter().collect::<std::collections::BTreeSet<_>>(),
                    inputs.into_iter().collect()
                );
            }
        }
        assert!(normalize(&b.network, Order::Forward, 0, 0).is_none());
    }
}

#[test]
fn affine_recognition_is_not_limited_by_input_count_or_call_stack() {
    let mut b = Builder::default();
    b.network.inputs = 1500;
    let mut root = b.node(0, 1, 0);
    for i in 0..1500 {
        let v = b.node(1, i, 0);
        root = b.node(2, root, v);
    }
    b.network.outputs = vec![root];
    let (constant, inputs) = affine(&b.network, &mut 100_000, 10_000).unwrap().unwrap();
    assert!(constant);
    assert_eq!(inputs.len(), 1500);
    assert!(affine(&b.network, &mut 10, 10_000).is_none());
    assert!(affine(&b.network, &mut 100_000, 10).is_none());
}
#[test]
fn wide_distributivity_and_idempotence_cancel_without_truth_tables() {
    let mut b = Builder::default();
    b.network.inputs = 64;
    let inputs: Vec<_> = (0..64).map(|i| b.node(1, i, 0)).collect();
    let mut left = b.node(0, 0, 0);
    let mut right = left;
    for i in 1..63 {
        let xy = b.node(2, inputs[i], inputs[i + 1]);
        let xy = b.node(3, inputs[0], xy);
        left = b.node(2, left, xy);
        let x = b.node(3, inputs[0], inputs[i]);
        let y = b.node(3, inputs[0], inputs[i + 1]);
        let xy = b.node(2, x, y);
        right = b.node(2, right, xy);
    }
    let square = b.node(3, left, left);
    let difference = b.node(2, square, right);
    b.network.outputs = vec![difference, inputs[63]];
    for order in [Order::Forward, Order::Reverse] {
        let n = normalize(&b.network, order, 1_000_000, 50_000).unwrap();
        assert_eq!(n.nodes[n.outputs[0] as usize], [0, 0, 0]);
        assert_eq!(n.nodes[n.outputs[1] as usize], [1, 63, 0]);
    }
}
