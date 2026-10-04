//! Shared Boolean XAG construction and structure-preserving SMT lowering.
use std::collections::BTreeMap;

pub(crate) mod davio;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Network {
    pub inputs: u32,
    /// 0=constant, 1=input, 2=XOR, 3=AND. Child indices precede parents.
    pub nodes: Vec<[u32; 3]>,
    pub outputs: Vec<u32>,
}
impl Network {
    fn validate(&self) -> bool {
        self.inputs as usize <= self.nodes.len()
            && self
                .nodes
                .iter()
                .enumerate()
                .all(|(i, &[op, a, b])| match op {
                    0 => a <= 1,
                    1 => a < self.inputs,
                    2 | 3 => (a as usize) < i && (b as usize) < i,
                    _ => false,
                })
            && self
                .outputs
                .iter()
                .all(|&i| (i as usize) < self.nodes.len())
    }
    /// Each gate gets one definition. No distribution or recursive text expansion.
    pub(crate) fn smt(&self, names: &[String], prefix: &str) -> Option<(String, Vec<String>)> {
        if !self.validate() || names.len() != self.inputs as usize {
            return None;
        }
        let mut script = String::new();
        let mut values = Vec::new();
        for (i, &[op, a, b]) in self.nodes.iter().enumerate() {
            let expression = match op {
                0 => (a != 0).to_string(),
                1 => names[a as usize].clone(),
                2 | 3 => format!(
                    "({} {} {})",
                    if op == 2 { "xor" } else { "and" },
                    values[a as usize],
                    values[b as usize]
                ),
                _ => unreachable!(),
            };
            let name = format!("{prefix}{i}");
            script.push_str(&format!("(define-fun {name} () Bool {expression})\n"));
            values.push(name);
        }
        Some((
            script,
            self.outputs
                .iter()
                .map(|&i| values[i as usize].clone())
                .collect(),
        ))
    }
}

#[derive(Default)]
pub(crate) struct Builder {
    pub network: Network,
    unique: BTreeMap<[u32; 3], u32>,
}
impl Builder {
    pub fn node(&mut self, op: u32, mut a: u32, mut b: u32) -> u32 {
        if op >= 2 && a > b {
            std::mem::swap(&mut a, &mut b);
        }
        let key = [op, a, b];
        if let Some(&i) = self.unique.get(&key) {
            return i;
        }
        let i = u32::try_from(self.network.nodes.len()).expect("XAG exceeds address space");
        self.network.nodes.push(key);
        self.unique.insert(key, i);
        i
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowering_keeps_unused_inputs_and_shared_complemented_outputs() {
        let net = Network {
            inputs: 3,
            nodes: vec![[1, 0, 0], [1, 1, 0], [1, 2, 0], [0, 1, 0], [2, 0, 3]],
            outputs: vec![4, 0, 4],
        };
        let (script, outputs) = net.smt(&["a".into(), "b".into(), "c".into()], "g").unwrap();
        assert_eq!(outputs, ["g4", "g0", "g4"]);
        assert_eq!(
            script,
            concat!(
                "(define-fun g0 () Bool a)\n",
                "(define-fun g1 () Bool b)\n",
                "(define-fun g2 () Bool c)\n",
                "(define-fun g3 () Bool true)\n",
                "(define-fun g4 () Bool (xor g0 g3))\n",
            )
        );
        assert!(net.smt(&[], "g").is_none());
    }

    #[test]
    fn builder_shares_commutative_gates_without_expansion() {
        let mut builder = Builder::default();
        builder.network.inputs = 2;
        let a = builder.node(1, 0, 0);
        let b = builder.node(1, 1, 0);
        for op in [2, 3] {
            assert_eq!(builder.node(op, a, b), builder.node(op, b, a));
        }
        assert_eq!(builder.network.nodes.len(), 4);
        builder.network.outputs = vec![2, 3];
        let (script, outputs) = builder.network.smt(&["a".into(), "b".into()], "g").unwrap();
        assert_eq!(script.lines().count(), 4);
        assert!(script.contains("(and g0 g1)"));
        assert_eq!(outputs, ["g2", "g3"]);
    }

    #[test]
    fn malformed_graphs_are_rejected_before_lowering() {
        for node in [[2, 0, 0], [3, 1, 0], [1, 0, 0], [0, 2, 0], [4, 0, 0]] {
            let net = Network {
                inputs: 0,
                nodes: vec![node],
                outputs: vec![0],
            };
            assert!(net.smt(&[], "g").is_none());
        }
        let net = Network {
            inputs: 0,
            nodes: vec![[0, 0, 0]],
            outputs: vec![1],
        };
        assert!(net.smt(&[], "g").is_none());
    }

    #[test]
    fn constant_and_empty_graphs_lower_without_inputs() {
        let net = Network {
            inputs: 0,
            nodes: vec![[0, 0, 0], [0, 1, 0]],
            outputs: vec![0, 1],
        };
        let (script, outputs) = net.smt(&[], "g").unwrap();
        assert_eq!(outputs, ["g0", "g1"]);
        assert_eq!(
            script,
            "(define-fun g0 () Bool false)\n(define-fun g1 () Bool true)\n"
        );
        assert_eq!(
            Network::default().smt(&[], "g"),
            Some((String::new(), Vec::new()))
        );
    }
}
