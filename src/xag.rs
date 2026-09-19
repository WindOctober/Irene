//! Shared Boolean XAG construction for local exact normalization.
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
