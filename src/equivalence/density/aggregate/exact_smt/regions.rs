//! Exact, bounded free-coordinate partition certificates. This is NOT path
//! sampling: both cofactors of every selected free coordinate must be proved.
use super::*;

impl Encoder {
    pub(super) fn guard_graph(&self, name: &str) -> Option<KernelBooleanPolynomial> {
        match name {
            "true" => Some(KernelBooleanPolynomial::one()),
            "false" => Some(KernelBooleanPolynomial::zero()),
            _ => self.guards.get(name).cloned().or_else(|| {
                let i: usize = name.strip_prefix('u')?.parse().ok()?;
                Some(KernelBooleanPolynomial::variable(
                    self.coordinates.get(i)?.clone(),
                ))
            }),
        }
    }

    fn specialize_factors(
        &mut self,
        factors: &[Polynomial],
        v: &KernelVariable,
        bit: bool,
    ) -> Option<Vec<Polynomial>> {
        let replacement = KernelBooleanPolynomial::from(bit);
        factors
            .iter()
            .map(|factor| {
                let mut result = Vec::new();
                for atom in factor {
                    let guard = self.guard_graph(&atom.guard)?.substitute(v, &replacement);
                    if guard.is_zero() {
                        continue;
                    }
                    let mut atom = atom.clone();
                    atom.guard = self.boolean(&guard)?;
                    let source = atom.power.form()?;
                    let mut form = PhaseForm {
                        constant: source.constant,
                        ..PhaseForm::default()
                    };
                    for (p, c) in source.selectors {
                        form.add(p.substitute(v, &replacement), c);
                    }
                    atom.power = self.lower_phase_form(form)?;
                    result.push(atom);
                }
                self.compact(result)
            })
            .collect()
    }

    pub(super) fn prove_regions(
        &self,
        a: &[Polynomial],
        b: &[Polynomial],
    ) -> Option<crate::equivalence::solver::smt::PortfolioResult> {
        let guard_vars: BTreeSet<_> = a
            .iter()
            .chain(b)
            .flatten()
            .map(|a| self.guard_graph(&a.guard))
            .collect::<Option<Vec<_>>>()?
            .iter()
            .flat_map(KernelBooleanPolynomial::variables)
            .collect();
        if guard_vars.is_empty()
            || guard_vars.len() > 12
            || a.iter().chain(b).map(Vec::len).sum::<usize>() > 512
        {
            return None;
        }
        let mut pending = vec![(self.clone(), a.to_vec(), b.to_vec())];
        let mut results = Vec::new();
        let start = std::time::Instant::now();
        let mut nodes = 0;
        let mut leaves = 0;
        while let Some((mut e, a, b)) = pending.pop() {
            nodes += 1;
            if nodes > 512 || start.elapsed().as_secs() >= 60 {
                return None;
            }
            if a == b || (a.iter().any(Vec::is_empty) && b.iter().any(Vec::is_empty)) {
                continue;
            }
            let guards: Vec<Vec<_>> = a
                .iter()
                .chain(&b)
                .map(|p| {
                    p.iter()
                        .map(|a| e.guard_graph(&a.guard))
                        .collect::<Option<Vec<_>>>()
                })
                .collect::<Option<_>>()?;
            let vars: BTreeSet<_> = guards
                .iter()
                .flatten()
                .flat_map(KernelBooleanPolynomial::variables)
                .collect();
            if let Some(v) = vars.iter().max_by_key(|v| {
                let mut dead = 0;
                let mut constants = 0;
                for bit in [false, true] {
                    let rhs = KernelBooleanPolynomial::from(bit);
                    for factor in &guards {
                        let simplified: Vec<_> =
                            factor.iter().map(|p| p.substitute(v, &rhs)).collect();
                        dead += usize::from(
                            !factor.is_empty()
                                && simplified.iter().all(KernelBooleanPolynomial::is_zero),
                        );
                        constants += simplified
                            .iter()
                            .filter(|p| p.is_zero() || p.is_one())
                            .count();
                    }
                }
                (dead, constants)
            }) {
                if v.is_bound_path() {
                    return None;
                }
                for bit in [false, true] {
                    let mut child = e.clone();
                    let left = child.specialize_factors(&a, v, bit)?;
                    let right = child.specialize_factors(&b, v, bit)?;
                    pending.push((child, left, right));
                }
                continue;
            }
            leaves += 1;
            let mut a = a;
            let mut b = b;
            e.relative_product_phases(&mut a, &mut b)?;
            let stride = a
                .iter()
                .chain(&b)
                .flatten()
                .fold(HALF, |s, a| s.min(a.power.step()));
            let degree = (HALF / stride) as usize;
            if degree > 8 || a.iter().chain(&b).flatten().any(|a| a.radical) {
                return None;
            }
            if let Some(proof) = e.prove_factor_products(&a, &b, degree) {
                results.extend(proof.results);
                continue;
            }
            let query = e.dense_product_query(a, b, degree)?;
            let r = run_solver(Solver::Bitwuzla, &query.script);
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "scheduled region leaf={leaves} nodes={nodes} status={:?} seconds={:.3}",
                    r.status,
                    r.duration.as_secs_f64()
                );
            }
            if r.status != SolverStatus::Unsat {
                return None;
            }
            results.push(r);
        }
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "scheduled regions complete: nodes={nodes} leaves={leaves} queries={} seconds={:.3}",
                results.len(),
                start.elapsed().as_secs_f64()
            );
        }
        Some(crate::equivalence::solver::smt::PortfolioResult {
            consensus: crate::equivalence::solver::smt::PortfolioConsensus::Unsat,
            results,
        })
    }
}
