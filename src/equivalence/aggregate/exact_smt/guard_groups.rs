//! Sufficient certificates for complete sums grouped by identical guards.
//! Guards need not be disjoint. A failed group NEVER certifies inequality:
//! contributions in other overlapping groups can cancel its difference.
use super::*;

impl Power {
    pub(super) fn form(&self) -> Option<PhaseForm> {
        match self {
            Self::Constant(c) => Some(PhaseForm {
                constant: *c,
                ..PhaseForm::default()
            }),
            Self::Structured(_, _, form) => Some((**form).clone()),
            Self::Expr(..) => None,
        }
    }
}

impl PhaseForm {
    pub(super) fn add(&mut self, selector: KernelBooleanPolynomial, coefficient: u64) {
        let selector = KernelBooleanPolynomial::from_graph(selector.as_graph().factored());
        let c = coefficient % ORDER;
        if selector.is_zero() || c == 0 {
            return;
        }
        if selector.is_one() {
            self.constant = (self.constant + c) % ORDER;
            return;
        }
        let value = (self.selectors.remove(&selector).unwrap_or(0) + c) % ORDER;
        if value != 0 {
            self.selectors.insert(selector, value);
        }
    }

    pub(super) fn combine(mut self, other: Self, subtract: bool) -> Self {
        let coefficient = |c| if subtract { (ORDER - c) % ORDER } else { c };
        self.constant = (self.constant + coefficient(other.constant)) % ORDER;
        for (s, c) in other.selectors {
            self.add(s, coefficient(c));
        }
        self
    }
}

impl Encoder {
    pub(super) fn normalize_factor_contents(
        &mut self,
        left: &mut [Polynomial],
        right: &mut [Polynomial],
    ) -> Option<()> {
        let mut contents = Vec::new();
        for factors in [&mut *left, &mut *right] {
            let mut content = integer(1);
            for factor in factors {
                let mut numerator = BigInt::from(0);
                let mut denominator = BigInt::from(1);
                for atom in factor.iter() {
                    numerator = gcd(
                        numerator,
                        BigInt::from(atom.weight.numer().magnitude().clone()),
                    );
                    denominator = (&denominator
                        / gcd(denominator.clone(), atom.weight.denom().clone()))
                        * atom.weight.denom();
                    if denominator.bits() > MAX_BITS {
                        return None;
                    }
                }
                if numerator == BigInt::from(0) {
                    return None;
                }
                let factor_content = BigRational::new(numerator, denominator);
                for atom in factor {
                    atom.weight /= &factor_content;
                }
                content *= factor_content;
                if content.numer().bits() > MAX_BITS || content.denom().bits() > MAX_BITS {
                    return None;
                }
            }
            contents.push(content);
        }
        let ratio = &contents[1] / &contents[0];
        if ratio != integer(1) {
            let index = right.iter().position(|p| p.len() > 1).unwrap_or(0);
            for atom in right.get_mut(index)? {
                atom.weight *= &ratio;
            }
        }
        Some(())
    }

    pub(super) fn relative_product_phases(
        &mut self,
        left: &mut [Polynomial],
        right: &mut [Polynomial],
    ) -> Option<()> {
        let mut phases = Vec::new();
        for factors in [&mut *left, &mut *right] {
            let mut phase = Power::Constant(0);
            for factor in factors {
                if let [atom] = factor.as_mut_slice() {
                    phase = self.plus_power(phase, atom.power.clone())?;
                    // Keep the guard, weight and radical, including zero weights.
                    atom.power = Power::Constant(0);
                }
            }
            phases.push(phase);
        }
        let delta = self.relative_power(phases[1].clone(), &phases[0])?;
        if delta != Power::Constant(0) {
            // Prefer a sum factor to retain direct matching of common guarded
            // singleton factors. This is an exact identity, not path alignment.
            let default = right.iter().position(|p| p.len() > 1).unwrap_or(0);
            let supports: Vec<BTreeSet<_>> = left
                .iter()
                .zip(right.iter())
                .map(|(a, b)| {
                    a.iter()
                        .chain(b)
                        .filter_map(|a| a.power.form())
                        .flat_map(|f| f.selectors.into_keys().flat_map(|p| p.variables()))
                        .collect()
                })
                .collect();
            let mut pieces = Vec::new();
            if let Some(form) = delta.form() {
                if form.constant != 0 {
                    pieces.push((BTreeSet::new(), Power::Constant(form.constant)));
                }
                for (selector, c) in form.selectors {
                    let parts: Vec<_> = if c == HALF {
                        selector
                            .as_graph()
                            .xor_terms()
                            .into_iter()
                            .map(KernelBooleanPolynomial::from_graph)
                            .collect()
                    } else {
                        vec![selector]
                    };
                    for p in parts {
                        let support = p.variables();
                        let mut form = PhaseForm::default();
                        form.add(p, c);
                        pieces.push((support, self.lower_phase_form(form)?));
                    }
                }
            } else {
                pieces.push((BTreeSet::new(), delta));
            }
            for (support, power) in pieces {
                // Keep ket-/bra-local phase differences with their respective
                // sum factors whenever support establishes an exact placement.
                let index = supports
                    .iter()
                    .enumerate()
                    .filter(|(i, s)| right[*i].len() > 1 && support.is_subset(s))
                    .min_by_key(|(_, s)| s.len())
                    .map(|(i, _)| i)
                    .unwrap_or(default);
                for atom in right.get_mut(index)? {
                    atom.power = self.plus_power(atom.power.clone(), power.clone())?;
                }
            }
        }
        Some(())
    }

    pub(super) fn lower_phase_form(&mut self, form: PhaseForm) -> Option<Power> {
        // Extract ALL half-turn parts, even in a mixed-denominator phase.
        // HALF*(f+g) == HALF*(f XOR g) modulo ORDER; no ANF expansion.
        let mut normalized = PhaseForm {
            constant: form.constant % ORDER,
            ..PhaseForm::default()
        };
        let mut parity = crate::symbolic::BooleanPolynomial::zero();
        for (s, c) in form.selectors {
            self.charge(1)?;
            if c >= HALF {
                parity = parity.xor(&s.as_graph());
            }
            normalized.add(s, c % HALF);
        }
        normalized.add(KernelBooleanPolynomial::from_graph(parity.factored()), HALF);
        // Admission may fix bound variables. Retain only selectors which
        // actually survive lowering, so the cached text and form agree.
        let mut retained = PhaseForm {
            constant: normalized.constant,
            ..PhaseForm::default()
        };
        let mut terms = Vec::new();
        let mut stride = ORDER;
        for (s, c) in normalized.selectors {
            let g = self.boolean(&s)?;
            match g.as_str() {
                "false" => continue,
                "true" => retained.constant = (retained.constant + c) % ORDER,
                _ => {
                    stride = stride.min(1u64 << c.trailing_zeros().min(62));
                    terms.push(self.define(
                        "(_ BitVec 62)",
                        format!("(ite {g} (_ bv{c} 62) (_ bv0 62))"),
                    )?);
                    retained.selectors.insert(s, c);
                }
            }
        }
        if terms.is_empty() {
            return Some(Power::Constant(retained.constant));
        }
        stride = stride.min(Power::Constant(retained.constant).step());
        if retained.constant != 0 {
            terms.push(Power::Constant(retained.constant).text());
        }
        let mut text = terms.remove(0);
        for next in terms {
            text = self.define("(_ BitVec 62)", format!("(bvadd {text} {next})"))?;
        }
        Some(Power::Structured(
            text,
            stride,
            std::sync::Arc::new(retained),
        ))
    }

    pub(super) fn relative_power(&mut self, value: Power, anchor: &Power) -> Option<Power> {
        if value == *anchor {
            return Some(Power::Constant(0));
        }
        if *anchor == Power::Constant(0) {
            return Some(value);
        }
        if let (Some(a), Some(b)) = (value.form(), anchor.form()) {
            return self.lower_phase_form(a.combine(b, true));
        }
        Some(Power::Expr(
            self.define(
                "(_ BitVec 62)",
                format!("(bvsub {} {})", value.text(), anchor.text()),
            )?,
            value.step().min(anchor.step()),
        ))
    }

    pub(super) fn prove_guard_groups(
        &self,
        a: &Polynomial,
        b: &Polynomial,
        domain: &[String],
    ) -> Option<crate::equivalence::smt::PortfolioResult> {
        if !crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
            return None;
        }
        fn groups(p: &Polynomial) -> BTreeMap<String, Polynomial> {
            let mut groups = BTreeMap::<String, Polynomial>::new();
            for atom in p {
                if atom.guard != "false" && atom.weight != integer(0) {
                    groups
                        .entry(atom.guard.clone())
                        .or_default()
                        .push(atom.clone());
                }
            }
            groups
        }
        let a = groups(a);
        let b = groups(b);
        // Only directly identical guards are matched here. No quadratic search
        // for semantic matches and no assumption that the groups are disjoint.
        if a.len() > 128 || !a.keys().eq(b.keys()) {
            return None;
        }
        let debug = std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some();
        if debug {
            eprintln!(
                "density exact SMT guarded certificate: {} matched groups",
                a.len()
            );
        }
        let started = std::time::Instant::now();
        let mut results = Vec::new();
        for (guard, left) in a {
            let right = &b[&guard];
            if left == *right {
                continue;
            }
            if started.elapsed() >= crate::equivalence::smt::solver_timeout() {
                return None;
            }
            let mut encoder = self.clone();
            let anchor = left.first()?.power.clone();
            let mut difference = Vec::new();
            for (sign, terms) in [(1, &left), (-1, right)] {
                for atom in terms {
                    let mut atom = atom.clone();
                    // Divide BOTH sides by the SAME unit phase. Never remove
                    // unrelated phases separately, nor any possibly zero weight.
                    atom.power = encoder.relative_power(atom.power, &anchor)?;
                    atom.guard = "true".into();
                    atom.weight *= integer(sign);
                    difference.push(atom);
                }
            }
            let difference = encoder.compact(difference)?;
            if difference.is_empty() {
                continue;
            }
            let stride = difference.iter().fold(HALF, |s, a| s.min(a.power.step()));
            let degree = (HALF / stride) as usize;
            let mut query = if degree <= 8 && difference.iter().all(|a| !a.radical) {
                encoder.dense_product_query(vec![difference], vec![Vec::new()], degree)?
            } else {
                encoder.query(difference)?
            };
            query.script = query.script.replace(
                "(check-sat)",
                &format!("{}(assert {guard})\n(check-sat)", domain.join("")),
            );
            let result = run_solver(Solver::Bitwuzla, &query.script);
            if debug {
                eprintln!(
                    "density exact SMT guarded group: {guard} {:?}",
                    result.status
                );
            }
            if result.status != SolverStatus::Unsat {
                return None;
            }
            results.push(result);
        }
        Some(crate::equivalence::smt::PortfolioResult {
            consensus: crate::equivalence::smt::PortfolioConsensus::Unsat,
            results,
        })
    }
}
