//! Boolean queries restored from FSE-Ver, including Davio preprocessing.
use std::collections::BTreeMap;
use crate::ir::Qubit;
use crate::symbolic::{BooleanPolynomial, Variable};
pub(super) fn boolean_miter(
    differences: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<String> {
    let declarations = declarations(positions.len(), &[namespace]);
    let (network, variables) = BooleanPolynomial::graph_network(differences);
    let network = crate::xag::davio::preprocess(network);
    let names = variables
        .iter()
        .map(|v| match v {
            Variable::Input(q) => positions.get(q).map(|i| format!("{namespace}{i}")),
            Variable::Path(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let (definitions, terms) = network.smt(&names, "out_xag_")?;
    Some(smt_script(
        format!("{declarations}{definitions}"),
        smt_or(&terms),
        &[],
    ))
}
pub(super) fn injectivity_query(
    outputs: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
) -> Option<String> {
    let distinct_inputs = (0..positions.len())
        .map(|index| format!("(xor x{index} z{index})"))
        .collect::<Vec<_>>();
    let equal_outputs = outputs
        .iter()
        .map(|output| {
            Some(format!(
                "(= {} {})",
                smt_boolean(output, positions, "x")?,
                smt_boolean(output, positions, "z")?
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let assertion = format!(
        "(and {} {})",
        smt_or(&distinct_inputs),
        smt_and(&equal_outputs)
    );
    Some(smt_script(
        declarations(positions.len(), &["x", "z"]),
        assertion,
        &[],
    ))
}
fn declarations(width: usize, namespaces: &[&str]) -> String {
    namespaces
        .iter()
        .flat_map(|namespace| {
            (0..width).map(move |index| format!("(declare-fun {namespace}{index} () Bool)\n"))
        })
        .collect()
}
fn smt_boolean(
    polynomial: &BooleanPolynomial,
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<String> {
    polynomial.smt_expression(|variable| match variable {
        Variable::Input(qubit) => positions
            .get(qubit)
            .map(|position| format!("{namespace}{position}")),
        Variable::Path(_) => None,
    })
}
fn smt_or(terms: &[String]) -> String {
    smt_fold(terms, "or", "false")
}
fn smt_and(terms: &[String]) -> String {
    smt_fold(terms, "and", "true")
}
fn smt_fold(terms: &[String], operator: &str, identity: &str) -> String {
    terms
        .iter()
        .cloned()
        .fold(identity.to_owned(), |left, right| {
            format!("({operator} {left} {right})")
        })
}
fn smt_script(declarations: String, assertion: String, values: &[String]) -> String {
    let get_values = if values.is_empty() {
        String::new()
    } else {
        format!("(get-value ({}))\n", values.join(" "))
    };
    format!(
        "(set-logic QF_BV)\n(set-option :produce-models true)\n{declarations}(assert {assertion})\n(check-sat)\n{get_values}"
    )
}
