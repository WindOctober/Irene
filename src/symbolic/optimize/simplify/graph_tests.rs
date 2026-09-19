use super::*;

#[test]
fn bdd_conversion_preserves_nonflat_graphs_without_anf() {
    let variable = |i| BooleanPolynomial::variable(Variable::Path(i));
    let product = (0..20).fold(BooleanPolynomial::one(), |p, i| {
        p.and(&variable(i).complement())
    });
    assert!(product.expanded_terms(1024).is_none());
    let inconsistent =
        BddGuard::build(&[product.complement(), variable(0).complement()]).expect("small BDD");
    assert!(!inconsistent.function.satisfiable());
    let consistent = BddGuard::build(&[product.complement(), variable(0)]).expect("small BDD");
    assert!(consistent.function.satisfiable());
}
