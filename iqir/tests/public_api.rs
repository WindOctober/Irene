use iqir::{AstIdGenerator, NumericConstant, NumericExprKind};

#[test]
fn external_construction_and_copy_keep_identity_separate_from_content() {
    let mut ids = AstIdGenerator::default();
    let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
    let source = ids.node(NumericExprKind::Neg(Box::new(pi)));
    let copy = ids.clone_numeric_expr(&source);
    assert_eq!(source, copy);
    assert_ne!(source.ast_id(), copy.ast_id());
    let mut next = AstIdGenerator::starting_at(copy.ast_id().index() + 1);
    let other = next.node(NumericExprKind::Constant(NumericConstant::Tau));
    assert!(other.ast_id().index() > copy.ast_id().index());
}
