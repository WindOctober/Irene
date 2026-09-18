use super::*;
use std::collections::BTreeSet;

fn numeric_ids(expression: &NumericExpr) -> Vec<usize> {
    fn visit(expression: &NumericExpr, ids: &mut Vec<usize>) {
        ids.push(expression.ast_id.index());
        match &expression.kind {
            NumericExprKind::Rational(_)
            | NumericExprKind::Constant(_)
            | NumericExprKind::Input(_) => {}
            NumericExprKind::Neg(inner) => visit(inner, ids),
            NumericExprKind::Add(left, right)
            | NumericExprKind::Sub(left, right)
            | NumericExprKind::Mul(left, right)
            | NumericExprKind::Div(left, right) => {
                visit(left, ids);
                visit(right, ids);
            }
        }
    }
    let mut ids = Vec::new();
    visit(expression, &mut ids);
    ids
}

#[test]
fn copying_numeric_leaves_preserves_exact_values_and_input_symbols() {
    let mut ids = AstIdGenerator::default();
    for kind in [
        NumericExprKind::Rational(BigRational::new((-7).into(), 11.into())),
        NumericExprKind::Constant(NumericConstant::Pi),
        NumericExprKind::Constant(NumericConstant::Tau),
        NumericExprKind::Constant(NumericConstant::Euler),
        NumericExprKind::Input(SymbolId(42)),
    ] {
        let source = ids.node(kind);
        let before = numeric_ids(&source);
        let next = ids.next;
        let copy = ids.clone_numeric_expr(&source);
        assert_eq!(copy, source);
        assert_eq!(numeric_ids(&source), before);
        assert_eq!(numeric_ids(&copy), vec![next]);
        assert_ne!(copy.ast_id, source.ast_id);
        assert_eq!(ids.next, next + 1);
    }
}

#[test]
fn copying_nested_numeric_expressions_refreshes_every_node_on_each_copy() {
    let mut ids = AstIdGenerator::default();
    let theta = ids.node(NumericExprKind::Input(SymbolId(9)));
    let negative = ids.node(NumericExprKind::Neg(Box::new(theta)));
    let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
    let sum = ids.node(NumericExprKind::Add(Box::new(negative), Box::new(pi)));
    let fraction = ids.node(NumericExprKind::Rational(BigRational::new(
        3.into(),
        7.into(),
    )));
    let difference = ids.node(NumericExprKind::Sub(Box::new(sum), Box::new(fraction)));
    let factor = ids.node(NumericExprKind::Input(SymbolId(10)));
    let product = ids.node(NumericExprKind::Mul(Box::new(difference), Box::new(factor)));
    let divisor = ids.node(NumericExprKind::Rational(BigRational::from_integer(
        2.into(),
    )));
    let source = ids.node(NumericExprKind::Div(Box::new(product), Box::new(divisor)));

    let source_ids = numeric_ids(&source);
    let mut allocated = source_ids.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(allocated.len(), source_ids.len());
    for _ in 0..3 {
        let start = ids.next;
        let copy = ids.clone_numeric_expr(&source);
        assert_eq!(copy, source);
        let copy_ids = numeric_ids(&copy);
        assert_eq!(copy_ids.len(), source_ids.len());
        assert_eq!(ids.next, start + source_ids.len());
        assert_eq!(
            copy_ids.iter().copied().collect::<BTreeSet<_>>(),
            (start..ids.next).collect::<BTreeSet<_>>()
        );
        for id in copy_ids {
            assert!(allocated.insert(id), "reused AST identity {id}");
        }
        assert_eq!(numeric_ids(&source), source_ids);
    }
    assert_eq!(allocated, (0..ids.next).collect());
}
