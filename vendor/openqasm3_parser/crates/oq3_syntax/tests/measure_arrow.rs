use oq3_syntax::{ast, AstNode, SourceFile};

#[test]
fn parses_measurement_arrow_statement() {
    let parse = SourceFile::parse("measure q -> c[0];");
    assert!(parse.errors().is_empty(), "{:?}", parse.errors());

    let measurement = match parse.tree().statements().next() {
        Some(ast::Stmt::Measure(measurement)) => measurement,
        _ => panic!("expected a measurement statement"),
    };

    assert_eq!(
        measurement.qubit().unwrap().syntax().text().to_string(),
        "q"
    );
    assert_eq!(
        measurement.target().unwrap().syntax().text().to_string(),
        "c[0]"
    );
}
