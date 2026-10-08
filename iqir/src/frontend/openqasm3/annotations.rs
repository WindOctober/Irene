//! Attach parsed specifications before executable lowering expands statements.
use super::*;
use crate::annotation::{
    Annotation, AnnotationKind, AnnotationPayload, SourceSpan, SpecExpr, SpecType,
    check_expression, define_function, parse_annotation, parse_function,
};

impl Lowerer {
    pub(super) fn declare_spec_function(
        &mut self,
        pragma: ast::PragmaStatement,
    ) -> Result<(), FrontendError> {
        let range = pragma.syntax().text_range();
        let span = SourceSpan {
            source: self.source_name.clone(),
            start: u32::from(range.start()) as usize,
            end: u32::from(range.end()) as usize,
        };
        let f = parse_function(&format!("pragma{}", pragma.pragma_text()), span.clone()).map_err(
            |e| FrontendError::Annotation {
                source_name: span.source.clone(),
                offset: span.start + e.offset,
                message: e.message,
            },
        )?;
        define_function(&mut self.spec_functions, f).map_err(|e| FrontendError::Annotation {
            source_name: span.source,
            offset: span.start,
            message: e.to_string(),
        })?;
        Ok(())
    }

    pub(super) fn annotated_statements(
        &self,
        statements: impl Iterator<Item = Stmt>,
    ) -> Result<Vec<(Vec<Annotation>, Stmt)>, FrontendError> {
        let mut result = Vec::new();
        let mut pending = Vec::new();
        for statement in statements {
            if let Stmt::AnnotationStatement(a) = statement {
                let range = a.syntax().text_range();
                let span = SourceSpan {
                    source: self.source_name.clone(),
                    start: u32::from(range.start()) as usize,
                    end: u32::from(range.end()) as usize,
                };
                let annotation =
                    parse_annotation(&a.annotation_text(), span.clone()).map_err(|e| {
                        FrontendError::Annotation {
                            source_name: span.source,
                            offset: span.start + e.offset,
                            message: e.message,
                        }
                    })?;
                pending.push(annotation);
            } else {
                result.push((std::mem::take(&mut pending), statement));
            }
        }
        if let Some(a) = pending.first() {
            return Err(
                self.annotation_error(a, "annotation has no following statement in this block")
            );
        }
        Ok(result)
    }

    fn annotation_error(&self, a: &Annotation, message: impl Into<String>) -> FrontendError {
        FrontendError::Annotation {
            source_name: a.span.source.clone(),
            offset: a.span.start,
            message: message.into(),
        }
    }

    pub(super) fn lower_annotated_statement(
        &mut self,
        mut annotations: Vec<Annotation>,
        statement: Stmt,
    ) -> Result<Statement, FrontendError> {
        if !matches!(
            &statement,
            Stmt::WhileStmt(_)
                | Stmt::ForStmt(_)
                | Stmt::IfStmt(_)
                | Stmt::ExprStmt(_)
                | Stmt::AssignmentStmt(_)
                | Stmt::Measure(_)
                | Stmt::Reset(_)
                | Stmt::Barrier(_)
        ) {
            return Err(self.annotation_error(&annotations[0], "annotations currently require an executable statement, not a declaration/definition"));
        }
        for a in &mut annotations {
            if matches!(
                a.kind,
                AnnotationKind::Invariant | AnnotationKind::Terminates
            ) && !matches!(&statement, Stmt::WhileStmt(_))
            {
                return Err(self.annotation_error(a, "invariant/terminates requires a while statement (static for loops are expanded)"));
            }
            if let AnnotationPayload::Expression(e) = &mut a.payload {
                let ty =
                    check_expression(e, &self.spec_functions, |name| self.resolve_spec_name(name))
                        .map_err(|message| FrontendError::Annotation {
                            source_name: a.span.source.clone(),
                            offset: a.span.start,
                            message: message.to_string(),
                        })?;
                if !matches!(ty, SpecType::Bool | SpecType::Bit) {
                    return Err(self.annotation_error(
                        a,
                        "requires/ensures/invariant must be Boolean predicates",
                    ));
                }
            }
        }
        let lowered = self.lower_statement(statement)?;
        // In particular, retain a broadcast's entire Scope, not its first gate.
        self.annotations.insert(lowered.ast_id(), annotations);
        Ok(lowered)
    }

    fn resolve_spec_name(&self, name: &str) -> Result<(SpecExpr, SpecType), String> {
        let binding = self
            .scopes
            .lookup(name)
            .map_err(|_| format!("unknown specification identifier `{name}`"))?;
        let ty = match binding.kind {
            BindingKind::QuantumVariable(QuantumType::Scalar) => SpecType::Qubit,
            BindingKind::QuantumVariable(QuantumType::Register { width }) => {
                SpecType::QubitRegister(width)
            }
            BindingKind::Constant(_) => {
                return Err(format!(
                    "`{name}` is a mathematical builtin; use a backslash-prefixed constant in specifications"
                ));
            }
            BindingKind::ClassicalBit(t) | BindingKind::StaticBits { ty: t, .. } => match t {
                BitType::Bool => SpecType::Bool,
                BitType::Bit => SpecType::Bit,
                BitType::Angle { .. } => SpecType::Angle,
                _ => SpecType::Uint,
            },
            BindingKind::Scalar {
                ty: ScalarType::Int { signed, .. },
                ..
            } => {
                if signed {
                    SpecType::Int
                } else {
                    SpecType::Uint
                }
            }
            BindingKind::Scalar {
                ty: ScalarType::Float { .. },
                ..
            } => SpecType::Float,
            BindingKind::NumericInput(t) => match t {
                NumericType::Int(_) => SpecType::Int,
                NumericType::Uint(_) => SpecType::Uint,
                NumericType::Float(_) => SpecType::Float,
                NumericType::Angle(_) => SpecType::Angle,
            },
            _ => {
                return Err(format!(
                    "`{name}` is not a classical specification value or program quantum variable"
                ));
            }
        };
        let expression = match binding.kind {
            BindingKind::Constant(c) => SpecExpr::Constant(c),
            BindingKind::StaticBits {
                value,
                ty: BitType::Bool | BitType::Bit,
            } => SpecExpr::Bool(value != 0),
            BindingKind::StaticBits {
                value,
                ty: BitType::Uint { .. },
            } => SpecExpr::Number(BigRational::from_integer(value.into())),
            BindingKind::Scalar {
                is_const: true,
                value: Some(v),
                ..
            }
            | BindingKind::Scalar {
                assignable: false,
                value: Some(v),
                ..
            } => {
                let number = match v {
                    ScalarValue::Integer(i) => BigRational::from_integer(i.into()),
                    _ => BigRational::from_float(v.as_float().ok_or("invalid float constant")?)
                        .ok_or("non-finite specification constant")?,
                };
                SpecExpr::Number(number)
            }
            BindingKind::Scalar { .. }
            | BindingKind::ClassicalBit(_)
            | BindingKind::NumericInput(_)
            | BindingKind::QuantumVariable(_) => SpecExpr::Symbol {
                id: binding.id,
                name: name.to_owned(),
            },
            _ => {
                return Err(format!(
                    "unsupported specification binding `{name}` ({})",
                    binding.kind.description()
                ));
            }
        };
        Ok((expression, ty))
    }
}
