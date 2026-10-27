//! Attach parsed specifications before executable lowering expands statements.
use super::*;
use crate::annotation::{
    Annotation, AnnotationKind, AnnotationPayload, SourceSpan, SpecExpr, SpecType,
    check_expression, define_function, parse_annotation, parse_function,
};

/// `None` denotes a standalone assertion rather than an attached source statement.
type AnnotatedStatement = (Vec<Annotation>, Option<Stmt>);

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
    ) -> Result<Vec<AnnotatedStatement>, FrontendError> {
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
                if annotation.kind == AnnotationKind::Assert {
                    if let Some(a) = pending.first() {
                        return Err(self.annotation_error(a, "statement annotations require an executable statement before a standalone assert"));
                    }
                    result.push((vec![annotation], None));
                } else {
                    pending.push(annotation);
                }
            } else {
                result.push((std::mem::take(&mut pending), Some(statement)));
            }
        }
        if let Some(a) = pending.first() {
            return Err(
                self.annotation_error(a, "annotation has no following statement in this block")
            );
        }
        Ok(result)
    }

    /// An empty executable sequence anchors a proof boundary without changing
    /// program state or requiring a following source statement.
    pub(super) fn lower_assertion(
        &mut self,
        mut annotations: Vec<Annotation>,
    ) -> Result<Statement, FrontendError> {
        let a = &mut annotations[0];
        let AnnotationPayload::Expression(e) = &mut a.payload else {
            unreachable!()
        };
        let ty = check_expression(e, &self.spec_functions, |name| self.resolve_spec_name(name))
            .map_err(|e| self.annotation_error(a, e.to_string()))?;
        if !matches!(ty, SpecType::Bool | SpecType::Bit) {
            return Err(self.annotation_error(a, "assert must be a Boolean predicate"));
        }
        let boundary = self.sequence(Vec::new());
        self.annotations.insert(boundary.ast_id(), annotations);
        Ok(boundary)
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
        annotations: Vec<Annotation>,
        statement: Stmt,
    ) -> Result<Statement, FrontendError> {
        if let Stmt::ForStmt(for_statement) = &statement {
            let has_loop_contract = self.structured
                && annotations.iter().any(|a| matches!(a.kind,
                    AnnotationKind::Invariant | AnnotationKind::ExitState
                    | AnnotationKind::InitialState | AnnotationKind::Terminates
                    | AnnotationKind::RankingFunction | AnnotationKind::RankingProof));
            if has_loop_contract || !self.should_unroll_for(for_statement)? {
                return self.lower_runtime_for(for_statement.clone(), annotations);
            }
        }
        let scoped = matches!(
            &statement,
            Stmt::WhileStmt(_) | Stmt::ForStmt(_) | Stmt::IfStmt(_)
        ) && annotations
            .iter()
            .any(|a| a.kind == AnnotationKind::GhostDeclare);
        if scoped {
            self.scopes.enter(ScopeKind::Block);
        }
        let result = self.lower_annotations(annotations, statement, scoped, None);
        if scoped {
            self.scopes.exit();
        }
        result
    }

    pub(super) fn lower_annotations(
        &mut self,
        mut annotations: Vec<Annotation>,
        statement: Stmt,
        statement_scoped: bool,
        generated_loop: Option<Statement>,
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
        if let Some(absent) = annotations
            .iter()
            .find(|a| matches!(a.payload, AnnotationPayload::NoState))
        {
            if annotations
                .iter()
                .filter(|a| a.kind == AnnotationKind::ExitState)
                .count()
                != 1
            {
                return Err(self.annotation_error(
                    absent,
                    "exit_state none cannot be combined with another exit_state",
                ));
            }
        }
        for a in &mut annotations {
            let source_name = a.span.source.clone();
            let offset = a.span.start;
            let error = |message: String| FrontendError::Annotation {
                source_name: source_name.clone(),
                offset,
                message,
            };
            match &mut a.payload {
                AnnotationPayload::GhostDeclare {
                    id,
                    name,
                    ty,
                    initializer,
                    scoped,
                } => {
                    if matches!(name.as_str(), "true" | "false") {
                        return Err(error("reserved ghost variable name".into()));
                    }
                    if let Some(value) = initializer {
                        let actual = check_expression(value, &self.spec_functions, |n| {
                            self.resolve_spec_name(n)
                        })
                        .map_err(|e| error(e.to_string()))?;
                        if !ty.accepts_value(actual, value) {
                            return Err(error(format!(
                                "ghost `{name}` expects {ty:?}, got {actual:?}"
                            )));
                        }
                        self.check_ghost_value(value).map_err(&error)?;
                    }
                    let binding = self
                        .scopes
                        .declare(name.clone(), BindingKind::Ghost(*ty))
                        .map_err(|e| error(format!("invalid ghost declaration: {e:?}")))?;
                    *id = Some(binding.id);
                    *scoped = statement_scoped;
                    continue;
                }
                AnnotationPayload::GhostAssign { id, name, value } => {
                    let binding = self
                        .scopes
                        .lookup(name)
                        .map_err(|_| error(format!("unknown ghost variable `{name}`")))?;
                    let BindingKind::Ghost(ty) = binding.kind else {
                        return Err(error(format!("`{name}` is not a ghost variable")));
                    };
                    let actual = check_expression(value, &self.spec_functions, |n| {
                        self.resolve_spec_name(n)
                    })
                    .map_err(|e| error(e.to_string()))?;
                    if !ty.accepts_value(actual, value) {
                        return Err(error(format!(
                            "ghost `{name}` expects {ty:?}, got {actual:?}"
                        )));
                    }
                    self.check_ghost_value(value).map_err(&error)?;
                    *id = Some(binding.id);
                    continue;
                }
                _ => {}
            }
            if matches!(
                a.kind,
                AnnotationKind::Invariant
                    | AnnotationKind::InitialState
                    | AnnotationKind::ExitState
                    | AnnotationKind::Terminates
                    | AnnotationKind::RankingFunction
                    | AnnotationKind::RankingProof
            ) && !matches!(&statement, Stmt::WhileStmt(_))
                && generated_loop.is_none()
            {
                return Err(self.annotation_error(
                    a,
                    "loop contracts require a while statement (static for loops are expanded)",
                ));
            }
            if let AnnotationPayload::State { targets, operator } = &mut a.payload {
                let mut reference = SpecExpr::Call {
                    function: crate::annotation::MathFunction::DensityBlock,
                    arguments: std::mem::take(targets),
                };
                let expected = check_expression(&mut reference, &self.spec_functions, |name| {
                    self.resolve_spec_name(name)
                })
                .map_err(|e| error(e.to_string()))?;
                let SpecExpr::Call { arguments, .. } = reference else {
                    unreachable!()
                };
                *targets = arguments;
                // Reject overlapping references, including a register and one of its wires.
                let mut regions: Vec<(crate::SymbolId, Option<usize>)> = Vec::new();
                for target in targets.iter() {
                    let (id, index) = match target.uncast() {
                        SpecExpr::Symbol { id, .. } => (*id, None),
                        SpecExpr::Index { value, index } => {
                            let SpecExpr::Symbol { id, name } = value.uncast() else {
                                return Err(error("state target must name quantum storage".into()));
                            };
                            let i = index
                                .uncast()
                                .literal()
                                .filter(|n| n.is_integer())
                                .and_then(|n| n.to_integer().to_string().parse::<usize>().ok())
                                .ok_or_else(|| {
                                    error(
                                        "state target index must be a constant nonnegative integer"
                                            .into(),
                                    )
                                })?;
                            let (_, SpecType::QubitRegister(width)) =
                                self.resolve_spec_name(name).map_err(&error)?
                            else {
                                return Err(error(
                                    "indexed state target must name a quantum register".into(),
                                ));
                            };
                            if i >= width {
                                return Err(error("state target index out of range".into()));
                            }
                            (*id, Some(i))
                        }
                        _ => return Err(error("state target must name quantum storage".into())),
                    };
                    if regions.iter().any(|(old, at)| {
                        *old == id && (at.is_none() || index.is_none() || *at == index)
                    }) {
                        return Err(error("state targets overlap".into()));
                    }
                    regions.push((id, index));
                }
                let actual = check_expression(operator, &self.spec_functions, |name| {
                    self.resolve_spec_name(name)
                })
                .map_err(|e| error(e.to_string()))?;
                if actual != expected {
                    return Err(error(format!(
                        "state declaration expects {expected:?}, got {actual:?}"
                    )));
                }
                // A declaration defines its operator from classical context, not by
                // querying the unknown state it is supposed to characterize.
                let mut pending = vec![operator.clone()];
                let mut budget = 4096usize;
                while let Some(e) = pending.pop() {
                    budget = budget
                        .checked_sub(1)
                        .ok_or_else(|| error("state operator checking budget exceeded".into()))?;
                    if let SpecExpr::Symbol { name, .. } = &e
                        && matches!(
                            self.resolve_spec_name(name).map_err(&error)?.1,
                            SpecType::Qubit | SpecType::QubitRegister(_)
                        )
                    {
                        return Err(error(
                            "state operator cannot query program quantum storage".into(),
                        ));
                    }
                    if let SpecExpr::Call { function, .. } = &e {
                        use crate::annotation::MathFunction::*;
                        if matches!(
                            function,
                            DensityBlock
                                | AvgDensity
                                | Diagonal
                                | Probability
                                | Expectation
                                | Trace
                                | Normalize
                        ) {
                            return Err(error(
                                "state operator must be explicit, not a program-state query".into(),
                            ));
                        }
                    }
                    if let SpecExpr::HelperCall {
                        function,
                        arguments,
                    } = &e
                    {
                        pending.push(
                            crate::annotation::instantiate_function(
                                &self.spec_functions,
                                *function,
                                arguments,
                            )
                            .map_err(|e| error(e.to_string()))?,
                        );
                    } else {
                        pending.extend(e.children().into_iter().cloned());
                    }
                }
            }
            if let AnnotationPayload::Expression(e) = &mut a.payload {
                let ty =
                    check_expression(e, &self.spec_functions, |name| self.resolve_spec_name(name))
                        .map_err(|message| FrontendError::Annotation {
                            source_name: a.span.source.clone(),
                            offset: a.span.start,
                            message: message.to_string(),
                        })?;
                if a.kind == AnnotationKind::RankingFunction {
                    if !matches!(ty, SpecType::Int(_) | SpecType::Uint(_)) {
                        return Err(
                            self.annotation_error(a, "ranking_function must have integer type")
                        );
                    }
                } else if !matches!(ty, SpecType::Bool | SpecType::Bit) {
                    return Err(self.annotation_error(
                        a,
                        "requires/ensures/invariant/ranking_proof must be Boolean predicates",
                    ));
                }
            }
        }
        let lowered = match generated_loop {
            Some(lowered) => lowered,
            None => self.lower_statement(statement)?,
        };
        // While nodes retain their source condition and identity, including
        // jumps. Runtime-for callers pass the actual generated loop here.
        self.annotations.insert(lowered.ast_id(), annotations);
        Ok(lowered)
    }

    fn check_ghost_value(&self, expression: &SpecExpr) -> Result<(), String> {
        let mut pending = vec![expression.clone()];
        let mut work = 0;
        while let Some(e) = pending.pop() {
            work += 1;
            if work > 4096 {
                return Err("ghost expression checking budget exceeded".into());
            }
            match &e {
                SpecExpr::Symbol { name, .. } => {
                    if matches!(
                        self.resolve_spec_name(name)?.1,
                        SpecType::Qubit | SpecType::QubitRegister(_)
                    ) {
                        return Err(
                            "ghost values read classical values, not program quantum states".into(),
                        );
                    }
                }
                SpecExpr::Call {
                    function:
                        crate::annotation::MathFunction::Probability
                        | crate::annotation::MathFunction::Expectation,
                    ..
                } => {
                    return Err("probability/expectation are state predicates, not per-execution ghost values".into());
                }
                SpecExpr::HelperCall {
                    function,
                    arguments,
                } => {
                    pending.push(
                        crate::annotation::instantiate_function(
                            &self.spec_functions,
                            *function,
                            arguments,
                        )
                        .map_err(|e| e.to_string())?,
                    );
                }
                _ => {}
            }
            pending.extend(e.children().into_iter().cloned());
        }
        Ok(())
    }

    fn resolve_spec_name(&self, name: &str) -> Result<(SpecExpr, SpecType), String> {
        let binding = self
            .scopes
            .lookup(name)
            .map_err(|_| format!("unknown specification identifier `{name}`"))?;
        let ty = match binding.kind {
            BindingKind::ScalarArray { .. } => {
                return Err(format!(
                    "array-valued specifications/invariants are not supported (`{name}`); static program reads and writes are supported"
                ));
            }
            BindingKind::Ghost(ty) => ty,
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
                BitType::Angle { width } => SpecType::Angle(Some(width)),
                BitType::Uint {
                    width,
                    explicit_width,
                } => SpecType::Uint(explicit_width.then_some(width)),
                BitType::Register { width } => SpecType::Uint(Some(width)),
            },
            BindingKind::Scalar {
                ty: ScalarType::Int { signed, width },
                explicit_width,
                ..
            } => {
                if signed {
                    SpecType::Int(explicit_width.then_some(width as usize))
                } else {
                    SpecType::Uint(explicit_width.then_some(width as usize))
                }
            }
            BindingKind::Scalar {
                ty: ScalarType::Float { width },
                explicit_width,
                ..
            } => SpecType::Float(explicit_width.then_some(width as usize)),
            BindingKind::NumericInput(t) => match t {
                NumericType::Int(w) => SpecType::Int(w),
                NumericType::Uint(w) => SpecType::Uint(w),
                NumericType::Float(w) => SpecType::Float(w),
                NumericType::Angle(w) => SpecType::Angle(w),
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
                if v.as_float()
                    .is_some_and(|v| v == 0.0 && v.is_sign_negative())
                {
                    SpecExpr::Unary {
                        op: crate::annotation::UnaryOp::Neg,
                        operand: Box::new(SpecExpr::Number(number).cast(ty)),
                    }
                } else {
                    SpecExpr::Number(number)
                }
            }
            BindingKind::Ghost(_)
            | BindingKind::Scalar { .. }
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
        let expression = if matches!(
            ty,
            SpecType::Int(_) | SpecType::Uint(_) | SpecType::Float(_) | SpecType::Angle(_)
        ) {
            expression.cast(ty)
        } else {
            expression
        };
        Ok((expression, ty))
    }
}
