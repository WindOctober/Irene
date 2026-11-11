//! Fixed-shape numeric arrays. Mutable arrays have functional storage;
//! immutable tables also support deferred symbolic selection.
use super::*;

pub(super) struct ScalarArray {
    pub(super) id: SymbolId,
    pub(super) ty: ScalarType,
    pub(super) table: Option<std::sync::Arc<crate::ConstantTable>>,
    pub(super) dimensions: Vec<usize>,
    pub(super) cells: Vec<String>,
}

impl Lowerer {
    pub(super) fn lower_array_declaration(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
    ) -> Result<Vec<Statement>, FrontendError> {
        let name = declaration_name(&declaration)?;
        let array = declaration.array_type().unwrap();
        let source_ty = array
            .scalar_type()
            .ok_or_else(|| expected!("numeric array element type", &array))?;
        let ty = self.scalar_type(&source_ty)?;
        // The pinned parser emits dimensions directly below ARRAY_TYPE, not
        // in the ExpressionList suggested by its generated accessor.
        let dimensions = array
            .syntax()
            .children()
            .filter_map(Expr::cast)
            .map(|e| self.static_index(e, true))
            .collect::<Result<Vec<_>, _>>()?;
        let count = dimensions
            .iter()
            .try_fold(1usize, |n, &d| n.checked_mul(d))
            .filter(|&n| n > 0 && n <= 4096)
            .filter(|_| !dimensions.is_empty() && dimensions.len() <= 7)
            .ok_or_else(|| {
                unsupported!(
                    "array shape (1..7 dimensions, at most 4096 nonempty cells)",
                    &array
                )
            })?;
        let is_const = declaration.const_token().is_some();
        let sources = match declaration.expr() {
            Some(source) => {
                let mut values = Vec::with_capacity(count);
                flatten_initializer(source, &dimensions, &mut values)?;
                values.into_iter().map(Some).collect::<Vec<_>>()
            }
            None if is_const => return Err(expected!("a const array initializer", &declaration)),
            None => vec![None; count],
        };
        let index = self.scalar_arrays.len();
        let array_binding = self
            .scopes
            .declare(name.clone(), BindingKind::ScalarArray { index, is_const })
            .map_err(scope_error)?;
        let cells = (0..if is_const {count} else {0})
            .map(|i| format!("$array{}_{}", array_binding.id.0, i))
            .collect::<Vec<_>>();
        // Only const declarations need per-element compile-time bindings.
        // Mutable declarations have one storage identity, not hidden scalars.
        let mut bindings = Vec::with_capacity(count);
        for cell in &cells {
            self.charge_static_expansion(&declaration)?;
            bindings.push(
                self.scopes
                    .declare(
                        cell.clone(),
                        BindingKind::Scalar {
                            ty,
                            explicit_width: source_ty.designator().is_some(),
                            is_const,
                            assignable: !is_const,
                            value: None,
                        },
                    )
                    .map_err(scope_error)?,
            );
        }
        self.scalar_arrays.push(ScalarArray {
            id: array_binding.id,
            ty,
            table: None,
            dimensions,
            cells: cells.clone(),
        });
        let mut statements = Vec::with_capacity(count);
        // Initializer elements are evaluated before any cell assignment becomes
        // visible, preserving aggregate initialization rather than sequential writes.
        let saved_ids = self.ids.clone();
        let initializers = sources
            .into_iter()
            .map(|source| {
                if source.as_ref().is_some_and(|e| {
                    e.syntax()
                        .descendants()
                        .filter_map(ast::Identifier::cast)
                        .any(|n| n.string() == name)
                }) {
                    return Err(unsupported!(
                        "self-referencing array initializer",
                        &declaration
                    ));
                }
                if is_const {
                    if let Some(e) = &source {
                        self.check_const_expression(e, 0)?;
                    }
                }
                source.map(|e| self.lower_scalar_expr(e, ty)).transpose()
            })
            .collect::<Result<Vec<_>, FrontendError>>();
        if is_const {
            self.ids = saved_ids;
        }
        let initializers = initializers?;
        // This is an optimization fact, not source-level const qualification.
        // Check all uses (including later/back-edge writes) before retaining a
        // table across loops. Mutable storage and const-expression rules stay
        // unchanged. Only closed, typed initializer values are eligible.
        let inferred_table = if !is_const && read_only_array(&declaration, &name)
        {
            initializers.iter().map(|e| e.as_ref().map(|e| e.constant_value())
                .transpose().map(|v| v.flatten()))
                .collect::<Result<Option<Vec<_>>, _>>()
                .map_err(|reason| FrontendError::ScalarEvaluation {
                    reason, snippet: declaration.syntax().text().to_string(),
                })?
        } else { None };
        let mut table_values = Vec::new();
        if !is_const {
            statements.push(self.ids.node(StatementKind::ArrayDeclare {
                id: array_binding.id, name: name.clone(), ty, length: count,
                initializers: initializers.clone(),
            }));
        }
        for (i, (_binding, initializer)) in bindings.into_iter().zip(initializers).enumerate() {
            if is_const {
                let value =
                    self.require_scalar_constant(initializer.as_ref().unwrap(), &declaration)?;
                self.scopes.set_scalar_value(&cells[i], value);
                table_values.push(value);
            }
        }
        if let Some(table_values) = if is_const { Some(table_values) } else { inferred_table } {
            self.scalar_arrays[index].table = Some(std::sync::Arc::new(
                crate::ConstantTable::new(ty, table_values).map_err(|reason| FrontendError::ScalarEvaluation {
                    reason, snippet: declaration.syntax().text().to_string(),
                })?,
            ));
        }
        Ok(statements)
    }

    pub(super) fn scalar_array_type(&self, expression: &Expr) -> Result<Option<ScalarType>, FrontendError> {
        let Expr::IndexedIdentifier(indexed) = expression else { return Ok(None) };
        let name = indexed.identifier().ok_or_else(|| expected!("array name", indexed))?.string();
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        Ok(match binding.kind {
            BindingKind::ScalarArray { index, .. } => Some(self.scalar_arrays[index].ty),
            _ => None,
        })
    }

    /// Lower an indexed read to a shared constant table or mutable array storage.
    /// Symbolic indices retain bounds checks in either representation.
    pub(super) fn constant_table_read(&mut self, expression: &Expr) -> Result<Option<crate::ScalarExpr>, FrontendError> {
        let Expr::IndexedIdentifier(indexed) = expression else { return Ok(None) };
        let name = indexed.identifier().ok_or_else(|| expected!("array name", indexed))?.string();
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ScalarArray { index, .. } = binding.kind else { return Ok(None) };
        self.check_constant_visibility(binding, expression)?;
        let array = &self.scalar_arrays[index];
        let dimensions = array.dimensions.clone();
        let Some(table) = array.table.clone() else {
            let (array, length, ty) = (array.id, array.dimensions.iter().product(), array.ty);
            let index = self.array_offset(expression, &dimensions)?;
            return Ok(Some(self.ids.node(crate::ScalarExprData { ty,
                kind: crate::ScalarExprKind::ArrayRead { array, length, index: Box::new(index) } })));
        };
        let index = self.array_offset(expression, &dimensions)?;
        let read = self.ids.node(crate::ScalarExprData {
            ty: table.ty(), kind: crate::ScalarExprKind::TableRead { table, index: Box::new(index) },
        });
        // A known bad index is an error, not a symbolic read with a default.
        if let Some(value) = read.constant_value().map_err(|reason| FrontendError::ScalarEvaluation {
            reason, snippet: expression.syntax().text().to_string(),
        })? {
            return Ok(Some(self.ids.node(crate::ScalarExprData { ty: read.ty, kind: value.expression() })));
        }
        Ok(Some(read))
    }

    /// Row-major offset with independent per-axis domains. In one dimension
    /// the consuming array read/store checks the index directly.
    pub(super) fn array_offset(&mut self, expression: &Expr, dimensions: &[usize])
        -> Result<crate::ScalarExpr, FrontendError> {
        let Expr::IndexedIdentifier(indexed) = expression else { unreachable!() };
        let mut indices = Vec::new();
        for op in indexed.index_operators() {
            let Some(IndexKind::ExpressionList(list)) = op.index_kind() else {
                return Err(unsupported!("array slice or set selection", expression));
            };
            indices.extend(list.exprs());
        }
        if indices.len() != dimensions.len() { return Err(expected!("one index for each array dimension", expression)) }
        let offset_ty = ScalarType::Int { width: 64, signed: true };
        let single_axis = dimensions.len() == 1;
        let mut offset = None;
        let mut stride = dimensions.iter().product::<usize>();
        for (source, &dimension) in indices.into_iter().zip(dimensions) {
            if source.syntax().descendants().any(|n| ast::IndexedIdentifier::cast(n).is_some()) {
                return Err(unsupported!("array-valued index expression", expression));
            }
            let ty = self.scalar_hint(&source)?.unwrap_or(offset_ty);
            if ty.is_float() { return Err(expected!("integer table index", expression)) }
            let index = self.lower_scalar_expr(source, ty)?;
            if single_axis {
                if let Some(crate::ScalarValue::Integer(i)) = index.constant_value()
                    .map_err(|reason| FrontendError::ScalarEvaluation {reason,snippet:expression.syntax().text().to_string()})? {
                    if i<0 || i as u128>=dimension as u128 {return Err(unsupported!("array index out of bounds",expression));}
                }
                offset = Some(index);
                break;
            }
            stride /= dimension;
            // Each axis is checked independently by the existing table-read
            // domain. Checking only the flattened offset would unsoundly let
            // e.g. a[0, columns] alias a[1, 0]. Offsets fit int64 because fixed
            // array declarations contain at most 4096 cells.
            let axis = std::sync::Arc::new(crate::ConstantTable::new(offset_ty,
                (0..dimension).map(|i| crate::ScalarValue::Integer((i * stride) as i128)).collect()
            ).expect("bounded integer table offsets"));
            let term = self.ids.node(crate::ScalarExprData {
                ty: offset_ty, kind: crate::ScalarExprKind::TableRead { table: axis, index: Box::new(index) },
            });
            offset = Some(match offset {
                None => term,
                Some(left) => self.ids.node(crate::ScalarExprData { ty: offset_ty,
                    kind: crate::ScalarExprKind::Binary { op: crate::ScalarArithmetic::Add,
                        left: Box::new(left), right: Box::new(term) } }),
            });
        }
        let offset = offset.expect("nonempty array rank");
        offset.constant_value().map_err(|reason| FrontendError::ScalarEvaluation {
            reason, snippet: expression.syntax().text().to_string(),
        })?;
        Ok(offset)
    }

    /// Resolve only a full static selection; never replace a dynamic selection
    /// with one guessed cell. Comma and chained index syntax are equivalent.
    pub(super) fn array_cell(
        &self,
        expression: &Expr,
        require_const: bool,
    ) -> Result<Option<Binding>, FrontendError> {
        let (name, operators) = match expression {
            Expr::IndexedIdentifier(indexed) => (
                indexed
                    .identifier()
                    .ok_or_else(|| expected!("array name", indexed))?
                    .string(),
                indexed.index_operators().collect::<Vec<_>>(),
            ),
            _ => return Ok(None),
        };
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ScalarArray { index, is_const } = binding.kind else {
            return Ok(None);
        };
        if require_const && !is_const {
            return Err(expected!("a const array", expression));
        }
        if !is_const { return Ok(None); }
        let array = &self.scalar_arrays[index];
        let mut indices = Vec::new();
        for op in operators {
            let Some(IndexKind::ExpressionList(list)) = op.index_kind() else {
                return Err(unsupported!("array slice or set selection", expression));
            };
            for e in list.exprs() {
                // Prevent recursion through arbitrarily nested array indices.
                if e.syntax()
                    .descendants()
                    .any(|n| ast::IndexedIdentifier::cast(n).is_some())
                {
                    return Err(unsupported!("array-valued index expression", expression));
                }
                if array.table.is_some() && !require_const
                    && !self.is_closed_integer_expression(&e)? {
                    return Ok(None);
                }
                indices.push(self.static_index(e, require_const).map_err(|_| {
                    unsupported!(
                        "array index must be a static integer (runtime indexing is not supported)",
                        expression
                    )
                })?);
            }
        }
        if indices.len() != array.dimensions.len() {
            return Err(expected!("one index for each array dimension", expression));
        }
        let mut offset = 0;
        for (i, d) in indices.into_iter().zip(&array.dimensions) {
            if i >= *d {
                return Err(expected!("an in-bounds array index", expression));
            }
            offset = offset * d + i;
        }
        let cell = self
            .scopes
            .lookup(&array.cells[offset])
            .map_err(scope_error)?;
        self.check_constant_visibility(cell, expression)?;
        Ok(Some(cell))
    }
}

/// Conservative whole-source use check. Same-name shadowing can prevent an
/// optimization, never justify one. A bare array use may escape through an
/// alias/reference and is rejected; element reads passed by value are safe.
fn read_only_array(declaration: &ast::ClassicalDeclarationStatement, name: &str) -> bool {
    let root = declaration.syntax().ancestors().last().unwrap();
    let mentions = |e: &Expr| e.syntax().descendants()
        .filter_map(ast::Identifier::cast).any(|id| id.string() == name);
    for node in root.descendants() {
        let target = if let Some(assign) = ast::AssignmentStmt::cast(node.clone()) {
            assign.syntax().children().find_map(Expr::cast)
        } else if let Some(binary) = ast::BinExpr::cast(node.clone()) {
            if matches!(binary.op_kind(), Some(ast::BinaryOp::Assignment { .. })) {
                binary.lhs()
            } else { None }
        } else { None };
        if target.as_ref().is_some_and(&mentions) { return false; }
        if let Some(id) = ast::Identifier::cast(node) {
            if id.string() == name && !id.syntax().parent()
                .and_then(ast::IndexedIdentifier::cast)
                .and_then(|indexed| indexed.identifier())
                .is_some_and(|base| base.syntax() == id.syntax()) {
                return false;
            }
        }
    }
    true
}

fn flatten_initializer(
    source: Expr,
    dimensions: &[usize],
    values: &mut Vec<Expr>,
) -> Result<(), FrontendError> {
    if dimensions.is_empty() {
        if matches!(source, Expr::ArrayLiteral(_)) {
            return Err(expected!("scalar array initializer element", &source));
        }
        values.push(source);
        return Ok(());
    }
    let Expr::ArrayLiteral(literal) = &source else {
        return Err(unsupported!(
            "array initializer other than a shape-matching literal",
            &source
        ));
    };
    let elements = literal
        .syntax()
        .children()
        .filter_map(Expr::cast)
        .collect::<Vec<_>>();
    if elements.len() != dimensions[0] {
        return Err(expected!(
            "array initializer matching the declared shape",
            &source
        ));
    }
    for element in elements {
        flatten_initializer(element, &dimensions[1..], values)?;
    }
    Ok(())
}
