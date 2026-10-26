//! Fixed-shape numeric arrays with statically selected cells. No array theory:
//! each cell has its own ordinary typed scalar storage and initialization state.
use super::*;

pub(super) struct ScalarArray {
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
        let cells = (0..count)
            .map(|i| format!("$array{}_{}", array_binding.id.0, i))
            .collect::<Vec<_>>();
        // Install every cell before evaluating initializers: forward/self reads
        // are uninitialized reads, never an accidental read of an outer array.
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
        for (i, (binding, initializer)) in bindings.into_iter().zip(initializers).enumerate() {
            if is_const {
                let value =
                    self.require_scalar_constant(initializer.as_ref().unwrap(), &declaration)?;
                self.scopes.set_scalar_value(&cells[i], value);
            } else {
                self.known_scalars.declare(binding.id, initializer.as_ref())?;
                statements.push(self.ids.node(StatementKind::ScalarDeclare {
                    id: binding.id,
                    name: format!("{name}[{i}]"),
                    ty,
                    explicit_width: source_ty.designator().is_some(),
                    initializer,
                }));
            }
        }
        Ok(statements)
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
