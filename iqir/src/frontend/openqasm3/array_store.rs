//! Symbolic array stores remain one operation; no per-cell conditional tree.
use super::*;

impl Lowerer {
    pub(super) fn array_compound_assignment(
        &mut self,
        lhs: &Expr,
        assignment: ast::BinExpr,
    ) -> Result<Option<Statement>, FrontendError> {
        let Expr::IndexedIdentifier(indexed) = lhs else {
            return Ok(None);
        };
        let name = indexed
            .identifier()
            .ok_or_else(|| expected!("array name", lhs))?
            .string();
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ScalarArray { index, is_const } = binding.kind else {
            return Ok(None);
        };
        if is_const {
            return Err(expected!("an assignable array element", lhs));
        }
        self.check_constant_visibility(binding, lhs)?;
        let a = &self.scalar_arrays[index];
        let (target, ty, dimensions) = (a.id, a.ty, a.dimensions.clone());
        let length = dimensions.iter().product();
        let offset = self.array_offset(lhs, &dimensions)?;
        let offset_ty = offset.ty;
        self.scopes.enter(ScopeKind::Block);
        let result = (|| {
            let mut temp = |name: &str, ty: ScalarType| {
                self.scopes
                    .declare(
                        name,
                        BindingKind::Scalar {
                            ty,
                            explicit_width: true,
                            is_const: false,
                            assignable: true,
                            value: None,
                        },
                    )
                    .map_err(scope_error)
            };
            let address = temp("@array.address", offset_ty)?.id;
            let cell = temp("@array.value", ty)?.id;
            let index = self.ids.node(crate::ScalarExprData {
                ty: offset_ty,
                kind: crate::ScalarExprKind::Read(address),
            });
            let read = self.ids.node(crate::ScalarExprData {
                ty,
                kind: crate::ScalarExprKind::ArrayRead {
                    array: target,
                    length,
                    index: Box::new(index.clone()),
                },
            });
            let address_decl = self.ids.node(StatementKind::ScalarDeclare {
                id: address,
                name: "@array.address".into(),
                ty: offset_ty,
                explicit_width: true,
                initializer: Some(offset),
            });
            let value_decl = self.ids.node(StatementKind::ScalarDeclare {
                id: cell,
                name: "@array.value".into(),
                ty,
                explicit_width: true,
                initializer: Some(read),
            });
            let operation = self.lower_scalar_compound(assignment, cell, ty)?;
            let value = self.ids.node(crate::ScalarExprData {
                ty,
                kind: crate::ScalarExprKind::Read(cell),
            });
            let store = self.ids.node(StatementKind::ArrayStore {
                target,
                index,
                value,
            });
            let block = self.ids.node(BlockData {
                statements: vec![address_decl, value_decl, operation, store],
                ..BlockData::default()
            });
            Ok(Some(self.ids.node(StatementKind::Scope(block))))
        })();
        self.scopes.exit();
        result
    }
    pub(super) fn dynamic_array_assignment(
        &mut self,
        lhs: &Expr,
        rhs: Expr,
    ) -> Result<Option<Statement>, FrontendError> {
        let Expr::IndexedIdentifier(indexed) = lhs else {
            return Ok(None);
        };
        let name = indexed
            .identifier()
            .ok_or_else(|| expected!("array name", lhs))?
            .string();
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ScalarArray { index, is_const } = binding.kind else {
            return Ok(None);
        };
        if is_const {
            return Err(expected!("an assignable array element", lhs));
        }
        self.check_constant_visibility(binding, lhs)?;
        let array = &self.scalar_arrays[index];
        let (target, ty, dimensions) = (array.id, array.ty, array.dimensions.clone());
        let index = self.array_offset(lhs, &dimensions)?;
        if matches!(&rhs,Expr::CallExpr(call) if self.is_subroutine_call(call)) {
            // Snapshot the address before the call, which may modify its inputs.
            self.scopes.enter(ScopeKind::Block);
            let result = (|| {
                let mut temp = |name: &str, ty: ScalarType| {
                    self.scopes
                        .declare(
                            name,
                            BindingKind::Scalar {
                                ty,
                                explicit_width: true,
                                is_const: false,
                                assignable: true,
                                value: None,
                            },
                        )
                        .map_err(scope_error)
                };
                let address = temp("@array.address", index.ty)?.id;
                let value = temp("@array.value", ty)?.id;
                let read_index = self.ids.node(crate::ScalarExprData {
                    ty: index.ty,
                    kind: crate::ScalarExprKind::Read(address),
                });
                let address_decl = self.ids.node(StatementKind::ScalarDeclare {
                    id: address,
                    name: "@array.address".into(),
                    ty: index.ty,
                    explicit_width: true,
                    initializer: Some(index),
                });
                let value_decl = self.ids.node(StatementKind::ScalarDeclare {
                    id: value,
                    name: "@array.value".into(),
                    ty,
                    explicit_width: true,
                    initializer: None,
                });
                let call = self.lower_scalar_value_assignment(value, ty, rhs)?;
                let read_value = self.ids.node(crate::ScalarExprData {
                    ty,
                    kind: crate::ScalarExprKind::Read(value),
                });
                let store = self.ids.node(StatementKind::ArrayStore {
                    target,
                    index: read_index,
                    value: read_value,
                });
                let body = self.ids.node(BlockData {
                    statements: vec![address_decl, value_decl, call, store],
                    ..BlockData::default()
                });
                Ok(Some(self.ids.node(StatementKind::Scope(body))))
            })();
            self.scopes.exit();
            return result;
        }
        let value = self.lower_scalar_expr(rhs, ty)?;
        Ok(Some(self.ids.node(StatementKind::ArrayStore {
            target,
            index,
            value,
        })))
    }
}
