use std::collections::HashMap;

use crate::ir::{NumericConstant, NumericType, SymbolId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ScopeKind {
    Global,
    Block,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BindingKind {
    QuantumRegister { width: usize },
    ClassicalBit { width: usize },
    NumericInput(NumericType),
    Gate,
    Constant(NumericConstant),
}

impl BindingKind {
    fn can_be_shadowed(self) -> bool {
        !matches!(self, Self::Gate)
    }

    pub(super) fn description(self) -> &'static str {
        match self {
            Self::QuantumRegister { .. } => "quantum register",
            Self::ClassicalBit { .. } => "classical bit register",
            Self::NumericInput(_) => "numeric input",
            Self::Gate => "gate",
            Self::Constant(_) => "constant",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Binding {
    pub id: SymbolId,
    pub kind: BindingKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ScopeError {
    AlreadyDeclared(String),
    CannotShadow(String),
    IllegalDeclaration {
        declaration: &'static str,
        scope: ScopeKind,
    },
    Unknown(String),
}

#[derive(Debug, Clone)]
struct Scope {
    kind: ScopeKind,
    bindings: HashMap<String, Binding>,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            bindings: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct ScopeStack {
    scopes: Vec<Scope>,
    next_symbol: usize,
}

impl ScopeStack {
    pub(super) fn new() -> Self {
        let mut symbols = Self {
            scopes: vec![Scope::new(ScopeKind::Global)],
            next_symbol: 0,
        };
        for (name, constant) in [
            ("pi", NumericConstant::Pi),
            ("π", NumericConstant::Pi),
            ("tau", NumericConstant::Tau),
            ("τ", NumericConstant::Tau),
            ("euler", NumericConstant::Euler),
            ("ℇ", NumericConstant::Euler),
        ] {
            symbols
                .declare(name, BindingKind::Constant(constant))
                .expect("built-in names are distinct");
        }
        for name in ["U", "gphase"] {
            symbols
                .declare(name, BindingKind::Gate)
                .expect("built-in gate names are distinct");
        }
        symbols
    }

    pub(super) fn enter(&mut self, kind: ScopeKind) {
        assert_ne!(kind, ScopeKind::Global);
        self.scopes.push(Scope::new(kind));
    }

    pub(super) fn exit(&mut self) {
        assert!(self.scopes.len() > 1, "cannot exit the global scope");
        self.scopes.pop();
    }

    pub(super) fn current_kind(&self) -> ScopeKind {
        self.scopes.last().expect("global scope exists").kind
    }

    pub(super) fn declare(
        &mut self,
        name: impl Into<String>,
        kind: BindingKind,
    ) -> Result<Binding, ScopeError> {
        let name = name.into();
        let current_kind = self.current_kind();
        if matches!(kind, BindingKind::QuantumRegister { .. }) && current_kind != ScopeKind::Global
        {
            return Err(ScopeError::IllegalDeclaration {
                declaration: "qubit",
                scope: current_kind,
            });
        }
        if matches!(kind, BindingKind::Gate) && current_kind != ScopeKind::Global {
            return Err(ScopeError::IllegalDeclaration {
                declaration: kind.description(),
                scope: current_kind,
            });
        }
        if self
            .scopes
            .last()
            .expect("global scope exists")
            .bindings
            .contains_key(&name)
        {
            return Err(ScopeError::AlreadyDeclared(name));
        }
        if self
            .scopes
            .iter()
            .rev()
            .filter_map(|scope| scope.bindings.get(&name))
            .any(|binding| !binding.kind.can_be_shadowed())
        {
            return Err(ScopeError::CannotShadow(name));
        }

        let binding = Binding {
            id: SymbolId(self.next_symbol),
            kind,
        };
        self.next_symbol += 1;
        self.scopes
            .last_mut()
            .expect("global scope exists")
            .bindings
            .insert(name, binding);
        Ok(binding)
    }

    pub(super) fn lookup(&self, name: &str) -> Result<Binding, ScopeError> {
        for scope in self.scopes.iter().rev() {
            let Some(binding) = scope.bindings.get(name).copied() else {
                continue;
            };
            return Ok(binding);
        }
        Err(ScopeError::Unknown(name.to_owned()))
    }

    pub(super) fn declare_standard_gates(&mut self) -> Result<(), ScopeError> {
        for name in [
            "p", "x", "y", "z", "h", "s", "sdg", "t", "tdg", "sx", "rx", "ry", "rz", "cx", "cy",
            "cz", "cp", "crx", "cry", "crz", "ch", "swap", "ccx", "cswap", "cu", "CX", "phase",
            "cphase", "id", "u1", "u2", "u3",
        ] {
            self.declare(name, BindingKind::Gate)?;
        }
        Ok(())
    }
}
