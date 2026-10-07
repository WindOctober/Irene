use std::collections::HashMap;

use crate::{NumericConstant, NumericType, SymbolId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ScopeKind {
    Global,
    Block,
    Subroutine,
}

/// Source-level shape of a quantum binding.
///
/// OpenQASM distinguishes `qubit q` from `qubit[1] q`. Both contain one
/// quantum wire, but only the former is a scalar operand that may be
/// broadcast against a register operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum QuantumType {
    Scalar,
    Register { width: usize },
}

impl QuantumType {
    pub(super) fn width(self) -> usize {
        match self {
            Self::Scalar => 1,
            Self::Register { width } => width,
        }
    }
}

/// Source-level shape of a classical bit binding.
///
/// `bool b`, `bit c`, and `bit[1] cs` have distinct storage types even though
/// each stores one binary value. Frontend type checking retains this
/// distinction while allowing the language's implicit scalar bool/bit casts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BitType {
    Bool,
    Bit,
    Register { width: usize },
    Angle { width: usize },
    Uint { width: usize, explicit_width: bool },
}

impl BitType {
    pub(super) fn width(self) -> usize {
        match self {
            Self::Bool | Self::Bit => 1,
            Self::Register { width } | Self::Angle { width } | Self::Uint { width, .. } => width,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BindingKind {
    QuantumVariable(QuantumType),
    QuantumParameter(QuantumType),
    ClassicalBit(BitType),
    NumericInput(NumericType),
    Gate,
    Subroutine {
        index: usize,
    },
    Constant(NumericConstant),
    /// IEEE value retained as bits, not replaced by a symbolic multiple of pi.
    StaticFloat {
        bits: u64,
        width: u32,
    },
    StaticBits {
        value: u64,
        ty: BitType,
    },
    /// Exact, range-checked static integer; a specialized loop value is not const.
    StaticInteger {
        value: i128,
        width: u32,
        signed: bool,
        explicit_width: bool,
        is_const: bool,
    },
}

impl BindingKind {
    fn can_be_shadowed(self) -> bool {
        !matches!(self, Self::Gate | Self::Subroutine { .. })
    }

    pub(super) fn description(self) -> &'static str {
        match self {
            Self::QuantumVariable(QuantumType::Scalar) => "qubit",
            Self::QuantumVariable(QuantumType::Register { .. }) => "quantum register",
            Self::QuantumParameter(_) => "quantum parameter",
            Self::ClassicalBit(BitType::Bool) => "Boolean",
            Self::ClassicalBit(BitType::Bit) => "classical bit",
            Self::ClassicalBit(BitType::Register { .. }) => "classical bit register",
            Self::ClassicalBit(BitType::Angle { .. }) => "fixed-width angle",
            Self::ClassicalBit(BitType::Uint { .. }) => "unsigned integer",
            Self::NumericInput(_) => "numeric input",
            Self::Gate => "gate",
            Self::Subroutine { .. } => "subroutine",
            Self::Constant(_) => "constant",
            Self::StaticFloat { .. } | Self::StaticBits { .. } => "constant",
            Self::StaticInteger { .. } => "static integer",
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
    global_before: Option<SymbolId>,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            bindings: HashMap::new(),
            global_before: None,
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct ScopeStack {
    scopes: Vec<Scope>,
    next_symbol: usize,
}

impl ScopeStack {
    pub(super) fn global_static_ids(&self) -> std::collections::BTreeSet<SymbolId> {
        self.scopes[0]
            .bindings
            .values()
            .filter_map(|binding| {
                matches!(
                    binding.kind,
                    BindingKind::StaticInteger { .. }
                        | BindingKind::StaticFloat { .. }
                        | BindingKind::StaticBits { .. }
                )
                .then_some(binding.id)
            })
            .collect()
    }

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

    /// Creates the smaller built-in namespace defined by OpenQASM 2.0.
    ///
    /// Unlike OpenQASM 3, version 2 has only `pi` as a numeric constant and
    /// reserves the uppercase primitive gates `U` and `CX`.  The names from
    /// `qelib1.inc` are installed separately at the include site.
    pub(super) fn new_openqasm2() -> Self {
        let mut symbols = Self {
            scopes: vec![Scope::new(ScopeKind::Global)],
            next_symbol: 0,
        };
        symbols
            .declare("pi", BindingKind::Constant(NumericConstant::Pi))
            .expect("the OpenQASM 2 built-in namespace is initially empty");
        for name in ["U", "CX"] {
            symbols
                .declare(name, BindingKind::Gate)
                .expect("OpenQASM 2 built-in gate names are distinct");
        }
        symbols
    }

    pub(super) fn enter(&mut self, kind: ScopeKind) {
        assert_ne!(kind, ScopeKind::Global);
        self.scopes.push(Scope::new(kind));
    }

    /// Reuse the callable scope rules, but resolve globals at definition time.
    /// Symbol IDs are monotonic, so the definition's ID excludes itself and
    /// all later declarations without cloning a symbol table or lowering body.
    pub(super) fn enter_definition(&mut self, definition: SymbolId) {
        self.enter(ScopeKind::Subroutine);
        self.scopes.last_mut().expect("entered scope").global_before = Some(definition);
    }

    pub(super) fn exit(&mut self) {
        assert!(self.scopes.len() > 1, "cannot exit the global scope");
        self.scopes.pop();
    }

    pub(super) fn current_kind(&self) -> ScopeKind {
        self.scopes.last().expect("global scope exists").kind
    }

    /// Declares a name in the innermost scope and allocates its program-local
    /// symbol ID. Declaration-site restrictions are checked before insertion.
    pub(super) fn declare(
        &mut self,
        name: impl Into<String>,
        kind: BindingKind,
    ) -> Result<Binding, ScopeError> {
        let name = name.into();
        let current_kind = self.current_kind();
        if matches!(kind, BindingKind::QuantumVariable(_)) && current_kind != ScopeKind::Global {
            return Err(ScopeError::IllegalDeclaration {
                declaration: "qubit",
                scope: current_kind,
            });
        }
        if matches!(kind, BindingKind::QuantumParameter(_)) && current_kind != ScopeKind::Subroutine
        {
            return Err(ScopeError::IllegalDeclaration {
                declaration: "quantum parameter",
                scope: current_kind,
            });
        }
        if matches!(kind, BindingKind::Gate | BindingKind::Subroutine { .. })
            && current_kind != ScopeKind::Global
        {
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

    /// Resolves the nearest lexically visible binding.
    ///
    /// During call-site specialization, a callee may see its own parameters
    /// and callable global names, but cannot capture caller locals or global
    /// mutable storage.
    pub(super) fn lookup(&self, name: &str) -> Result<Binding, ScopeError> {
        let subroutine_scope = self
            .scopes
            .iter()
            .rposition(|scope| scope.kind == ScopeKind::Subroutine);
        for (index, scope) in self.scopes.iter().enumerate().rev() {
            // Call-site specialization may temporarily nest two subroutine
            // scopes. Name lookup remains lexical: the callee cannot capture
            // parameters or locals from its caller.
            if subroutine_scope.is_some_and(|boundary| index < boundary)
                && scope.kind != ScopeKind::Global
            {
                continue;
            }
            let Some(binding) = scope.bindings.get(name).copied() else {
                continue;
            };
            if scope.kind == ScopeKind::Global
                && subroutine_scope
                    .and_then(|boundary| self.scopes[boundary].global_before)
                    .is_some_and(|limit| binding.id >= limit)
            {
                continue;
            }
            if subroutine_scope.is_some()
                && scope.kind == ScopeKind::Global
                && !matches!(
                    binding.kind,
                    BindingKind::Constant(_)
                        | BindingKind::Gate
                        | BindingKind::Subroutine { .. }
                        | BindingKind::StaticInteger { is_const: true, .. }
                        | BindingKind::StaticFloat { .. }
                        | BindingKind::StaticBits { .. }
                )
            {
                continue;
            }
            return Ok(binding);
        }
        Err(ScopeError::Unknown(name.to_owned()))
    }

    /// Adds `stdgates.inc` names and supported corpus extensions (such as CCZ).
    pub(super) fn declare_standard_gates(&mut self) -> Result<(), ScopeError> {
        for name in [
            "p", "x", "y", "z", "h", "s", "sdg", "t", "tdg", "sx", "rx", "ry", "rz", "cx", "cy",
            "cz", "cp", "crx", "cry", "crz", "ch", "swap", "ccx", "cswap", "cu", "CX", "phase",
            "cphase", "id", "u1", "u2", "u3", "ccz",
        ] {
            self.declare(name, BindingKind::Gate)?;
        }
        Ok(())
    }

    /// Adds the canonical `qelib1.inc` names and the small set of historical
    /// Qiskit aliases and extensions used by Irene's frozen OpenQASM 2 corpora.
    pub(super) fn declare_qelib1_gates(&mut self) -> Result<(), ScopeError> {
        for name in [
            "u3", "u2", "u1", "cx", "id", "u0", "u", "p", "x", "y", "z", "h", "s", "sdg", "t",
            "tdg", "rx", "ry", "rz", "sx", "sxdg", "cz", "cy", "swap", "ch", "ccx", "cswap", "crx",
            "cry", "crz", "cu1", "cp", "cu3", "ccz",
        ] {
            self.declare(name, BindingKind::Gate)?;
        }
        Ok(())
    }
}
