pub(crate) mod constraint_rows;

// Compatibility exports: OpenQASM input handling belongs to IQIR.
pub use iqir::frontend::{
    OpenQasmSource, OpenQasmSourceError, load_openqasm_source, openqasm_version,
};
