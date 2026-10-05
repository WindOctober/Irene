//! Import supported OpenQASM 2/3 programs into IQIR without a verifier.
//!
//! Use [parse_str] or [parse_file] to select the frontend from the source header,
//! or the version-specific modules to retain their original error types.

use std::path::Path;

use crate::{OpenQasmVersion, Program};

pub mod openqasm2;
pub mod openqasm3;
mod scope;
mod source;

pub use source::{OpenQasmSource, OpenQasmSourceError, load_openqasm_source, openqasm_version};

#[derive(Debug, thiserror::Error)]
pub enum ImportError {
    #[error(transparent)]
    Source(#[from] OpenQasmSourceError),
    #[error("unsupported OpenQASM version {major}.{minor}", major = .0.major, minor = .0.minor)]
    UnsupportedVersion(OpenQasmVersion),
    #[error(transparent)]
    OpenQasm2(#[from] openqasm2::FrontendError),
    #[error(transparent)]
    OpenQasm3(#[from] openqasm3::FrontendError),
}

/// Parses a self-contained source using its declared OpenQASM major version.
/// The selected frontend retains its existing language and include restrictions.
/// `source_name` is a diagnostic label, not an include-search directory.
pub fn parse_str(source: &str, source_name: &str) -> Result<Program, ImportError> {
    parse_versioned(source, source_name, openqasm_version(source)?)
}

/// Reads a UTF-8 OpenQASM file and lowers it to IQIR.
/// This does not enable additional include resolution or run verification.
pub fn parse_file(path: impl AsRef<Path>) -> Result<Program, ImportError> {
    let path = path.as_ref();
    let source = load_openqasm_source(path)?;
    parse_versioned(&source.text, &path.to_string_lossy(), source.version)
}

fn parse_versioned(
    source: &str,
    source_name: &str,
    version: OpenQasmVersion,
) -> Result<Program, ImportError> {
    match version.major {
        2 => Ok(openqasm2::parse_str(source, source_name)?),
        3 => Ok(openqasm3::parse_str(source, source_name)?),
        _ => Err(ImportError::UnsupportedVersion(version)),
    }
}

#[cfg(test)]
mod tests;
