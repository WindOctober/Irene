use std::fs;
use std::path::{Path, PathBuf};

use oq3_lexer::{TokenKind, tokenize};
use thiserror::Error;

use crate::ir::OpenQasmVersion;

#[derive(Debug, Error)]
pub enum OpenQasmSourceError {
    #[error("failed to read {path}: {source}")]
    Read {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("missing or malformed OPENQASM version declaration")]
    InvalidVersionDeclaration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenQasmSource {
    pub version: OpenQasmVersion,
    pub text: String,
}

/// Reads an OpenQASM file and returns its source text together with the
/// version declared in its `OPENQASM` header.
pub fn load_openqasm_source(path: impl AsRef<Path>) -> Result<OpenQasmSource, OpenQasmSourceError> {
    let path = path.as_ref();
    let text = fs::read_to_string(path).map_err(|source| OpenQasmSourceError::Read {
        path: path.to_path_buf(),
        source,
    })?;
    let version = openqasm_version(&text)?;
    Ok(OpenQasmSource { version, text })
}

/// Parses the version declaration at the beginning of an OpenQASM source.
///
/// The OpenQASM lexer skips leading whitespace and comments. Its first
/// significant token contains `OPENQASM M.m`, followed by `;`.
pub fn openqasm_version(source: &str) -> Result<OpenQasmVersion, OpenQasmSourceError> {
    let mut offset = 0;
    let mut significant = Vec::with_capacity(2);

    for token in tokenize(source) {
        let start = offset;
        offset += token.len as usize;
        match token.kind {
            TokenKind::Whitespace | TokenKind::LineComment => continue,
            TokenKind::BlockComment { terminated: true } => continue,
            TokenKind::BlockComment { terminated: false } => {
                return Err(OpenQasmSourceError::InvalidVersionDeclaration);
            }
            kind => significant.push((kind, &source[start..offset])),
        }
        if significant.len() == 2 {
            break;
        }
    }

    let [
        (
            TokenKind::OpenQasmVersionStmt {
                major: true,
                minor: true,
            },
            declaration,
        ),
        (TokenKind::Semi, _),
    ] = significant.as_slice()
    else {
        return Err(OpenQasmSourceError::InvalidVersionDeclaration);
    };
    let number = declaration
        .strip_prefix("OPENQASM")
        .ok_or(OpenQasmSourceError::InvalidVersionDeclaration)?
        .trim();
    let (major, minor) = number.split_once('.').unwrap_or((number, "0"));
    if minor.contains('.') {
        return Err(OpenQasmSourceError::InvalidVersionDeclaration);
    }
    Ok(OpenQasmVersion {
        major: major
            .parse()
            .map_err(|_| OpenQasmSourceError::InvalidVersionDeclaration)?,
        minor: minor
            .parse()
            .map_err(|_| OpenQasmSourceError::InvalidVersionDeclaration)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_version_after_comments() {
        let source = "// generated program\n/* source format */\nOPENQASM 3.0;";
        assert_eq!(
            openqasm_version(source).unwrap(),
            OpenQasmVersion { major: 3, minor: 0 }
        );
    }
}
