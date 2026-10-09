# Internal unit tests

`equivalence/` mirrors the verifier's module structure. Implementation modules
load these files with `#[cfg(test)]` and `#[path = "..."]`, retaining access to
private helpers without expanding the public API. Cargo runs them as library
unit tests (`cargo test --lib`), not as standalone integration-test crates.

Public API integration tests remain directly under `tests/`.
