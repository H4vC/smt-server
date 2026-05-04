use std::process::{Command, Stdio};

use smt_wire::BinaryRequest;

use crate::backend::{Backend, QueryResult};

/// CLI adapter for installations that provide a `z3` executable on `PATH`.
///
/// The full expression-to-SMT-LIB translation is filled in by later phases;
/// until then this backend reports `UNKNOWN` instead of failing the server.
#[derive(Debug, Clone)]
pub struct Z3CliBackend {
    executable: String,
}

impl Default for Z3CliBackend {
    fn default() -> Self {
        Self {
            executable: "z3".to_owned(),
        }
    }
}

impl Z3CliBackend {
    pub fn new(executable: impl Into<String>) -> Self {
        Self {
            executable: executable.into(),
        }
    }

    pub fn is_available(&self) -> bool {
        Command::new(&self.executable)
            .arg("--version")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|status| status.success())
            .unwrap_or(false)
    }
}

impl Backend for Z3CliBackend {
    fn name(&self) -> &'static str {
        "z3-cli"
    }

    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        if self.is_available() {
            Ok(QueryResult::unknown(
                "z3 CLI backend translation is not enabled in this phase",
            ))
        } else {
            Ok(QueryResult::unknown("z3 executable is not available"))
        }
    }
}
