// SPDX-License-Identifier: MPL-2.0

//! `echidna coprocessor`: the `echidna.coprocessor.*/1` contract on the
//! command line. This module only does I/O and exit codes; the contract
//! lives in `echidna::coprocessor_contract`. See
//! `docs/COPROCESSOR-CONTRACT.adoc`.

use super::CoprocessorCommand;
use echidna::coprocessor_contract::{self, CoprocessorResult, CoprocessorStatus};
use std::io::Read;
use std::path::PathBuf;

/// Run one `echidna coprocessor` subcommand. Never returns.
pub(crate) async fn coprocessor_command(cmd: CoprocessorCommand) -> ! {
    match cmd {
        CoprocessorCommand::Dispatch { request } => {
            let result = match read_request(request) {
                Ok(input) => coprocessor_contract::dispatch_request(&input).await,
                Err(e) => CoprocessorResult::malformed(e, 0),
            };
            emit_coprocessor_result(&result);
        },
        CoprocessorCommand::Capabilities => {
            let line = coprocessor_contract::capabilities()
                .to_jcs()
                .expect("the capabilities report holds no floats and no large integers");
            println!("{line}");
            std::process::exit(0);
        },
    }
}

/// Read the request text from `file`, or from stdin when `file` is `None`.
fn read_request(file: Option<PathBuf>) -> Result<String, String> {
    match file {
        Some(path) => std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read request file {}: {e}", path.display())),
        None => {
            let mut s = String::new();
            std::io::stdin()
                .read_to_string(&mut s)
                .map_err(|e| format!("cannot read request from stdin: {e}"))?;
            Ok(s)
        },
    }
}

/// Print `result` as its one JCS line on stdout and exit (0 iff computed).
///
/// If the value cannot be serialised, a minimal `error` object is printed
/// instead, so stdout always carries one contract object.
fn emit_coprocessor_result(result: &CoprocessorResult) -> ! {
    let (line, status) = match result.to_jcs() {
        Ok(line) => (line, result.status),
        Err(e) => (
            CoprocessorResult::malformed(format!("could not serialise result: {e}"), 0)
                .to_jcs()
                .expect("an error result with no outcome serialises"),
            CoprocessorStatus::Error,
        ),
    };
    println!("{line}");
    std::process::exit(status.exit_code());
}
