// SPDX-License-Identifier: MPL-2.0
//! Test-only helper for writing an executable fixture script.
//!
//! Writing a script and executing it straight away races with every other
//! test thread that spawns a process: a `fork` taken while the write
//! descriptor is still open copies it into the child, and until that child
//! reaches `exec` (the descriptor is close-on-exec) the kernel refuses to
//! execute the file with `ETXTBSY` ("Text file busy"). That failure showed up
//! in CI as `Failed to execute fzn-chuffed --help: Text file busy`.
//!
//! [`write_executable`] closes its own descriptor and then runs the script
//! once with a sentinel argument until the kernel accepts it. After one
//! successful `exec` no writer is left and no later `fork` can inherit one,
//! so the test's own spawn cannot see `ETXTBSY`. The fixture scripts exit at
//! once on any argument they do not expect, so the probe runs no fixture body.

use std::io::{ErrorKind, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::Path;
use std::time::Duration;

/// Name the step in a failed fixture write, so a test failure says which one.
fn step(what: &'static str) -> impl FnOnce(std::io::Error) -> std::io::Error {
    move |error| std::io::Error::new(error.kind(), format!("{what}: {error}"))
}

/// Write `contents` to `path` as an owner-executable script and wait until the
/// kernel will execute it. The script must exit without side effects when
/// called with a single unexpected argument.
///
/// An error names the step that failed. The calling test decides how to fail.
pub(crate) fn write_executable(path: &Path, contents: &str) -> std::io::Result<()> {
    {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o700)
            .open(path)
            .map_err(step("create fixture executable"))?;
        file.write_all(contents.as_bytes())
            .map_err(step("write fixture executable"))?;
    }
    // The creation mode is filtered by the umask; set it explicitly so the
    // fixture is executable whatever umask the test runner inherited.
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))
        .map_err(step("make fixture executable"))?;
    for _ in 0..200 {
        match std::process::Command::new(path)
            .arg("--echidna-fixture-ready")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
        {
            Err(error) if error.kind() == ErrorKind::ExecutableFileBusy => {
                std::thread::sleep(Duration::from_millis(10));
            },
            Err(error) => return Err(step("fixture executable cannot run")(error)),
            Ok(_) => return Ok(()),
        }
    }
    Err(std::io::Error::new(
        ErrorKind::ExecutableFileBusy,
        "fixture executable stayed busy (ETXTBSY) for 2 s",
    ))
}
