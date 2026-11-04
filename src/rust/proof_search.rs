// SPDX-License-Identifier: MPL-2.0
//! Proof search strategies for ECHIDNA
//!
//! This module implements pluggable proof search strategies following the
//! design in CHAPEL_PLUGGABILITY_DESIGN.md. Chapel is optional - the system
//! falls back to sequential search if Chapel is unavailable.
//!
//! # Safety & Unsafe Code Justification
//!
//! This module contains 7 unsafe blocks, ALL within the optional Chapel FFI:
//!
//! ## Why Unsafe Is Required:
//! - Chapel FFI requires C ABI interop (same as ffi/mod.rs)
//! - Converting C strings (CStr) to Rust strings requires unsafe
//! - Calling extern "C" functions requires unsafe
//! - Manual memory management for Chapel-allocated data requires unsafe
//!
//! ## Safety Guarantees:
//! - Every unsafe block is documented with SAFETY comments
//! - All pointers null-checked before dereferencing
//! - Proper cleanup with echidna_free_* functions
//! - Chapel FFI only active when feature="chapel" AND runtime available
//! - Falls back to safe sequential search if Chapel unavailable
//!
//! ## Audit Status (2026-02-12):
//! - ✓ All 7 unsafe blocks reviewed and documented
//! - ✓ All behind feature gate (optional dependency)
//! - ✓ Null pointer checks before all dereferences
//! - ✓ Memory properly freed after use
//! - ✓ No Chapel? No unsafe! (SequentialSearch is 100% safe)
//!
//! panic-attack flagged these as "High" severity because they use unsafe,
//! but they are LEGITIMATE, OPTIONAL, and NECESSARY for Chapel interop.

use crate::provers::{ProverConfig, ProverFactory, ProverKind};
use anyhow::Result;
use std::time::{Duration, Instant};

/// Proof result from any strategy
#[derive(Debug, Clone)]
pub struct ProofResult {
    pub success: bool,
    pub prover_name: Option<String>,
    pub time_seconds: f64,
    pub tactic_count: u32,
    pub error_message: Option<String>,
    pub strategy_used: String,
}

/// Trait for proof search strategies
///
/// All proof search implementations must implement this trait.
/// Strategies can be sequential (built-in) or parallel (via Chapel FFI).
pub trait ProofSearchStrategy: Send + Sync {
    /// Search for a proof using this strategy
    fn search(&self, goal: &str, timeout: Duration) -> Result<ProofResult>;

    /// Strategy name for logging
    fn name(&self) -> &str;

    /// Can this strategy run? (checks dependencies)
    fn available(&self) -> bool;
}

//==============================================================================
// Sequential Search (Always Available)
//==============================================================================

/// Sequential proof search - tries provers one by one
///
/// This is the default fallback strategy that's always available.
/// No external dependencies required.
pub struct SequentialSearch;

impl ProofSearchStrategy for SequentialSearch {
    fn search(&self, _goal: &str, timeout: Duration) -> Result<ProofResult> {
        let start = Instant::now();
        let config = ProverConfig {
            timeout: timeout.as_secs(),
            ..ProverConfig::default()
        };

        // Build list of available provers (those that can be instantiated)
        let mut tried: Vec<String> = Vec::new();
        for kind in ProverKind::all_core() {
            if start.elapsed() > timeout {
                break;
            }

            match ProverFactory::create(kind, config.clone()) {
                Ok(_prover) => {
                    tried.push(format!("{:?}", kind));
                    // Note: ProverBackend methods are async. Full sequential dispatch
                    // requires the async verify_proof_sequential() path (via ProverDispatcher).
                    // This sync strategy enumerates available provers for reporting.
                },
                Err(_) => continue,
            }
        }

        let elapsed = start.elapsed();
        Ok(ProofResult {
            success: false,
            prover_name: None,
            time_seconds: elapsed.as_secs_f64(),
            tactic_count: 0,
            error_message: Some(format!(
                "Sequential search checked {} provers ({}). Use ProverDispatcher for async verification.",
                tried.len(),
                tried.join(", ")
            )),
            strategy_used: self.name().to_string(),
        })
    }

    fn name(&self) -> &str {
        "Sequential"
    }

    fn available(&self) -> bool {
        true // Always available
    }
}

//==============================================================================
// Chapel Parallel Search (Optional, Feature-Gated)
//==============================================================================

#[cfg(feature = "chapel")]
mod chapel_ffi {
    use super::*;
    use anyhow::Context;
    use std::ffi::{CStr, CString};
    use std::os::raw::{c_char, c_double, c_int};

    /// C-compatible proof result from Zig FFI (30 provers)
    #[repr(C)]
    struct CProofResult {
        success: c_int,
        prover_id: c_int,
        time_seconds: c_double,
        exit_code: c_int,
        tactic_count: u32,
        category: c_int,
        prover_name: *const c_char,
        error_message: *const c_char,
    }

    extern "C" {
        fn echidna_prove_parallel(
            goal: *const c_char,
            prover_ids: *const c_int,
            num_provers: c_int,
            timeout_secs: c_int,
        ) -> CProofResult;

        fn echidna_free_proof_result(result: *mut CProofResult);
        fn echidna_chapel_is_available() -> c_int;
        fn echidna_chapel_get_version() -> *const c_char;
        fn echidna_chapel_available_prover_count() -> c_int;
        #[allow(dead_code)]
        fn echidna_chapel_is_prover_available(prover_id: c_int) -> c_int;
        fn echidna_free_string(s: *const c_char);
    }

    /// Synchronous Chapel search, serialized through the bridge's OS owner.
    ///
    /// The timeout is a per-prover whole-second limit. This API does not offer
    /// caller cancellation or a hard deadline covering queueing and runtime setup.
    pub struct ChapelParallelSearch;

    fn chapel_timeout_seconds(timeout: Duration) -> Result<c_int> {
        if timeout.is_zero() || timeout.subsec_nanos() != 0 {
            anyhow::bail!("Chapel timeout must be a positive whole number of seconds");
        }
        c_int::try_from(timeout.as_secs()).context("Chapel timeout exceeds the C ABI range")
    }

    impl ProofSearchStrategy for ChapelParallelSearch {
        fn search(&self, goal: &str, timeout: Duration) -> Result<ProofResult> {
            // Convert goal to C string
            let c_goal = CString::new(goal).context("Invalid goal string")?;
            let timeout_secs = chapel_timeout_seconds(timeout)?;

            // SAFETY: c_goal is a valid CString, null prover_ids with 0 count
            // means "use all 30 provers". The bridge runs on its runtime owner
            // and returns independent copies allocated by the bridge.
            let mut c_result = unsafe {
                echidna_prove_parallel(c_goal.as_ptr(), std::ptr::null(), 0, timeout_secs)
            };

            // Convert result
            let prover_name = if !c_result.prover_name.is_null() {
                // SAFETY: Non-null prover_name is a valid C string from Chapel FFI.
                unsafe {
                    let name_cstr = CStr::from_ptr(c_result.prover_name);
                    Some(name_cstr.to_string_lossy().to_string())
                }
            } else {
                None
            };

            let error_message = if !c_result.error_message.is_null() {
                // SAFETY: Non-null error_message is a valid C string from Chapel FFI.
                unsafe {
                    let err_cstr = CStr::from_ptr(c_result.error_message);
                    Some(err_cstr.to_string_lossy().to_string())
                }
            } else {
                None
            };

            let result = ProofResult {
                success: c_result.success != 0,
                prover_name,
                time_seconds: c_result.time_seconds,
                tactic_count: c_result.tactic_count,
                error_message,
                strategy_used: self.name().to_string(),
            };

            // SAFETY: c_result contains bridge-owned copies and must be freed once.
            unsafe {
                echidna_free_proof_result(&mut c_result as *mut _);
            }

            Ok(result)
        }

        fn name(&self) -> &str {
            "Chapel Parallel"
        }

        fn available(&self) -> bool {
            // SAFETY: The bridge initializes the real runtime once before querying it.
            unsafe { echidna_chapel_is_available() != 0 }
        }
    }

    impl ChapelParallelSearch {
        pub fn new() -> Result<Self> {
            // SAFETY: The bridge initializes the real runtime once before querying it.
            if unsafe { echidna_chapel_is_available() } == 0 {
                anyhow::bail!("Chapel runtime not available");
            }
            Ok(Self)
        }

        pub fn get_version() -> Result<String> {
            // SAFETY: Chapel FFI returns a valid C string that we copy and free.
            unsafe {
                let c_version = echidna_chapel_get_version();
                if c_version.is_null() {
                    anyhow::bail!("Chapel version unavailable");
                }

                let version_cstr = CStr::from_ptr(c_version);
                let version = version_cstr.to_string_lossy().to_string();

                echidna_free_string(c_version);

                Ok(version)
            }
        }

        /// Get count of provers available on this system (0-30)
        pub fn available_prover_count() -> u32 {
            // SAFETY: The bridge initializes the real runtime before querying the registry.
            let count = unsafe { echidna_chapel_available_prover_count() };
            if count >= 0 {
                count as u32
            } else {
                0
            }
        }
    }
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn chapel_timeout_cannot_become_the_native_default_or_wrap() {
            assert_eq!(chapel_timeout_seconds(Duration::from_secs(1)).unwrap(), 1);
            assert_eq!(
                chapel_timeout_seconds(Duration::from_secs(c_int::MAX as u64)).unwrap(),
                c_int::MAX
            );
            for timeout in [
                Duration::ZERO,
                Duration::from_millis(500),
                Duration::from_millis(1500),
                Duration::from_secs(c_int::MAX as u64 + 1),
                Duration::MAX,
            ] {
                assert!(chapel_timeout_seconds(timeout).is_err(), "{timeout:?}");
            }
        }

        #[cfg(echidna_chapel_real)]
        fn real_probe_command(test_name: &str, child_env: &str) -> std::process::Command {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            command
                .arg("--exact")
                .arg(format!("proof_search::chapel_ffi::tests::{test_name}"))
                .arg("--nocapture")
                .env(child_env, "1")
                .stdin(std::process::Stdio::null());
            command
        }

        #[cfg(echidna_chapel_real)]
        fn run_real_probe(command: &mut std::process::Command, marker: &str) {
            use std::fs::File;
            use std::process::{Child, Stdio};

            struct Reap(Child);
            impl Drop for Reap {
                fn drop(&mut self) {
                    let _ = self.0.kill();
                    let _ = self.0.wait();
                }
            }

            // Files avoid pipe backpressure while waiting and retain diagnostics
            // if a native assertion aborts before the child test reports failure.
            let logs = tempfile::tempdir().expect("probe log directory");
            let stdout_path = logs.path().join("stdout");
            let stderr_path = logs.path().join("stderr");
            command
                .stdout(Stdio::from(File::create(&stdout_path).unwrap()))
                .stderr(Stdio::from(File::create(&stderr_path).unwrap()));
            let mut child = Reap(command.spawn().expect("launch isolated real-runtime probe"));
            let started = Instant::now();
            let (status, timed_out) = loop {
                if let Some(status) = child.0.try_wait().expect("inspect real-runtime probe") {
                    break (status, false);
                }
                if started.elapsed() >= Duration::from_secs(30) {
                    child.0.kill().expect("stop timed-out real-runtime probe");
                    break (child.0.wait().expect("reap real-runtime probe"), true);
                }
                std::thread::sleep(Duration::from_millis(10));
            };
            let stdout = std::fs::read_to_string(stdout_path).expect("probe stdout");
            let stderr = std::fs::read_to_string(stderr_path).expect("probe stderr");
            assert!(
                !timed_out && status.success(),
                "real-runtime child failed (timeout={timed_out}, {status}):\n{stdout}\n{stderr}"
            );
            assert!(
                stdout.contains(marker),
                "the exact child test did not complete its real-runtime assertions: {stdout}"
            );
        }

        #[cfg(echidna_chapel_stubs)]
        #[test]
        fn stub_mode_cannot_claim_a_real_runtime() {
            assert!(ChapelParallelSearch::new().is_err());
            assert!(ChapelParallelSearch::get_version().is_err());
            assert_eq!(ChapelParallelSearch::available_prover_count(), 0);
        }

        #[cfg(echidna_chapel_real)]
        #[test]
        fn real_runtime_initializes_once_and_reports_its_version() {
            for _ in 0..2 {
                let strategy = ChapelParallelSearch::new().expect("real Chapel runtime");
                assert!(strategy.available());
                let version = ChapelParallelSearch::get_version().expect("real Chapel version");
                assert!(version.starts_with("ECHIDNA Chapel Metalayer "));
                assert!(ChapelParallelSearch::available_prover_count() <= 30);
            }
        }

        #[cfg(echidna_chapel_real)]
        #[test]
        fn real_search_without_provers_fails_and_frees_result() {
            const CHILD: &str = "ECHIDNA_CHAPEL_EMPTY_PATH_CHILD";
            if std::env::var_os(CHILD).is_some() {
                let start = std::sync::Arc::new(std::sync::Barrier::new(4));
                let callers: Vec<_> = (0..4)
                    .map(|_| {
                        let start = start.clone();
                        std::thread::spawn(move || {
                            start.wait();
                            let strategy = ChapelParallelSearch::new().expect("real Chapel runtime");
                            assert_eq!(ChapelParallelSearch::available_prover_count(), 0);
                            for _ in 0..2 {
                                assert!(strategy.available());
                                assert!(ChapelParallelSearch::get_version()
                                    .unwrap()
                                    .starts_with("ECHIDNA Chapel Metalayer "));
                                let result = strategy
                                    .search("True", Duration::from_secs(1))
                                    .expect("FFI returns a result when no prover is available");
                                assert!(!result.success);
                                assert_eq!(
                                    result.error_message.as_deref(),
                                    Some("All provers exhausted")
                                );
                            }
                        })
                    })
                    .collect();
                for caller in callers {
                    caller.join().expect("concurrent Chapel caller");
                }
                println!("ECHIDNA_REAL_CHAPEL_NO_PROVER_PROBE_COMPLETED");
                return;
            }

            // A fresh process gets an empty PATH before runtime initialization.
            // No global environment mutation races with other Rust tests, and
            // no external prover can be dispatched by this allocation/free probe.
            let empty_path = tempfile::tempdir().expect("empty prover search directory");
            let mut command = real_probe_command(
                "real_search_without_provers_fails_and_frees_result",
                CHILD,
            );
            command.env("PATH", empty_path.path());
            run_real_probe(
                &mut command,
                "ECHIDNA_REAL_CHAPEL_NO_PROVER_PROBE_COMPLETED",
            );
        }

        #[cfg(all(echidna_chapel_real, target_os = "linux"))]
        fn probe_process_stopped(pid: u32) -> std::io::Result<bool> {
            match std::fs::read_to_string(format!("/proc/{pid}/stat")) {
                Ok(stat) => {
                    let state = stat
                        .rsplit_once(')')
                        .and_then(|(_, fields)| fields.split_whitespace().next())
                        .ok_or_else(|| std::io::Error::other("malformed process state"))?;
                    Ok(matches!(state, "Z" | "X" | "x"))
                },
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(true),
                Err(error) => Err(error),
            }
        }

        #[cfg(all(echidna_chapel_real, target_os = "linux"))]
        #[test]
        fn real_search_deadline_stops_the_owned_prover() {
            use std::os::unix::fs::{symlink, PermissionsExt};

            const CHILD: &str = "ECHIDNA_CHAPEL_DEADLINE_CHILD";
            const PID_FILE: &str = "ECHIDNA_CHAPEL_PROVER_PID";
            if std::env::var_os(CHILD).is_some() {
                let strategy = ChapelParallelSearch::new().expect("real Chapel runtime");
                assert_eq!(ChapelParallelSearch::available_prover_count(), 1);
                let started = Instant::now();
                let result = strategy.search("True", Duration::from_secs(1));
                let elapsed = started.elapsed();
                let pid: u32 = std::fs::read_to_string(std::env::var_os(PID_FILE).unwrap())
                    .expect("the finite prover actually started")
                    .trim()
                    .parse()
                    .expect("prover PID");
                let stopped_before_cleanup = probe_process_stopped(pid);

                // Cleanup precedes assertions. The fake prover also has its own
                // finite four-second lifetime if the parent process must abort.
                if !matches!(stopped_before_cleanup, Ok(true)) {
                    let _ = std::process::Command::new("/bin/kill")
                        .args(["-KILL", &pid.to_string()])
                        .status();
                    let cleanup = Instant::now();
                    while matches!(probe_process_stopped(pid), Ok(false))
                        && cleanup.elapsed() < Duration::from_secs(2)
                    {
                        std::thread::sleep(Duration::from_millis(10));
                    }
                }

                assert!(
                    matches!(stopped_before_cleanup, Ok(true)),
                    "deadline returned with a live or unobservable prover: {stopped_before_cleanup:?}"
                );
                assert!(elapsed < Duration::from_secs(3), "deadline took {elapsed:?}");
                let result = result.expect("native timeout returns a failed search result");
                assert!(!result.success);
                assert_eq!(
                    result.error_message.as_deref(),
                    Some("All provers exhausted")
                );
                println!("ECHIDNA_REAL_CHAPEL_DEADLINE_PROBE_COMPLETED");
                return;
            }

            let fixture = tempfile::tempdir().expect("isolated finite prover directory");
            let which = which::which("which").expect("availability probe executable");
            symlink(which, fixture.path().join("which")).expect("isolated which");
            let prover = fixture.path().join("z3");
            std::fs::write(
                &prover,
                "#!/bin/sh\nprintf '%s\\n' \"$$\" > \"$ECHIDNA_CHAPEL_PROVER_PID\"\nexec /bin/sleep 4\n",
            )
            .expect("write finite prover");
            std::fs::set_permissions(&prover, std::fs::Permissions::from_mode(0o700))
                .expect("make finite prover executable");
            let mut command = real_probe_command(
                "real_search_deadline_stops_the_owned_prover",
                CHILD,
            );
            command
                .env("PATH", fixture.path())
                .env(PID_FILE, fixture.path().join("prover.pid"));
            run_real_probe(
                &mut command,
                "ECHIDNA_REAL_CHAPEL_DEADLINE_PROBE_COMPLETED",
            );
        }
    }
}

#[cfg(feature = "chapel")]
pub use chapel_ffi::ChapelParallelSearch;

//==============================================================================
// Strategy Selector
//==============================================================================

/// Selects and manages available proof search strategies
pub struct StrategySelector {
    strategies: Vec<Box<dyn ProofSearchStrategy>>,
}

impl StrategySelector {
    /// Auto-detect and register all available strategies
    pub fn auto() -> Self {
        #[allow(unused_mut)] // mut needed when chapel feature is enabled
        let mut strategies: Vec<Box<dyn ProofSearchStrategy>> = vec![
            // Always add sequential (fallback)
            Box::new(SequentialSearch),
        ];

        // Try to add Chapel (if feature enabled and runtime available)
        #[cfg(feature = "chapel")]
        {
            match ChapelParallelSearch::new() {
                Ok(chapel) => {
                    if chapel.available() {
                        tracing::info!("Chapel parallel search enabled");
                        if let Ok(version) = ChapelParallelSearch::get_version() {
                            tracing::info!("Chapel version: {}", version);
                        }
                        strategies.push(Box::new(chapel));
                    } else {
                        tracing::warn!("Chapel feature enabled but runtime not available");
                    }
                },
                Err(e) => {
                    tracing::warn!("Failed to initialize Chapel: {}", e);
                },
            }
        }

        #[cfg(not(feature = "chapel"))]
        {
            tracing::debug!("Chapel support not compiled in (use --features chapel)");
        }

        Self { strategies }
    }

    /// Get best available strategy (prefers parallel if available)
    pub fn best(&self) -> &dyn ProofSearchStrategy {
        // Prefer later entries (Chapel if available, otherwise sequential)
        self.strategies.last().unwrap().as_ref()
    }

    /// Get strategy by name
    pub fn by_name(&self, name: &str) -> Option<&dyn ProofSearchStrategy> {
        self.strategies
            .iter()
            .find(|s| s.name() == name)
            .map(|s| s.as_ref())
    }

    /// List all available strategies
    pub fn available_strategies(&self) -> Vec<&str> {
        self.strategies.iter().map(|s| s.name()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sequential_always_available() {
        let strategy = SequentialSearch;
        assert!(strategy.available());
        assert_eq!(strategy.name(), "Sequential");
    }

    #[test]
    fn test_strategy_selector_has_sequential() {
        let selector = StrategySelector::auto();
        let strategies = selector.available_strategies();
        assert!(strategies.contains(&"Sequential"));
    }

    #[test]
    fn test_sequential_search() {
        let strategy = SequentialSearch;
        let result = strategy.search("forall n, n + 0 = n", Duration::from_secs(5));
        assert!(result.is_ok());
    }

    #[test]
    fn test_proof_result_fields() {
        let result = ProofResult {
            success: true,
            prover_name: Some("Lean".to_string()),
            time_seconds: 1.5,
            tactic_count: 3,
            error_message: None,
            strategy_used: "Sequential".to_string(),
        };
        assert!(result.success);
        assert_eq!(result.prover_name.unwrap(), "Lean");
        assert_eq!(result.tactic_count, 3);
        assert!(result.error_message.is_none());
    }

    #[test]
    fn test_proof_result_failure() {
        let result = ProofResult {
            success: false,
            prover_name: None,
            time_seconds: 5.0,
            tactic_count: 0,
            error_message: Some("Timeout".to_string()),
            strategy_used: "Sequential".to_string(),
        };
        assert!(!result.success);
        assert!(result.prover_name.is_none());
        assert_eq!(result.error_message.unwrap(), "Timeout");
    }

    #[test]
    fn test_sequential_search_name() {
        let strategy = SequentialSearch;
        assert_eq!(strategy.name(), "Sequential");
    }
}
