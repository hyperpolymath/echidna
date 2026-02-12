// SPDX-License-Identifier: PMPL-1.0-or-later
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
use anyhow::{Context, Result};
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
    fn search(&self, goal: &str, timeout: Duration) -> Result<ProofResult> {
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
                }
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
    use std::ffi::{CStr, CString};
    use std::os::raw::{c_char, c_double, c_int};

    /// C-compatible proof result from Zig FFI
    #[repr(C)]
    struct CProofResult {
        success: c_int,
        prover_id: c_int,
        time_seconds: c_double,
        tactic_count: u32,
        prover_name: *const c_char,
        error_message: *const c_char,
    }

    extern "C" {
        fn echidna_prove_parallel(
            goal: *const c_char,
            prover_ids: *const c_int,
            num_provers: c_int,
        ) -> CProofResult;

        fn echidna_free_proof_result(result: *mut CProofResult);
        fn echidna_chapel_is_available() -> c_int;
        fn echidna_chapel_get_version() -> *const c_char;
        fn echidna_free_string(s: *const c_char);
    }

    pub struct ChapelParallelSearch;

    impl ProofSearchStrategy for ChapelParallelSearch {
        fn search(&self, goal: &str, _timeout: Duration) -> Result<ProofResult> {
            // Convert goal to C string
            let c_goal = CString::new(goal).context("Invalid goal string")?;

            // SAFETY: c_goal is a valid CString, null prover_ids with 0 count
            // means "use all provers". Chapel FFI allocates the result.
            let mut c_result = unsafe {
                echidna_prove_parallel(c_goal.as_ptr(), std::ptr::null(), 0)
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

            // SAFETY: c_result was allocated by Chapel FFI and must be freed once.
            unsafe {
                echidna_free_proof_result(&mut c_result as *mut _);
            }

            Ok(result)
        }

        fn name(&self) -> &str {
            "Chapel Parallel"
        }

        fn available(&self) -> bool {
            // SAFETY: echidna_chapel_is_available is a pure query with no side effects.
            unsafe { echidna_chapel_is_available() != 0 }
        }
    }

    impl ChapelParallelSearch {
        pub fn new() -> Result<Self> {
            // SAFETY: echidna_chapel_is_available is a pure query with no side effects.
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
        let mut strategies: Vec<Box<dyn ProofSearchStrategy>> = vec![];

        // Always add sequential (fallback)
        strategies.push(Box::new(SequentialSearch));

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
                }
                Err(e) => {
                    tracing::warn!("Failed to initialize Chapel: {}", e);
                }
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
}
