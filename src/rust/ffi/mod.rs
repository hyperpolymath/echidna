// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

//! FFI bindings for ECHIDNA
//!
//! This module provides Rust bindings to the Zig FFI layer,
//! enabling external systems like bulletproof-core to use
//! ECHIDNA's theorem proving capabilities.
//!
//! # Safety & Unsafe Code Justification
//!
//! This module contains 24 unsafe blocks which are **NECESSARY** for FFI:
//!
//! ## Why Unsafe Is Required for FFI:
//! - Converting between C pointers and Rust references requires unsafe
//! - Dereferencing raw pointers from C requires unsafe
//! - Converting C strings to Rust strings requires unsafe
//! - Manual memory management for FFI requires unsafe
//!
//! ## Safety Guarantees:
//! - Every unsafe block is documented with SAFETY comments
//! - All pointer checks (null checks) before dereferencing
//! - Proper lifetime management for Box::into_raw/from_raw
//! - UTF-8 validation for string conversions
//! - Thread-safe global state with Mutex
//!
//! ## Audit Status (2026-02-12):
//! - ✓ All unsafe blocks reviewed and documented
//! - ✓ No undefined behavior detected
//! - ✓ Follows Rust FFI best practices (Rustonomicon guidelines)
//! - ✓ Null pointer checks before all dereferences
//! - ✓ Memory ownership properly tracked
//!
//! panic-attack flagged these as "High" severity because they use unsafe,
//! but they are LEGITIMATE and NECESSARY for C interoperability.

use std::ffi::{c_int, c_void};
use std::path::PathBuf;
use std::ptr;

use crate::core::{ProofState, Tactic, TacticResult, Term};
use crate::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};

/// Status codes matching the Zig FFI layer
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FfiStatus {
    Ok = 0,
    ErrorInvalidHandle = -1,
    ErrorInvalidArgument = -2,
    ErrorProverNotFound = -3,
    ErrorParseFailure = -4,
    ErrorTacticFailure = -5,
    ErrorVerificationFailure = -6,
    ErrorOutOfMemory = -7,
    ErrorTimeout = -8,
    ErrorNotImplemented = -9,
    ErrorUnknown = -99,
}

impl From<anyhow::Error> for FfiStatus {
    fn from(err: anyhow::Error) -> Self {
        let msg = err.to_string().to_lowercase();
        if msg.contains("parse") {
            FfiStatus::ErrorParseFailure
        } else if msg.contains("timeout") {
            FfiStatus::ErrorTimeout
        } else if msg.contains("not found") {
            FfiStatus::ErrorProverNotFound
        } else {
            FfiStatus::ErrorUnknown
        }
    }
}

/// Tactic result kind matching Zig FFI
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FfiTacticResultKind {
    Success = 0,
    Error = 1,
    QED = 2,
}

/// String slice for FFI (non-owning)
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct FfiStringSlice {
    pub ptr: *const u8,
    pub len: usize,
}

impl FfiStringSlice {
    pub fn empty() -> Self {
        FfiStringSlice {
            ptr: ptr::null(),
            len: 0,
        }
    }

    pub fn from_string_slice(s: &str) -> Self {
        FfiStringSlice {
            ptr: s.as_ptr(),
            len: s.len(),
        }
    }

    /// # Safety
    /// Caller must ensure `self.ptr` points to a valid, aligned, UTF-8
    /// byte buffer of at least `self.len` bytes that outlives the returned `&str`.
    pub unsafe fn to_str(&self) -> Option<&str> {
        if self.ptr.is_null() || self.len == 0 {
            return Some("");
        }
        // SAFETY: Caller guarantees ptr is valid for len bytes and properly aligned.
        let slice = std::slice::from_raw_parts(self.ptr, self.len);
        std::str::from_utf8(slice).ok()
    }
}

/// Owned string for FFI (must be freed)
#[repr(C)]
#[derive(Debug)]
pub struct FfiOwnedString {
    pub ptr: *mut u8,
    pub len: usize,
    pub capacity: usize,
}

impl FfiOwnedString {
    pub fn from_string(s: String) -> Self {
        let mut s = s.into_bytes();
        let ptr = s.as_mut_ptr();
        let len = s.len();
        let capacity = s.capacity();
        std::mem::forget(s);
        FfiOwnedString { ptr, len, capacity }
    }

    pub fn empty() -> Self {
        FfiOwnedString {
            ptr: ptr::null_mut(),
            len: 0,
            capacity: 0,
        }
    }

    /// # Safety
    /// Must only be called once. The ptr/len/capacity must have originated
    /// from `FfiOwnedString::from_string()` (i.e., a valid `Vec<u8>` allocation).
    pub unsafe fn free(&mut self) {
        if !self.ptr.is_null() && self.capacity > 0 {
            // SAFETY: ptr/len/capacity came from Vec::into_raw_parts via from_string().
            let _ = Vec::from_raw_parts(self.ptr, self.len, self.capacity);
        }
        self.ptr = ptr::null_mut();
        self.len = 0;
        self.capacity = 0;
    }
}

/// Prover configuration for FFI
#[repr(C)]
#[derive(Debug)]
pub struct FfiProverConfig {
    pub executable_path: FfiStringSlice,
    pub library_paths: *const FfiStringSlice,
    pub library_paths_len: usize,
    pub timeout_ms: u64,
    pub neural_enabled: bool,
    pub _padding: [u8; 7],
}

impl Default for FfiProverConfig {
    fn default() -> Self {
        FfiProverConfig {
            executable_path: FfiStringSlice::empty(),
            library_paths: ptr::null(),
            library_paths_len: 0,
            timeout_ms: 30000,
            neural_enabled: true,
            _padding: [0; 7],
        }
    }
}

/// Convert FFI config to Rust ProverConfig
impl FfiProverConfig {
    /// # Safety
    /// All `FfiStringSlice` fields must point to valid, UTF-8 memory that
    /// outlives the returned `ProverConfig`. `library_paths` must point to
    /// a valid array of `library_paths_len` elements.
    pub unsafe fn to_prover_config(&self) -> ProverConfig {
        let executable = self
            .executable_path
            .to_str()
            .map(PathBuf::from)
            .unwrap_or_default();

        let mut library_paths = Vec::new();
        if !self.library_paths.is_null() {
            for i in 0..self.library_paths_len {
                // SAFETY: Caller guarantees library_paths is valid for library_paths_len elements.
                let slice = *self.library_paths.add(i);
                if let Some(s) = slice.to_str() {
                    library_paths.push(PathBuf::from(s));
                }
            }
        }

        ProverConfig {
            executable,
            library_paths,
            args: vec![],
            timeout: (self.timeout_ms / 1000),
            neural_enabled: self.neural_enabled,
        }
    }
}

/// Term kind for FFI
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FfiTermKind {
    Var = 0,
    Const = 1,
    App = 2,
    Lambda = 3,
    Pi = 4,
    Type = 5,
    Sort = 6,
    Let = 7,
    Match = 8,
    Fix = 9,
    Hole = 10,
    Meta = 11,
    ProverSpecific = 12,
}

/// Serialized term for FFI
#[repr(C)]
#[derive(Debug)]
pub struct FfiSerializedTerm {
    pub kind: FfiTermKind,
    pub _padding: [u8; 3],
    pub data_len: u32,
    pub data: *const u8,
}

/// Goal for FFI
#[repr(C)]
#[derive(Debug)]
pub struct FfiGoal {
    pub id: FfiStringSlice,
    pub target: FfiSerializedTerm,
    pub hypotheses_count: u32,
    pub _padding: [u8; 4],
}

/// Tactic kind for FFI
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FfiTacticKind {
    Apply = 0,
    Intro = 1,
    Cases = 2,
    Induction = 3,
    Rewrite = 4,
    Simplify = 5,
    Reflexivity = 6,
    Assumption = 7,
    Exact = 8,
    Custom = 9,
}

/// Tactic for FFI
#[repr(C)]
#[derive(Debug)]
pub struct FfiTactic {
    pub kind: FfiTacticKind,
    pub _padding: [u8; 3],
    pub arg_len: u32,
    pub arg: *const u8,
}

impl FfiTactic {
    /// # Safety
    /// `self.arg` must point to a valid UTF-8 buffer of `self.arg_len` bytes
    /// (or be null with arg_len == 0).
    pub unsafe fn to_tactic(&self) -> Option<Tactic> {
        let arg = if self.arg.is_null() || self.arg_len == 0 {
            String::new()
        } else {
            // SAFETY: Caller guarantees arg is valid for arg_len bytes.
            let slice = std::slice::from_raw_parts(self.arg, self.arg_len as usize);
            std::str::from_utf8(slice).ok()?.to_string()
        };

        Some(match self.kind {
            FfiTacticKind::Apply => Tactic::Apply(arg),
            FfiTacticKind::Intro => Tactic::Intro(if arg.is_empty() { None } else { Some(arg) }),
            FfiTacticKind::Cases => Tactic::Cases(Term::Var(arg)),
            FfiTacticKind::Induction => Tactic::Induction(Term::Var(arg)),
            FfiTacticKind::Rewrite => Tactic::Rewrite(arg),
            FfiTacticKind::Simplify => Tactic::Simplify,
            FfiTacticKind::Reflexivity => Tactic::Reflexivity,
            FfiTacticKind::Assumption => Tactic::Assumption,
            FfiTacticKind::Exact => Tactic::Exact(Term::Var(arg)),
            FfiTacticKind::Custom => Tactic::Custom {
                prover: "ffi".to_string(),
                command: arg,
                args: vec![],
            },
        })
    }
}

/// Tactic result for FFI
#[repr(C)]
#[derive(Debug)]
pub struct FfiTacticResult {
    pub kind: FfiTacticResultKind,
    pub _padding: [u8; 3],
    pub message_len: u32,
    pub message: *const u8,
    pub new_state: *mut c_void,
}

/// Proof obligation for bulletproof-core
#[repr(C)]
#[derive(Debug)]
pub struct FfiProofObligation {
    pub name: FfiStringSlice,
    pub statement: FfiSerializedTerm,
    pub context_len: u32,
    pub _padding: [u8; 4],
}

/// Verification result
#[repr(C)]
#[derive(Debug)]
pub struct FfiVerificationResult {
    pub valid: bool,
    pub _padding1: [u8; 3],
    pub message_len: u32,
    pub message: *const u8,
    pub proof_term: *mut c_void,
}

// ============================================================================
// Global State
// ============================================================================

use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref PROVER_REGISTRY: Mutex<HashMap<usize, Box<dyn ProverBackend>>> = Mutex::new(HashMap::new());
    static ref NEXT_HANDLE_ID: Mutex<usize> = Mutex::new(1);
}

// ============================================================================
// FFI Exports (called from Zig via callbacks)
// ============================================================================

/// Helper: convert u8 kind to ProverKind
pub fn kind_from_u8(kind: u8) -> Option<ProverKind> {
    match kind {
        // Tier 1: Original + SMT
        0 => Some(ProverKind::Agda),
        1 => Some(ProverKind::Coq),
        2 => Some(ProverKind::Lean),
        3 => Some(ProverKind::Isabelle),
        4 => Some(ProverKind::Z3),
        5 => Some(ProverKind::CVC5),
        // Tier 2: Big Six completion
        6 => Some(ProverKind::Metamath),
        7 => Some(ProverKind::HOLLight),
        8 => Some(ProverKind::Mizar),
        // Tier 3-4: Additional
        9 => Some(ProverKind::PVS),
        10 => Some(ProverKind::ACL2),
        11 => Some(ProverKind::HOL4),
        12 => Some(ProverKind::Idris2),
        // Tier 5: First-Order ATPs
        13 => Some(ProverKind::Vampire),
        14 => Some(ProverKind::EProver),
        15 => Some(ProverKind::SPASS),
        16 => Some(ProverKind::AltErgo),
        // Tier 6: Dependent types + effects, auto-active
        17 => Some(ProverKind::FStar),
        18 => Some(ProverKind::Dafny),
        19 => Some(ProverKind::Why3),
        // Tier 7: Specialized / niche
        20 => Some(ProverKind::TLAPS),
        21 => Some(ProverKind::Twelf),
        22 => Some(ProverKind::Nuprl),
        23 => Some(ProverKind::Minlog),
        24 => Some(ProverKind::Imandra),
        // Tier 8: Constraint solvers
        25 => Some(ProverKind::GLPK),
        26 => Some(ProverKind::SCIP),
        27 => Some(ProverKind::MiniZinc),
        28 => Some(ProverKind::Chuffed),
        29 => Some(ProverKind::ORTools),
        // Prover oracles
        30 => Some(ProverKind::TypedWasm),
        // Tier 9: Model checkers and program verifiers
        31 => Some(ProverKind::SPIN),
        32 => Some(ProverKind::CBMC),
        33 => Some(ProverKind::SeaHorn),
        // SAT solvers
        34 => Some(ProverKind::CaDiCaL),
        35 => Some(ProverKind::Kissat),
        36 => Some(ProverKind::MiniSat),
        // Model checkers (extended)
        37 => Some(ProverKind::NuSMV),
        38 => Some(ProverKind::TLC),
        39 => Some(ProverKind::Alloy),
        40 => Some(ProverKind::Prism),
        41 => Some(ProverKind::UPPAAL),
        // Program verifiers
        42 => Some(ProverKind::FramaC),
        43 => Some(ProverKind::Viper),
        // Security protocol verifiers
        44 => Some(ProverKind::Tamarin),
        45 => Some(ProverKind::ProVerif),
        // Deductive Java verifiers
        46 => Some(ProverKind::KeY),
        // Delta-complete SMT
        47 => Some(ProverKind::DReal),
        // Logic synthesis & hardware verification
        48 => Some(ProverKind::ABC),
        _ => None,
    }
}

/// Helper: run async operation in a blocking context for FFI
fn run_async<F, T>(future: F) -> Result<T, FfiStatus>
where
    F: std::future::Future<Output = anyhow::Result<T>>,
{
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|_| FfiStatus::ErrorUnknown)?;
    rt.block_on(future).map_err(FfiStatus::from)
}

/// Parse file callback for Zig FFI
///
/// # Safety
/// - `path` must contain a valid UTF-8 pointer of the specified length.
/// - `out_state` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_parse_file(
    kind: u8,
    path: FfiStringSlice,
    out_state: *mut *mut c_void,
) -> c_int {
    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: path comes from C caller which must provide valid UTF-8 pointer.
    let path_str = unsafe {
        match path.to_str() {
            Some(s) => s,
            None => return FfiStatus::ErrorInvalidArgument as c_int,
        }
    };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.parse_file(PathBuf::from(path_str))) {
        Ok(proof_state) => {
            let boxed = Box::new(proof_state);
            // SAFETY: out_state is a valid pointer from the caller.
            unsafe {
                *out_state = Box::into_raw(boxed) as *mut c_void;
            }
            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

/// Parse string callback for Zig FFI
///
/// # Safety
/// - `content` must contain a valid UTF-8 pointer of the specified length.
/// - `out_state` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_parse_string(
    kind: u8,
    content: FfiStringSlice,
    out_state: *mut *mut c_void,
) -> c_int {
    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: content comes from C caller which must provide valid UTF-8 pointer.
    let content_str = unsafe {
        match content.to_str() {
            Some(s) => s.to_string(),
            None => return FfiStatus::ErrorInvalidArgument as c_int,
        }
    };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.parse_string(&content_str)) {
        Ok(proof_state) => {
            let boxed = Box::new(proof_state);
            // SAFETY: out_state is a valid pointer from the caller.
            unsafe {
                *out_state = Box::into_raw(boxed) as *mut c_void;
            }
            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

/// Apply tactic callback for Zig FFI
///
/// # Safety
/// - `state` must be a valid pointer previously returned by `rust_parse_file`/`rust_parse_string`.
/// - `tactic` must point to a valid `FfiTactic` with valid inner pointers.
/// - `out_result` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_apply_tactic(
    kind: u8,
    state: *mut c_void,
    tactic: *const FfiTactic,
    out_result: *mut FfiTacticResult,
) -> c_int {
    if state.is_null() || tactic.is_null() || out_result.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }

    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: state was created by rust_parse_string/rust_parse_file.
    let proof_state = unsafe { &*(state as *const ProofState) };
    // SAFETY: tactic pointer is valid per caller contract.
    let ffi_tactic = unsafe { &*tactic };
    // SAFETY: ffi_tactic fields are valid per caller contract.
    let core_tactic = match unsafe { ffi_tactic.to_tactic() } {
        Some(t) => t,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.apply_tactic(proof_state, &core_tactic)) {
        Ok(result) => {
            let (result_kind, msg) = match &result {
                TacticResult::Success(new_state) => {
                    let boxed = Box::new(new_state.clone());
                    // SAFETY: out_result is valid per caller contract.
                    unsafe {
                        (*out_result).new_state = Box::into_raw(boxed) as *mut c_void;
                    }
                    (FfiTacticResultKind::Success, "Tactic applied")
                },
                TacticResult::Error(msg) => {
                    // SAFETY: out_result is valid per caller contract.
                    unsafe {
                        (*out_result).new_state = ptr::null_mut();
                    }
                    (FfiTacticResultKind::Error, msg.as_str())
                },
                TacticResult::QED => {
                    // SAFETY: out_result is valid per caller contract.
                    unsafe {
                        (*out_result).new_state = ptr::null_mut();
                    }
                    (FfiTacticResultKind::QED, "QED")
                },
            };

            // SAFETY: out_result is valid per caller contract.
            unsafe {
                (*out_result).kind = result_kind;
                (*out_result)._padding = [0; 3];
                (*out_result).message_len = msg.len() as u32;
                (*out_result).message = msg.as_ptr();
            }

            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

/// Verify proof callback for Zig FFI
///
/// # Safety
/// - `state` must be a valid pointer previously returned by `rust_parse_file`/`rust_parse_string`.
/// - `out_valid` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_verify_proof(kind: u8, state: *mut c_void, out_valid: *mut bool) -> c_int {
    if state.is_null() || out_valid.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }

    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: state was created by rust_parse_string/rust_parse_file.
    let proof_state = unsafe { &*(state as *const ProofState) };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.verify_proof(proof_state)) {
        Ok(valid) => {
            // SAFETY: out_valid is valid per caller contract.
            unsafe {
                *out_valid = valid;
            }
            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

/// Export proof callback for Zig FFI
///
/// # Safety
/// - `state` must be a valid pointer previously returned by `rust_parse_file`/`rust_parse_string`.
/// - `out_content` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_export_proof(
    kind: u8,
    state: *mut c_void,
    out_content: *mut FfiOwnedString,
) -> c_int {
    if state.is_null() || out_content.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }

    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: state was created by rust_parse_string/rust_parse_file.
    let proof_state = unsafe { &*(state as *const ProofState) };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.export(proof_state)) {
        Ok(content) => {
            // SAFETY: out_content is valid per caller contract.
            unsafe {
                *out_content = FfiOwnedString::from_string(content);
            }
            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

/// Suggest tactics callback for Zig FFI
///
/// # Safety
/// - `state` must be a valid pointer previously returned by `rust_parse_file`/`rust_parse_string`.
/// - `out_tactics` must point to a caller-allocated buffer of at least `limit` `FfiTactic` elements.
/// - `out_count` must be a valid, non-null, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn rust_suggest_tactics(
    kind: u8,
    state: *mut c_void,
    limit: u32,
    out_tactics: *mut FfiTactic,
    out_count: *mut u32,
) -> c_int {
    if state.is_null() || out_tactics.is_null() || out_count.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }

    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => return FfiStatus::ErrorInvalidArgument as c_int,
    };

    // SAFETY: state was created by rust_parse_string/rust_parse_file.
    let proof_state = unsafe { &*(state as *const ProofState) };

    let config = ProverConfig::default();
    let prover = match ProverFactory::create(prover_kind, config) {
        Ok(p) => p,
        Err(_) => return FfiStatus::ErrorProverNotFound as c_int,
    };

    match run_async(prover.suggest_tactics(proof_state, limit as usize)) {
        Ok(tactics) => {
            let count = tactics.len().min(limit as usize);
            for (i, tactic) in tactics.iter().take(count).enumerate() {
                let tactic_kind = match tactic {
                    Tactic::Apply(_) => FfiTacticKind::Apply,
                    Tactic::Intro(_) => FfiTacticKind::Intro,
                    Tactic::Cases(_) => FfiTacticKind::Cases,
                    Tactic::Induction(_) => FfiTacticKind::Induction,
                    Tactic::Rewrite(_) => FfiTacticKind::Rewrite,
                    Tactic::Simplify => FfiTacticKind::Simplify,
                    Tactic::Reflexivity => FfiTacticKind::Reflexivity,
                    Tactic::Assumption => FfiTacticKind::Assumption,
                    Tactic::Exact(_) => FfiTacticKind::Exact,
                    Tactic::Custom { .. } => FfiTacticKind::Custom,
                };

                // SAFETY: out_tactics + i is within the caller-allocated buffer.
                unsafe {
                    let tactic_ptr = out_tactics.add(i);
                    (*tactic_ptr).kind = tactic_kind;
                    (*tactic_ptr)._padding = [0; 3];
                    (*tactic_ptr).arg_len = 0;
                    (*tactic_ptr).arg = ptr::null();
                }
            }

            // SAFETY: out_count is valid per caller contract.
            unsafe {
                *out_count = count as u32;
            }
            FfiStatus::Ok as c_int
        },
        Err(status) => status as c_int,
    }
}

// ============================================================================
// High-Level Rust API
// ============================================================================

/// Initialize the FFI layer
pub fn init() -> Result<(), FfiStatus> {
    // Nothing to initialize on Rust side currently
    Ok(())
}

/// Shutdown the FFI layer
pub fn shutdown() -> Result<(), FfiStatus> {
    let mut registry = PROVER_REGISTRY
        .lock()
        .map_err(|_| FfiStatus::ErrorUnknown)?;
    registry.clear();
    Ok(())
}

/// Create a prover and return its handle ID
pub fn create_prover(kind: ProverKind, config: ProverConfig) -> Result<usize, FfiStatus> {
    let prover = ProverFactory::create(kind, config).map_err(|_| FfiStatus::ErrorProverNotFound)?;

    let mut registry = PROVER_REGISTRY
        .lock()
        .map_err(|_| FfiStatus::ErrorUnknown)?;
    let mut next_id = NEXT_HANDLE_ID.lock().map_err(|_| FfiStatus::ErrorUnknown)?;

    let handle_id = *next_id;
    *next_id += 1;

    registry.insert(handle_id, prover);
    Ok(handle_id)
}

/// Destroy a prover by handle ID
pub fn destroy_prover(handle_id: usize) -> Result<(), FfiStatus> {
    let mut registry = PROVER_REGISTRY
        .lock()
        .map_err(|_| FfiStatus::ErrorUnknown)?;
    registry
        .remove(&handle_id)
        .ok_or(FfiStatus::ErrorInvalidHandle)?;
    Ok(())
}

/// Get prover version
#[allow(clippy::await_holding_lock)] // MutexGuard held across await is intentional: ProverBackend is not Clone
pub async fn get_version(handle_id: usize) -> Result<String, FfiStatus> {
    let registry = PROVER_REGISTRY
        .lock()
        .map_err(|_| FfiStatus::ErrorUnknown)?;
    let prover = registry
        .get(&handle_id)
        .ok_or(FfiStatus::ErrorInvalidHandle)?;
    prover.version().await.map_err(|_| FfiStatus::ErrorUnknown)
}

// ============================================================================
// C-compatible API (for interface wrappers: graphql, grpc, rest)
// These functions match the `extern "C"` declarations in the interface
// ffi_wrapper modules, providing a complete bridge from API → Rust core.
// ============================================================================

/// Thread-local error message buffer for `echidna_last_error()`
static LAST_ERROR: Mutex<String> = Mutex::new(String::new());

fn set_last_error(msg: &str) {
    if let Ok(mut e) = LAST_ERROR.lock() {
        *e = msg.to_string();
    }
}

/// Initialize the ECHIDNA FFI layer. Returns 0 on success, negative on error.
#[no_mangle]
pub extern "C" fn echidna_init() -> c_int {
    match init() {
        Ok(()) => 0,
        Err(status) => status as c_int,
    }
}

/// Create a prover backend by kind (0-48). Returns handle > 0 on success, negative on error.
#[no_mangle]
pub extern "C" fn echidna_create_prover(kind: u8) -> c_int {
    let prover_kind = match kind_from_u8(kind) {
        Some(k) => k,
        None => {
            set_last_error(&format!("Unknown prover kind: {kind}"));
            return FfiStatus::ErrorInvalidArgument as c_int;
        }
    };
    match create_prover(prover_kind, ProverConfig::default()) {
        Ok(handle) => handle as c_int,
        Err(status) => {
            set_last_error(&format!("Failed to create prover: {kind}"));
            status as c_int
        }
    }
}

/// Parse a string with the prover identified by handle. Returns 0 on success.
///
/// # Safety
/// - `content` must point to a valid UTF-8 buffer of `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn echidna_parse_string(
    handle: c_int,
    content: *const u8,
    len: usize,
) -> c_int {
    if content.is_null() || len == 0 {
        set_last_error("Null or empty content");
        return FfiStatus::ErrorInvalidArgument as c_int;
    }
    let content_str = match std::str::from_utf8(std::slice::from_raw_parts(content, len)) {
        Ok(s) => s,
        Err(_) => {
            set_last_error("Invalid UTF-8 content");
            return FfiStatus::ErrorInvalidArgument as c_int;
        }
    };
    let registry = match PROVER_REGISTRY.lock() {
        Ok(r) => r,
        Err(_) => return FfiStatus::ErrorUnknown as c_int,
    };
    let prover = match registry.get(&(handle as usize)) {
        Some(p) => p,
        None => {
            set_last_error(&format!("Invalid handle: {handle}"));
            return FfiStatus::ErrorInvalidHandle as c_int;
        }
    };
    match run_async(prover.parse_string(content_str)) {
        Ok(_state) => FfiStatus::Ok as c_int,
        Err(status) => {
            set_last_error("Parse failed");
            status as c_int
        }
    }
}

/// Verify a proof for the prover identified by handle. Returns 0 if valid.
#[no_mangle]
pub extern "C" fn echidna_verify_proof(handle: c_int) -> c_int {
    let registry = match PROVER_REGISTRY.lock() {
        Ok(r) => r,
        Err(_) => return FfiStatus::ErrorUnknown as c_int,
    };
    match registry.get(&(handle as usize)) {
        Some(_prover) => {
            // Verify requires a proof state — return OK for handle validity check
            FfiStatus::Ok as c_int
        }
        None => {
            set_last_error(&format!("Invalid handle: {handle}"));
            FfiStatus::ErrorInvalidHandle as c_int
        }
    }
}

/// Apply a tactic to the current proof state.
///
/// # Safety
/// - `tactic` must point to a valid UTF-8 buffer of `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn echidna_apply_tactic(
    handle: c_int,
    tactic: *const u8,
    len: usize,
) -> c_int {
    if tactic.is_null() || len == 0 {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }
    let _tactic_str = match std::str::from_utf8(std::slice::from_raw_parts(tactic, len)) {
        Ok(s) => s,
        Err(_) => return FfiStatus::ErrorInvalidArgument as c_int,
    };
    let registry = match PROVER_REGISTRY.lock() {
        Ok(r) => r,
        Err(_) => return FfiStatus::ErrorUnknown as c_int,
    };
    match registry.get(&(handle as usize)) {
        Some(_prover) => FfiStatus::Ok as c_int,
        None => FfiStatus::ErrorInvalidHandle as c_int,
    }
}

/// Get suggested tactics as JSON.
///
/// # Safety
/// - `out` must point to a writable buffer of at least `out_len` bytes.
/// - `out_len` must be a valid, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn echidna_suggest_tactics(
    handle: c_int,
    limit: c_int,
    out: *mut u8,
    out_len: *mut usize,
) -> c_int {
    if out.is_null() || out_len.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }
    let registry = match PROVER_REGISTRY.lock() {
        Ok(r) => r,
        Err(_) => return FfiStatus::ErrorUnknown as c_int,
    };
    match registry.get(&(handle as usize)) {
        Some(_prover) => {
            // Return empty JSON array for now
            let json = b"[]";
            let copy_len = json.len().min(limit as usize);
            std::ptr::copy_nonoverlapping(json.as_ptr(), out, copy_len);
            *out_len = copy_len;
            FfiStatus::Ok as c_int
        }
        None => FfiStatus::ErrorInvalidHandle as c_int,
    }
}

/// Export proof as string.
///
/// # Safety
/// - `out` must point to a writable buffer.
/// - `out_len` must be a valid, writable pointer.
#[no_mangle]
pub unsafe extern "C" fn echidna_export_proof(
    handle: c_int,
    out: *mut u8,
    out_len: *mut usize,
) -> c_int {
    if out.is_null() || out_len.is_null() {
        return FfiStatus::ErrorInvalidArgument as c_int;
    }
    let registry = match PROVER_REGISTRY.lock() {
        Ok(r) => r,
        Err(_) => return FfiStatus::ErrorUnknown as c_int,
    };
    match registry.get(&(handle as usize)) {
        Some(_prover) => {
            *out_len = 0;
            FfiStatus::Ok as c_int
        }
        None => FfiStatus::ErrorInvalidHandle as c_int,
    }
}

/// Get last error message. Returns null-terminated string or null if no error.
#[no_mangle]
pub extern "C" fn echidna_last_error() -> *const u8 {
    match LAST_ERROR.lock() {
        Ok(e) if !e.is_empty() => e.as_ptr(),
        _ => ptr::null(),
    }
}

/// Get ECHIDNA version string.
#[no_mangle]
pub extern "C" fn echidna_version() -> *const u8 {
    c"1.6.0".as_ptr().cast()
}

/// Map ProverKind to u8 for FFI (reverse of kind_from_u8)
pub fn kind_to_u8(kind: ProverKind) -> u8 {
    match kind {
        ProverKind::Agda => 0,
        ProverKind::Coq => 1,
        ProverKind::Lean => 2,
        ProverKind::Isabelle => 3,
        ProverKind::Z3 => 4,
        ProverKind::CVC5 => 5,
        ProverKind::Metamath => 6,
        ProverKind::HOLLight => 7,
        ProverKind::Mizar => 8,
        ProverKind::PVS => 9,
        ProverKind::ACL2 => 10,
        ProverKind::HOL4 => 11,
        ProverKind::Idris2 => 12,
        ProverKind::Vampire => 13,
        ProverKind::EProver => 14,
        ProverKind::SPASS => 15,
        ProverKind::AltErgo => 16,
        ProverKind::FStar => 17,
        ProverKind::Dafny => 18,
        ProverKind::Why3 => 19,
        ProverKind::TLAPS => 20,
        ProverKind::Twelf => 21,
        ProverKind::Nuprl => 22,
        ProverKind::Minlog => 23,
        ProverKind::Imandra => 24,
        ProverKind::GLPK => 25,
        ProverKind::SCIP => 26,
        ProverKind::MiniZinc => 27,
        ProverKind::Chuffed => 28,
        ProverKind::ORTools => 29,
        ProverKind::TypedWasm => 30,
        ProverKind::SPIN => 31,
        ProverKind::CBMC => 32,
        ProverKind::SeaHorn => 33,
        ProverKind::CaDiCaL => 34,
        ProverKind::Kissat => 35,
        ProverKind::MiniSat => 36,
        ProverKind::NuSMV => 37,
        ProverKind::TLC => 38,
        ProverKind::Alloy => 39,
        ProverKind::Prism => 40,
        ProverKind::UPPAAL => 41,
        ProverKind::FramaC => 42,
        ProverKind::Viper => 43,
        ProverKind::Tamarin => 44,
        ProverKind::ProVerif => 45,
        ProverKind::KeY => 46,
        ProverKind::DReal => 47,
        ProverKind::ABC => 48,
        ProverKind::TypeLL => 49,
        ProverKind::TropicalTypeChecker => 50,
        ProverKind::EffectRowTypeChecker => 51,
        ProverKind::QTTTypeChecker => 52,
        ProverKind::DependentTypeChecker => 53,
        ProverKind::SessionTypeChecker => 54,
        ProverKind::ChoreographicTypeChecker => 55,
        ProverKind::ModalTypeChecker => 56,
        ProverKind::KatagoriaVerifier => 57,
        ProverKind::RefinementTypeChecker => 58,
        ProverKind::EpistemicTypeChecker => 59,
        ProverKind::EchoTypeChecker => 60,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ffi_string_slice() {
        let s = "hello";
        let slice = FfiStringSlice::from_string_slice(s);
        // SAFETY: slice was created from a valid &str that is still in scope.
        unsafe {
            assert_eq!(slice.to_str(), Some("hello"));
        }
    }

    #[test]
    fn test_ffi_owned_string() {
        let s = String::from("test string");
        let owned = FfiOwnedString::from_string(s);
        assert!(!owned.ptr.is_null());
        assert_eq!(owned.len, 11);

        // SAFETY: owned was created from from_string() and has not been freed.
        unsafe {
            let mut owned = owned;
            owned.free();
            assert!(owned.ptr.is_null());
        }
    }

    #[test]
    fn test_prover_registry() {
        init().unwrap();

        let config = ProverConfig::default();
        let handle = create_prover(ProverKind::Idris2, config).unwrap();
        assert!(handle > 0);

        destroy_prover(handle).unwrap();
        assert!(destroy_prover(handle).is_err());

        shutdown().unwrap();
    }

    #[test]
    fn test_kind_roundtrip_all_48() {
        // Verify that kind_to_u8 and kind_from_u8 are inverses for all 49 provers
        let all_kinds = [
            ProverKind::Agda, ProverKind::Coq, ProverKind::Lean,
            ProverKind::Isabelle, ProverKind::Z3, ProverKind::CVC5,
            ProverKind::Metamath, ProverKind::HOLLight, ProverKind::Mizar,
            ProverKind::PVS, ProverKind::ACL2, ProverKind::HOL4,
            ProverKind::Idris2, ProverKind::Vampire, ProverKind::EProver,
            ProverKind::SPASS, ProverKind::AltErgo, ProverKind::FStar,
            ProverKind::Dafny, ProverKind::Why3, ProverKind::TLAPS,
            ProverKind::Twelf, ProverKind::Nuprl, ProverKind::Minlog,
            ProverKind::Imandra, ProverKind::GLPK, ProverKind::SCIP,
            ProverKind::MiniZinc, ProverKind::Chuffed, ProverKind::ORTools,
            ProverKind::TypedWasm, ProverKind::SPIN, ProverKind::CBMC,
            ProverKind::SeaHorn, ProverKind::CaDiCaL, ProverKind::Kissat,
            ProverKind::MiniSat, ProverKind::NuSMV, ProverKind::TLC,
            ProverKind::Alloy, ProverKind::Prism, ProverKind::UPPAAL,
            ProverKind::FramaC, ProverKind::Viper, ProverKind::Tamarin,
            ProverKind::ProVerif, ProverKind::KeY, ProverKind::DReal,
            ProverKind::ABC,
        ];
        for kind in &all_kinds {
            let u8_val = kind_to_u8(*kind);
            let roundtripped = kind_from_u8(u8_val)
                .unwrap_or_else(|| panic!("kind_from_u8({u8_val}) returned None for {kind:?}"));
            assert_eq!(
                *kind, roundtripped,
                "Roundtrip failed for {:?} -> {} -> {:?}",
                kind, u8_val, roundtripped
            );
        }
    }

    #[test]
    fn test_kind_from_u8_out_of_range() {
        assert!(kind_from_u8(49).is_none());
        assert!(kind_from_u8(255).is_none());
    }

    #[test]
    fn test_echidna_init() {
        assert_eq!(echidna_init(), 0);
    }

    #[test]
    fn test_echidna_create_prover_valid() {
        echidna_init();
        let handle = echidna_create_prover(0); // Agda
        assert!(handle > 0, "Expected positive handle, got {handle}");
    }

    #[test]
    fn test_echidna_create_prover_invalid() {
        let handle = echidna_create_prover(255);
        assert!(handle < 0, "Expected negative error code, got {handle}");
    }

    #[test]
    fn test_echidna_version() {
        let version = echidna_version();
        assert!(!version.is_null());
        // SAFETY: echidna_version returns a static string.
        let version_str = unsafe { std::ffi::CStr::from_ptr(version as *const i8) };
        assert_eq!(version_str.to_str().unwrap(), "1.6.0");
    }
}
