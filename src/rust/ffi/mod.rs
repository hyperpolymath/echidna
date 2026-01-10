// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! FFI bindings for ECHIDNA
//!
//! This module provides Rust bindings to the Zig FFI layer,
//! enabling external systems like bulletproof-core to use
//! ECHIDNA's theorem proving capabilities.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
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

    pub fn from_str(s: &str) -> Self {
        FfiStringSlice {
            ptr: s.as_ptr(),
            len: s.len(),
        }
    }

    pub unsafe fn to_str(&self) -> Option<&str> {
        if self.ptr.is_null() || self.len == 0 {
            return Some("");
        }
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

    pub unsafe fn free(&mut self) {
        if !self.ptr.is_null() && self.capacity > 0 {
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
    pub unsafe fn to_prover_config(&self) -> ProverConfig {
        let executable = self
            .executable_path
            .to_str()
            .map(PathBuf::from)
            .unwrap_or_default();

        let mut library_paths = Vec::new();
        if !self.library_paths.is_null() {
            for i in 0..self.library_paths_len {
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
            timeout: (self.timeout_ms / 1000) as u64,
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
    pub unsafe fn to_tactic(&self) -> Option<Tactic> {
        let arg = if self.arg.is_null() || self.arg_len == 0 {
            String::new()
        } else {
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
// FFI Exports (called from Zig)
// ============================================================================

/// Parse file callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_parse_file(
    kind: u8,
    path: FfiStringSlice,
    out_state: *mut *mut c_void,
) -> c_int {
    let prover_kind = match kind {
        0 => ProverKind::Agda,
        1 => ProverKind::Coq,
        2 => ProverKind::Lean,
        3 => ProverKind::Isabelle,
        4 => ProverKind::Z3,
        5 => ProverKind::CVC5,
        6 => ProverKind::Metamath,
        7 => ProverKind::HOLLight,
        8 => ProverKind::Mizar,
        9 => ProverKind::PVS,
        10 => ProverKind::ACL2,
        11 => ProverKind::HOL4,
        12 => ProverKind::Idris2,
        _ => return FfiStatus::ErrorInvalidArgument as c_int,
    };

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

    // Would need async runtime here
    // For now, return not implemented
    FfiStatus::ErrorNotImplemented as c_int
}

/// Parse string callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_parse_string(
    kind: u8,
    content: FfiStringSlice,
    out_state: *mut *mut c_void,
) -> c_int {
    FfiStatus::ErrorNotImplemented as c_int
}

/// Apply tactic callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_apply_tactic(
    kind: u8,
    state: *mut c_void,
    tactic: *const FfiTactic,
    out_result: *mut FfiTacticResult,
) -> c_int {
    FfiStatus::ErrorNotImplemented as c_int
}

/// Verify proof callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_verify_proof(
    kind: u8,
    state: *mut c_void,
    out_valid: *mut bool,
) -> c_int {
    FfiStatus::ErrorNotImplemented as c_int
}

/// Export proof callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_export_proof(
    kind: u8,
    state: *mut c_void,
    out_content: *mut FfiOwnedString,
) -> c_int {
    FfiStatus::ErrorNotImplemented as c_int
}

/// Suggest tactics callback for Zig FFI
#[no_mangle]
pub extern "C" fn rust_suggest_tactics(
    kind: u8,
    state: *mut c_void,
    limit: u32,
    out_tactics: *mut FfiTactic,
    out_count: *mut u32,
) -> c_int {
    FfiStatus::ErrorNotImplemented as c_int
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
    let mut registry = PROVER_REGISTRY.lock().map_err(|_| FfiStatus::ErrorUnknown)?;
    registry.clear();
    Ok(())
}

/// Create a prover and return its handle ID
pub fn create_prover(kind: ProverKind, config: ProverConfig) -> Result<usize, FfiStatus> {
    let prover = ProverFactory::create(kind, config).map_err(|_| FfiStatus::ErrorProverNotFound)?;

    let mut registry = PROVER_REGISTRY.lock().map_err(|_| FfiStatus::ErrorUnknown)?;
    let mut next_id = NEXT_HANDLE_ID.lock().map_err(|_| FfiStatus::ErrorUnknown)?;

    let handle_id = *next_id;
    *next_id += 1;

    registry.insert(handle_id, prover);
    Ok(handle_id)
}

/// Destroy a prover by handle ID
pub fn destroy_prover(handle_id: usize) -> Result<(), FfiStatus> {
    let mut registry = PROVER_REGISTRY.lock().map_err(|_| FfiStatus::ErrorUnknown)?;
    registry
        .remove(&handle_id)
        .ok_or(FfiStatus::ErrorInvalidHandle)?;
    Ok(())
}

/// Get prover version
pub async fn get_version(handle_id: usize) -> Result<String, FfiStatus> {
    let registry = PROVER_REGISTRY.lock().map_err(|_| FfiStatus::ErrorUnknown)?;
    let prover = registry
        .get(&handle_id)
        .ok_or(FfiStatus::ErrorInvalidHandle)?;
    prover
        .version()
        .await
        .map_err(|_| FfiStatus::ErrorUnknown)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ffi_string_slice() {
        let s = "hello";
        let slice = FfiStringSlice::from_str(s);
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
}
