// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL FFI Wrapper - Connects GraphQL interface to ECHIDNA Rust core via Zig FFI

use std::ffi::{CString, CStr};
use std::os::raw::{c_char, c_int};
use anyhow::{Result, anyhow};

// Re-export FFI types from core
pub use echidna::ffi::{FfiStatus, FfiStringSlice, FfiOwnedString, FfiProverConfig};

// External Zig FFI functions (from libechidna_ffi.so)
extern "C" {
    pub fn echidna_init() -> c_int;
    pub fn echidna_deinit();
    pub fn echidna_create_prover(kind: u8) -> c_int;
    pub fn echidna_destroy_prover(handle: c_int);
    pub fn echidna_parse_string(handle: c_int, content: *const u8, len: usize) -> c_int;
    pub fn echidna_verify_proof(handle: c_int) -> c_int;
    pub fn echidna_apply_tactic(handle: c_int, tactic: *const u8, len: usize) -> c_int;
    pub fn echidna_suggest_tactics(handle: c_int, limit: c_int, out: *mut u8, out_len: *mut usize) -> c_int;
    pub fn echidna_export_proof(handle: c_int, out: *mut u8, out_len: *mut usize) -> c_int;
    pub fn echidna_last_error() -> *const u8;
    pub fn echidna_version() -> *const u8;
}

/// Initialize the FFI layer
pub fn init_ffi() -> Result<()> {
    unsafe {
        let rc = echidna_init();
        if rc != 0 {
            let err_ptr = echidna_last_error();
            let err_msg = if err_ptr.is_null() {
                "Unknown FFI initialization error".to_string()
            } else {
                CStr::from_ptr(err_ptr as *const c_char).to_string_lossy().into_owned()
            };
            return Err(anyhow!("FFI initialization failed: {}", err_msg));
        }
    }
    Ok(())
}

/// Get FFI version
pub fn get_version() -> Result<String> {
    unsafe {
        let ptr = echidna_version();
        if ptr.is_null() {
            return Err(anyhow!("FFI version pointer is null"));
        }
        let version = CStr::from_ptr(ptr as *const c_char).to_string_lossy().into_owned();
        Ok(version)
    }
}

/// Get last FFI error
pub fn get_last_error() -> Result<String> {
    unsafe {
        let ptr = echidna_last_error();
        if ptr.is_null() {
            return Err(anyhow!("No error message available"));
        }
        let error = CStr::from_ptr(ptr as *const c_char).to_string_lossy().into_owned();
        Ok(error)
    }
}

/// Create a prover instance via FFI
pub fn create_prover(prover_kind: u8) -> Result<i32> {
    unsafe {
        let handle = echidna_create_prover(prover_kind);
        if handle < 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Failed to create prover: {}", error));
        }
        Ok(handle)
    }
}

/// Destroy a prover instance
pub fn destroy_prover(handle: i32) -> Result<()> {
    unsafe {
        echidna_destroy_prover(handle);
    }
    Ok(())
}

/// Parse proof content via FFI
pub fn parse_string(handle: i32, content: &str) -> Result<()> {
    unsafe {
        let c_content = CString::new(content)?;
        let rc = echidna_parse_string(handle, c_content.as_ptr() as *const u8, content.len());
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Parse failed: {}", error));
        }
    }
    Ok(())
}

/// Verify proof via FFI
pub fn verify_proof(handle: i32) -> Result<bool> {
    unsafe {
        let rc = echidna_verify_proof(handle);
        Ok(rc == 1)
    }
}

/// Apply tactic via FFI
pub fn apply_tactic(handle: i32, tactic: &str) -> Result<bool> {
    unsafe {
        let c_tactic = CString::new(tactic)?;
        let rc = echidna_apply_tactic(handle, c_tactic.as_ptr() as *const u8, tactic.len());
        Ok(rc == 0)
    }
}

/// Suggest tactics via FFI
pub fn suggest_tactics(handle: i32, limit: usize) -> Result<Vec<String>> {
    unsafe {
        let mut buffer = vec![0u8; 4096];
        let mut buffer_len = buffer.len();
        
        let rc = echidna_suggest_tactics(
            handle,
            limit as c_int,
            buffer.as_mut_ptr(),
            &mut buffer_len as *mut usize
        );
        
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Suggest tactics failed: {}", error));
        }
        
        if buffer_len == 0 {
            return Ok(vec![]);
        }
        
        buffer.truncate(buffer_len);
        let result = String::from_utf8(buffer)?;
        
        // Parse JSON array of tactics
        let tactics: Vec<String> = serde_json::from_str(&result)?;
        Ok(tactics)
    }
}

/// Export proof via FFI
pub fn export_proof(handle: i32) -> Result<String> {
    unsafe {
        let mut buffer = vec![0u8; 8192];
        let mut buffer_len = buffer.len();
        
        let rc = echidna_export_proof(
            handle,
            buffer.as_mut_ptr(),
            &mut buffer_len as *mut usize
        );
        
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Export failed: {}", error));
        }
        
        if buffer_len == 0 {
            return Ok(String::new());
        }
        
        buffer.truncate(buffer_len);
        let result = String::from_utf8(buffer)?;
        Ok(result)
    }
}

/// Convert GraphQL ProverKind to FFI ordinal
pub fn prover_kind_to_ffi(kind: &crate::schema::ProverKind) -> u8 {
    match kind {
        crate::schema::ProverKind::Agda => 0,
        crate::schema::ProverKind::Coq => 1,
        crate::schema::ProverKind::Lean => 2,
        crate::schema::ProverKind::Isabelle => 3,
        crate::schema::ProverKind::Z3 => 4,
        crate::schema::ProverKind::CVC5 => 5,
        crate::schema::ProverKind::Metamath => 6,
        crate::schema::ProverKind::HOLLight => 7,
        crate::schema::ProverKind::Mizar => 8,
        crate::schema::ProverKind::PVS => 9,
        crate::schema::ProverKind::ACL2 => 10,
        crate::schema::ProverKind::HOL4 => 11,
        crate::schema::ProverKind::Idris2 => 12,
        crate::schema::ProverKind::Vampire => 13,
        crate::schema::ProverKind::EProver => 14,
        crate::schema::ProverKind::SPASS => 15,
        crate::schema::ProverKind::AltErgo => 16,
        crate::schema::ProverKind::FStar => 17,
        crate::schema::ProverKind::Dafny => 18,
        crate::schema::ProverKind::Why3 => 19,
        crate::schema::ProverKind::TLAPS => 20,
        crate::schema::ProverKind::Twelf => 21,
        crate::schema::ProverKind::Nuprl => 22,
        crate::schema::ProverKind::Minlog => 23,
        crate::schema::ProverKind::Imandra => 24,
        crate::schema::ProverKind::GLPK => 25,
        crate::schema::ProverKind::SCIP => 26,
        crate::schema::ProverKind::MiniZinc => 27,
        crate::schema::ProverKind::Chuffed => 28,
        crate::schema::ProverKind::ORTools => 29,
    }
}

/// Convert FFI ordinal to GraphQL ProverKind
pub fn ffi_to_prover_kind(ordinal: u8) -> Option<crate::schema::ProverKind> {
    match ordinal {
        0 => Some(crate::schema::ProverKind::Agda),
        1 => Some(crate::schema::ProverKind::Coq),
        2 => Some(crate::schema::ProverKind::Lean),
        3 => Some(crate::schema::ProverKind::Isabelle),
        4 => Some(crate::schema::ProverKind::Z3),
        5 => Some(crate::schema::ProverKind::CVC5),
        6 => Some(crate::schema::ProverKind::Metamath),
        7 => Some(crate::schema::ProverKind::HOLLight),
        8 => Some(crate::schema::ProverKind::Mizar),
        9 => Some(crate::schema::ProverKind::PVS),
        10 => Some(crate::schema::ProverKind::ACL2),
        11 => Some(crate::schema::ProverKind::HOL4),
        12 => Some(crate::schema::ProverKind::Idris2),
        13 => Some(crate::schema::ProverKind::Vampire),
        14 => Some(crate::schema::ProverKind::EProver),
        15 => Some(crate::schema::ProverKind::SPASS),
        16 => Some(crate::schema::ProverKind::AltErgo),
        17 => Some(crate::schema::ProverKind::FStar),
        18 => Some(crate::schema::ProverKind::Dafny),
        19 => Some(crate::schema::ProverKind::Why3),
        20 => Some(crate::schema::ProverKind::TLAPS),
        21 => Some(crate::schema::ProverKind::Twelf),
        22 => Some(crate::schema::ProverKind::Nuprl),
        23 => Some(crate::schema::ProverKind::Minlog),
        24 => Some(crate::schema::ProverKind::Imandra),
        25 => Some(crate::schema::ProverKind::GLPK),
        26 => Some(crate::schema::ProverKind::SCIP),
        27 => Some(crate::schema::ProverKind::MiniZinc),
        28 => Some(crate::schema::ProverKind::Chuffed),
        29 => Some(crate::schema::ProverKind::ORTools),
        _ => None,
    }
}
