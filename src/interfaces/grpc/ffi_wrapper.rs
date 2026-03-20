// SPDX-License-Identifier: PMPL-1.0-or-later
// gRPC FFI Wrapper - Connects gRPC interface to ECHIDNA Rust core via Zig FFI

use std::ffi::{CString, CStr};
use std::os::raw::{c_int, c_void};
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
                CStr::from_ptr(err_ptr).to_string_lossy().into_owned()
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
        let version = CStr::from_ptr(ptr).to_string_lossy().into_owned();
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
        let error = CStr::from_ptr(ptr).to_string_lossy().into_owned();
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
        let rc = echidna_parse_string(handle, c_content.as_ptr(), content.len());
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
        let rc = echidna_apply_tactic(handle, c_tactic.as_ptr(), tactic.len());
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

/// Convert gRPC ProverKind to FFI ordinal
pub fn proto_kind_to_ffi(kind: i32) -> Result<u8> {
    match kind {
        1 => Ok(0), // Agda
        2 => Ok(1), // Coq
        3 => Ok(2), // Lean
        4 => Ok(3), // Isabelle
        5 => Ok(4), // Z3
        6 => Ok(5), // CVC5
        7 => Ok(6), // Metamath
        8 => Ok(7), // HOLLight
        9 => Ok(8), // Mizar
        10 => Ok(9), // PVS
        11 => Ok(10), // ACL2
        12 => Ok(11), // HOL4
        13 => Ok(12), // Idris2
        14 => Ok(13), // Vampire
        15 => Ok(14), // EProver
        16 => Ok(15), // SPASS
        17 => Ok(16), // AltErgo
        18 => Ok(17), // FStar
        19 => Ok(18), // Dafny
        20 => Ok(19), // Why3
        21 => Ok(20), // TLAPS
        22 => Ok(21), // Twelf
        23 => Ok(22), // Nuprl
        24 => Ok(23), // Minlog
        25 => Ok(24), // Imandra
        26 => Ok(25), // GLPK
        27 => Ok(26), // SCIP
        28 => Ok(27), // MiniZinc
        29 => Ok(28), // Chuffed
        30 => Ok(29), // ORTools
        _ => Err(anyhow!("Unknown prover kind: {}", kind)),
    }
}

/// Convert FFI ordinal to gRPC ProverKind
pub fn ffi_to_proto_kind(ordinal: u8) -> i32 {
    match ordinal {
        0 => 1, // Agda
        1 => 2, // Coq
        2 => 3, // Lean
        3 => 4, // Isabelle
        4 => 5, // Z3
        5 => 6, // CVC5
        6 => 7, // Metamath
        7 => 8, // HOLLight
        8 => 9, // Mizar
        9 => 10, // PVS
        10 => 11, // ACL2
        11 => 12, // HOL4
        12 => 13, // Idris2
        13 => 14, // Vampire
        14 => 15, // EProver
        15 => 16, // SPASS
        16 => 17, // AltErgo
        17 => 18, // FStar
        18 => 19, // Dafny
        19 => 20, // Why3
        20 => 21, // TLAPS
        21 => 22, // Twelf
        22 => 23, // Nuprl
        23 => 24, // Minlog
        24 => 25, // Imandra
        25 => 26, // GLPK
        26 => 27, // SCIP
        27 => 28, // MiniZinc
        28 => 29, // Chuffed
        29 => 30, // ORTools
        _ => 0, // Unknown
    }
}
