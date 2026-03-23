// SPDX-License-Identifier: PMPL-1.0-or-later
//! Build script for ECHIDNA
//!
//! When the `chapel` feature is enabled, this links against the Zig-built
//! Chapel FFI bridge library (libechidna_chapel_ffi).
//!
//! Build order: Chapel (.chpl) → C headers → Zig (chapel_bridge.zig) → Rust (proof_search.rs)

fn main() {
    // Only link Chapel FFI when the feature is enabled
    #[cfg(feature = "chapel")]
    {
        // Look for the Zig-built library in src/zig_ffi/zig-out/lib/
        let zig_ffi_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("zig_ffi")
            .join("zig-out")
            .join("lib");

        if zig_ffi_dir.exists() {
            println!("cargo:rustc-link-search=native={}", zig_ffi_dir.display());
            println!("cargo:rustc-link-lib=static=echidna_chapel_ffi");
            println!("cargo:rustc-link-lib=dylib=c");
        } else {
            // Also check standard install location
            let alt_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lib");
            if alt_dir.exists() {
                println!("cargo:rustc-link-search=native={}", alt_dir.display());
                println!("cargo:rustc-link-lib=static=echidna_chapel_ffi");
                println!("cargo:rustc-link-lib=dylib=c");
            } else {
                println!("cargo:warning=Chapel FFI library not found. Build it first with: just build-chapel-ffi");
                println!("cargo:warning=Looked in: {}", zig_ffi_dir.display());
            }
        }

        // Re-run if FFI source changes
        println!("cargo:rerun-if-changed=src/zig_ffi/chapel_bridge.zig");
        println!("cargo:rerun-if-changed=src/zig_ffi/build.zig");
    }
}
