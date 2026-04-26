// SPDX-License-Identifier: PMPL-1.0-or-later
//! Build script for ECHIDNA
//!
//! Chapel:  Chapel (.chpl) → Zig bridge → Rust
//! SPARK:   Ada/SPARK (echidna_spark.gpr) → Zig bridge → Rust
//!
//! SPARK build order:
//!   1. gprbuild -P src/ada/spark/echidna_spark.gpr
//!   2. cd src/zig && zig build -Dspark
//!   3. cargo build --features spark

fn main() {
    // SPARK axiom-policy bridge (requires GPRbuild + Zig; see just spark-all)
    #[cfg(feature = "spark")]
    {
        let spark_zig_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("zig")
            .join("zig-out")
            .join("lib");

        let spark_ada_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("lib")
            .join("spark");

        if spark_zig_dir.exists() {
            println!("cargo:rustc-link-search=native={}", spark_zig_dir.display());
            println!("cargo:rustc-link-lib=static=echidna_spark_zig");
        } else {
            println!(
                "cargo:warning=SPARK Zig bridge not found. \
                 Build with: cd src/zig && zig build -Dspark"
            );
        }

        if spark_ada_dir.exists() {
            println!("cargo:rustc-link-search=native={}", spark_ada_dir.display());
            println!("cargo:rustc-link-lib=static=echidna_spark");
            println!("cargo:rustc-link-lib=dylib=gnat");
        } else {
            println!(
                "cargo:warning=SPARK Ada library not found. \
                 Build with: gprbuild -P src/ada/spark/echidna_spark.gpr"
            );
        }

        println!("cargo:rustc-link-lib=dylib=c");
        println!("cargo:rerun-if-changed=src/ada/spark/axiom_policy.adb");
        println!("cargo:rerun-if-changed=src/ada/spark/axiom_policy.ads");
        println!("cargo:rerun-if-changed=src/zig/ffi/axiom_spark_bridge.zig");
    }

    // FLINT CAS coprocessor (in-process, the only CAS we link rather than exec)
    #[cfg(feature = "flint")]
    {
        // Try pkg-config first; fall back to a bare -lflint on the standard
        // library path.  FLINT is LGPL-3 and compatible with the PMPL/MPL-2.0
        // fallback licence under which ECHIDNA is distributed.
        let found_via_pkg_config = std::process::Command::new("pkg-config")
            .args(["--exists", "flint"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);

        if found_via_pkg_config {
            // Let pkg-config emit the full set of link flags.
            if let Ok(output) = std::process::Command::new("pkg-config")
                .args(["--libs", "flint"])
                .output()
            {
                let flags = String::from_utf8_lossy(&output.stdout);
                for flag in flags.split_whitespace() {
                    if let Some(path) = flag.strip_prefix("-L") {
                        println!("cargo:rustc-link-search=native={path}");
                    } else if let Some(lib) = flag.strip_prefix("-l") {
                        println!("cargo:rustc-link-lib=dylib={lib}");
                    }
                }
            }
        } else {
            // No pkg-config entry; attempt bare link on the system library path.
            println!("cargo:rustc-link-lib=dylib=flint");
            println!(
                "cargo:warning=FLINT not found via pkg-config — \
                 trying bare -lflint.  Install FLINT (LGPL-3) and ensure \
                 its headers are on the include path."
            );
        }

        println!("cargo:rerun-if-changed=src/rust/coprocessor/flint.rs");
    }

    // Chapel parallel proof search bridge
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
