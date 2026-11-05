// SPDX-License-Identifier: MPL-2.0
//! Build script for ECHIDNA
//!
//! Chapel:  Chapel (.chpl) → Zig bridge → Rust
//! SPARK:   Ada/SPARK (echidna_spark.gpr) → Zig bridge → Rust
//!
//! SPARK build order:
//!   1. gprbuild -P src/ada/spark/echidna_spark.gpr
//!   2. cd src/zig && zig build -Dspark
//!   3. cargo build --features spark

#[cfg(feature = "chapel")]
#[path = "build_support/chapel.rs"]
mod chapel_link;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(echidna_chapel_real)");
    println!("cargo:rustc-check-cfg=cfg(echidna_chapel_stubs)");
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

    // Chapel parallel proof search bridge. Real mode also links the compiler's
    // runtime closure; a static Zig archive does not supply transitive links.
    #[cfg(feature = "chapel")]
    {
        chapel_link::configure(std::path::Path::new(env!("CARGO_MANIFEST_DIR")))
            .unwrap_or_else(|error| panic!("Chapel native link setup: {error}"));
        println!("cargo:rerun-if-changed=build_support/chapel.rs");
        println!("cargo:rerun-if-changed=src/zig_ffi/chapel_bridge.zig");
        println!("cargo:rerun-if-changed=src/zig_ffi/build.zig");
    }
}
