// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: util. Moved verbatim from main.rs (hotspot split).

use anyhow::Result;
use echidna::{ProverConfig, ProverKind};
use indicatif::{ProgressBar, ProgressStyle};
use std::path::PathBuf;

/// Initialize tracing/logging; logs go to stderr when `to_stderr` is set.
pub(crate) fn init_tracing(verbose: bool, to_stderr: bool) {
    use tracing_subscriber::filter::EnvFilter;
    use tracing_subscriber::{fmt, prelude::*};

    let filter = if verbose {
        EnvFilter::new("echidna=debug,info")
    } else {
        EnvFilter::new("echidna=info,warn")
    };

    let registry = tracing_subscriber::registry().with(filter);
    if to_stderr {
        registry
            .with(fmt::layer().with_writer(std::io::stderr))
            .init();
    } else {
        registry.with(fmt::layer()).init();
    }
}

/// Detect prover from file extension or use specified prover
pub(crate) fn detect_prover(
    prover_kind: Option<ProverKind>,
    file: &std::path::Path,
) -> Result<ProverKind> {
    if let Some(kind) = prover_kind {
        return Ok(kind);
    }

    echidna::provers::ProverFactory::detect_from_file(file).ok_or_else(|| {
        anyhow::anyhow!(
            "Could not detect prover from file extension: {}. Please specify with --prover",
            file.display()
        )
    })
}

/// Create prover configuration
pub(crate) fn create_config(
    kind: ProverKind,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    project_root: Option<PathBuf>,
    sandbox: &str,
) -> Result<ProverConfig> {
    let sandbox_mode: echidna::provers::SandboxMode =
        sandbox.parse().map_err(|e: String| anyhow::anyhow!(e))?;

    let config = ProverConfig {
        timeout,
        neural_enabled: neural,
        executable: executable.unwrap_or_else(|| get_default_executable(kind)),
        library_paths: if library.is_empty() {
            ProverConfig::default().library_paths
        } else {
            library
        },
        project_root,
        sandbox: sandbox_mode,
        ..ProverConfig::default()
    };

    Ok(config)
}

/// Get default executable path for a prover
pub(crate) fn get_default_executable(kind: ProverKind) -> PathBuf {
    match kind {
        ProverKind::Agda => PathBuf::from("agda"),
        ProverKind::Coq => PathBuf::from("coqtop"),
        ProverKind::Lean => PathBuf::from("lean"),
        ProverKind::Isabelle => PathBuf::from("isabelle"),
        ProverKind::Z3 => PathBuf::from("z3"),
        ProverKind::CVC5 => PathBuf::from("cvc5"),
        ProverKind::Metamath => PathBuf::from("metamath"),
        ProverKind::HOLLight => PathBuf::from("ocaml"),
        ProverKind::Mizar => PathBuf::from("verifier"),
        ProverKind::PVS => PathBuf::from("pvs"),
        ProverKind::ACL2 => PathBuf::from("acl2"),
        ProverKind::HOL4 => PathBuf::from("hol"),
        ProverKind::Idris2 => PathBuf::from("idris2"),
        ProverKind::Vampire => PathBuf::from("vampire"),
        ProverKind::EProver => PathBuf::from("eprover"),
        ProverKind::SPASS => PathBuf::from("SPASS"),
        ProverKind::AltErgo => PathBuf::from("alt-ergo"),
        ProverKind::FStar => PathBuf::from("fstar.exe"),
        ProverKind::Dafny => PathBuf::from("dafny"),
        ProverKind::Why3 => PathBuf::from("why3"),
        ProverKind::TLAPS => PathBuf::from("tlapm"),
        ProverKind::Twelf => PathBuf::from("twelf-server"),
        ProverKind::Nuprl => PathBuf::from("nuprl"),
        ProverKind::Minlog => PathBuf::from("minlog"),
        ProverKind::Imandra => PathBuf::from("imandra"),
        ProverKind::GLPK => PathBuf::from("glpsol"),
        ProverKind::SCIP => PathBuf::from("scip"),
        ProverKind::MiniZinc => PathBuf::from("minizinc"),
        ProverKind::Chuffed => PathBuf::from("fzn-chuffed"),
        ProverKind::ORTools => PathBuf::from("ortools_solve"),
        ProverKind::TypedWasm => PathBuf::from("idris2"),
        ProverKind::SPIN => PathBuf::from("spin"),
        ProverKind::CBMC => PathBuf::from("cbmc"),
        ProverKind::CaDiCaL => PathBuf::from("cadical"),
        ProverKind::Kissat => PathBuf::from("kissat"),
        ProverKind::MiniSat => PathBuf::from("minisat"),
        ProverKind::NuSMV => PathBuf::from("nuXmv"),
        ProverKind::TLC => PathBuf::from("tlc2.TLC"),
        ProverKind::Alloy => PathBuf::from("alloy"),
        ProverKind::Prism => PathBuf::from("prism"),
        ProverKind::UPPAAL => PathBuf::from("verifyta"),
        ProverKind::FramaC => PathBuf::from("frama-c"),
        ProverKind::SeaHorn => PathBuf::from("seahorn"),
        ProverKind::Viper => PathBuf::from("viper"),
        ProverKind::Tamarin => PathBuf::from("tamarin-prover"),
        ProverKind::ProVerif => PathBuf::from("proverif"),
        ProverKind::KeY => PathBuf::from("key"),
        ProverKind::DReal => PathBuf::from("dreal"),
        ProverKind::ABC => PathBuf::from("abc"),
        // HP ecosystem: route through the TypeLL kernel CLI, with two named
        // exceptions (katagoria, tropical-type-check). Mirrors provers/mod.rs
        // default_executable() — source of truth is that function.
        kind if kind.is_hp_ecosystem() => PathBuf::from(kind.default_executable()),
        _ => PathBuf::from(kind.default_executable()),
    }
}

/// Create a progress bar with standard styling
pub(crate) fn create_progress_bar(message: &str) -> ProgressBar {
    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.green} {msg}")
            .expect("Failed to set progress bar template"),
    );
    pb.set_message(message.to_string());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb
}
