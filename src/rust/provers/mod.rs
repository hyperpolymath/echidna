// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

#![allow(dead_code)]

//! Theorem prover backend implementations
//!
//! Supports 12 theorem provers across 4 tiers

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::core::{ProofState, Tactic, TacticResult, Term};

pub mod agda;
pub mod coq;
pub mod lean;
pub mod isabelle;
pub mod z3;
pub mod cvc5;
pub mod metamath;
pub mod hol_light;
pub mod mizar;
pub mod pvs;
pub mod acl2;
pub mod hol4;
pub mod idris2;
pub mod vampire;
pub mod eprover;
pub mod spass;
pub mod altergo;
pub mod fstar;
pub mod dafny;
pub mod why3;
pub mod tlaps;
pub mod twelf;
pub mod nuprl;
pub mod minlog;
pub mod imandra;
pub mod glpk;
pub mod scip;
pub mod minizinc;
pub mod chuffed;
pub mod ortools;

/// Enumeration of all supported provers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProverKind {
    // Tier 1: Original + SMT solvers
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    CVC5,

    // Tier 2: "Big Six" completion
    Metamath,
    HOLLight,
    Mizar,

    // Tier 3: Additional coverage
    PVS,
    ACL2,

    // Tier 4: Advanced
    HOL4,

    // Extended: Additional provers
    Idris2,

    // Tier 5: First-Order ATPs
    Vampire,
    EProver,
    SPASS,
    AltErgo,

    // Tier 6: Dependent types + effects, auto-active, orchestration
    FStar,
    Dafny,
    Why3,

    // Tier 7: Specialized / niche
    TLAPS,
    Twelf,
    Nuprl,
    Minlog,
    Imandra,

    // Tier 8: Constraint solvers
    GLPK,
    SCIP,
    MiniZinc,
    Chuffed,
    ORTools,
}

impl std::str::FromStr for ProverKind {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "agda" => Ok(ProverKind::Agda),
            "coq" => Ok(ProverKind::Coq),
            "lean" => Ok(ProverKind::Lean),
            "isabelle" => Ok(ProverKind::Isabelle),
            "z3" => Ok(ProverKind::Z3),
            "cvc5" => Ok(ProverKind::CVC5),
            "metamath" => Ok(ProverKind::Metamath),
            "hollight" | "hol-light" => Ok(ProverKind::HOLLight),
            "mizar" => Ok(ProverKind::Mizar),
            "pvs" => Ok(ProverKind::PVS),
            "acl2" => Ok(ProverKind::ACL2),
            "hol4" => Ok(ProverKind::HOL4),
            "idris2" | "idris" => Ok(ProverKind::Idris2),
            "vampire" => Ok(ProverKind::Vampire),
            "eprover" | "e" => Ok(ProverKind::EProver),
            "spass" => Ok(ProverKind::SPASS),
            "altergo" | "alt-ergo" => Ok(ProverKind::AltErgo),
            "fstar" | "f*" | "f-star" => Ok(ProverKind::FStar),
            "dafny" => Ok(ProverKind::Dafny),
            "why3" => Ok(ProverKind::Why3),
            "tlaps" | "tla+" => Ok(ProverKind::TLAPS),
            "twelf" => Ok(ProverKind::Twelf),
            "nuprl" => Ok(ProverKind::Nuprl),
            "minlog" => Ok(ProverKind::Minlog),
            "imandra" => Ok(ProverKind::Imandra),
            "glpk" => Ok(ProverKind::GLPK),
            "scip" => Ok(ProverKind::SCIP),
            "minizinc" | "mzn" => Ok(ProverKind::MiniZinc),
            "chuffed" => Ok(ProverKind::Chuffed),
            "ortools" | "or-tools" => Ok(ProverKind::ORTools),
            _ => Err(anyhow::anyhow!("Unknown prover: {}", s)),
        }
    }
}

impl std::fmt::Display for ProverKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ProverKind {
    /// All core provers for 1.0 (12 total)
    pub fn all_core() -> Vec<ProverKind> {
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HOLLight,
            ProverKind::Mizar,
            ProverKind::PVS,
            ProverKind::ACL2,
            ProverKind::HOL4,
        ]
    }

    /// All provers including extended coverage
    pub fn all() -> Vec<ProverKind> {
        let mut provers = Self::all_core();
        provers.extend_from_slice(&[
            ProverKind::Idris2,
            ProverKind::Vampire,
            ProverKind::EProver,
            ProverKind::SPASS,
            ProverKind::AltErgo,
            ProverKind::FStar,
            ProverKind::Dafny,
            ProverKind::Why3,
            ProverKind::TLAPS,
            ProverKind::Twelf,
            ProverKind::Nuprl,
            ProverKind::Minlog,
            ProverKind::Imandra,
            ProverKind::GLPK,
            ProverKind::SCIP,
            ProverKind::MiniZinc,
            ProverKind::Chuffed,
            ProverKind::ORTools,
        ]);
        provers
    }

    /// Get complexity rating (1-5, lower is easier)
    pub fn complexity(&self) -> u8 {
        match self {
            ProverKind::Metamath => 2,
            ProverKind::Agda => 3,
            ProverKind::HOLLight => 3,
            ProverKind::Mizar => 3,
            ProverKind::Lean => 3,
            ProverKind::Coq => 3,
            ProverKind::Isabelle => 4,
            ProverKind::Z3 => 2,
            ProverKind::CVC5 => 2,
            ProverKind::PVS => 4,
            ProverKind::ACL2 => 4,
            ProverKind::HOL4 => 5,
            ProverKind::Idris2 => 3,
            ProverKind::Vampire => 2,  // Automated, relatively simple
            ProverKind::EProver => 2,  // Similar to Vampire
            ProverKind::SPASS => 2,    // Automated FOL
            ProverKind::AltErgo => 2,  // SMT + FOL
            ProverKind::FStar => 3,    // Dependent types + effects
            ProverKind::Dafny => 2,    // Auto-active
            ProverKind::Why3 => 3,     // Multi-prover orchestration
            ProverKind::TLAPS => 4,    // TLA+ proof system
            ProverKind::Twelf => 4,    // Logical framework
            ProverKind::Nuprl => 4,    // Constructive type theory
            ProverKind::Minlog => 4,   // Minimal logic
            ProverKind::Imandra => 3,  // ML-based reasoning
            ProverKind::GLPK => 2,     // LP solver
            ProverKind::SCIP => 3,     // MINLP solver
            ProverKind::MiniZinc => 2, // Constraint modelling
            ProverKind::Chuffed => 2,  // CP solver
            ProverKind::ORTools => 2,  // Constraint/optimization solver
        }
    }

    /// Get tier (1-5)
    pub fn tier(&self) -> u8 {
        match self {
            ProverKind::Agda | ProverKind::Coq | ProverKind::Lean |
            ProverKind::Isabelle | ProverKind::Z3 | ProverKind::CVC5 => 1,

            ProverKind::Metamath | ProverKind::HOLLight | ProverKind::Mizar => 2,

            ProverKind::PVS | ProverKind::ACL2 => 3,

            ProverKind::HOL4 => 4,

            // Extended tier (same as Tier 1 in capability)
            ProverKind::Idris2 => 1,

            // Tier 5: First-Order ATPs
            ProverKind::Vampire => 5,
            ProverKind::EProver => 5,
            ProverKind::SPASS => 5,
            ProverKind::AltErgo => 5,

            // Tier 6: Dependent types + effects, auto-active
            ProverKind::FStar => 1,  // Small kernel, dependent types
            ProverKind::Dafny => 2,  // Auto-active (relies on Boogie->Z3)
            ProverKind::Why3 => 2,   // Multi-prover orchestration

            // Tier 7: Specialized / niche
            ProverKind::TLAPS => 2,
            ProverKind::Twelf => 4,
            ProverKind::Nuprl => 4,
            ProverKind::Minlog => 4,
            ProverKind::Imandra => 2,

            // Tier 8: Constraint solvers
            ProverKind::GLPK => 5,
            ProverKind::SCIP => 5,
            ProverKind::MiniZinc => 5,
            ProverKind::Chuffed => 5,
            ProverKind::ORTools => 5,
        }
    }

    /// Get expected implementation time in weeks
    pub fn implementation_time(&self) -> f32 {
        match self {
            ProverKind::Metamath => 1.5,
            ProverKind::Z3 | ProverKind::CVC5 => 1.0,
            ProverKind::HOLLight | ProverKind::Mizar => 2.0,
            ProverKind::Agda | ProverKind::Lean | ProverKind::Coq => 2.5,
            ProverKind::Isabelle => 3.0,
            ProverKind::PVS | ProverKind::ACL2 => 3.5,
            ProverKind::HOL4 => 4.0,
            ProverKind::Idris2 => 2.5,
            ProverKind::Vampire => 1.5,  // Automated, TPTP format
            ProverKind::EProver => 1.5,  // Similar to Vampire
            ProverKind::SPASS => 1.5,    // DFG format
            ProverKind::AltErgo => 1.5,  // Native format
            ProverKind::FStar => 2.5,    // Dependent types + effects
            ProverKind::Dafny => 2.0,    // Auto-active, Boogie pipeline
            ProverKind::Why3 => 2.0,     // Multi-prover
            ProverKind::TLAPS => 2.5,    // TLA+ specific
            ProverKind::Twelf => 3.0,    // LF framework
            ProverKind::Nuprl => 3.0,    // Constructive type theory
            ProverKind::Minlog => 2.5,   // Minimal logic
            ProverKind::Imandra => 2.0,  // ML-based
            ProverKind::GLPK => 1.0,     // LP API
            ProverKind::SCIP => 1.5,     // MINLP API
            ProverKind::MiniZinc => 1.0, // Constraint modelling
            ProverKind::Chuffed => 1.0,  // CP solver
            ProverKind::ORTools => 1.5,  // Constraint/optimization
        }
    }
}

/// Configuration for a prover backend
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProverConfig {
    /// Path to prover executable
    pub executable: PathBuf,

    /// Library/standard library paths
    pub library_paths: Vec<PathBuf>,

    /// Additional arguments
    pub args: Vec<String>,

    /// Timeout in seconds
    pub timeout: u64,

    /// Enable neural premise selection
    pub neural_enabled: bool,
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            executable: PathBuf::new(),
            library_paths: vec![],
            args: vec![],
            timeout: 300,  // 5 minutes
            neural_enabled: true,
        }
    }
}

/// Universal trait for theorem prover backends
#[async_trait]
pub trait ProverBackend: Send + Sync {
    /// Get prover kind
    fn kind(&self) -> ProverKind;

    /// Get prover version
    async fn version(&self) -> anyhow::Result<String>;

    /// Parse a proof file into ProofState
    async fn parse_file(&self, path: PathBuf) -> anyhow::Result<ProofState>;

    /// Parse a proof from string
    async fn parse_string(&self, content: &str) -> anyhow::Result<ProofState>;

    /// Apply a tactic to current proof state
    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic)
        -> anyhow::Result<TacticResult>;

    /// Check if a proof is valid
    async fn verify_proof(&self, state: &ProofState) -> anyhow::Result<bool>;

    /// Export proof to prover-specific format
    async fn export(&self, state: &ProofState) -> anyhow::Result<String>;

    /// Get suggested tactics using neural premise selection
    async fn suggest_tactics(&self, state: &ProofState, limit: usize)
        -> anyhow::Result<Vec<Tactic>>;

    /// Search for theorems matching a pattern
    async fn search_theorems(&self, pattern: &str) -> anyhow::Result<Vec<String>>;

    /// Get configuration
    fn config(&self) -> &ProverConfig;

    /// Set configuration
    fn set_config(&mut self, config: ProverConfig);

    /// Attempt to prove a goal (synchronous wrapper for actor use)
    fn prove(&self, goal: &crate::core::Goal) -> anyhow::Result<ProofState> {
        // Default implementation: create initial proof state from goal
        Ok(ProofState {
            goals: vec![goal.clone()],
            context: crate::core::Context::default(),
            proof_script: vec![],
            metadata: std::collections::HashMap::new(),
        })
    }
}

/// Factory for creating prover backends
pub struct ProverFactory;

impl ProverFactory {
    pub fn create(kind: ProverKind, config: ProverConfig) -> anyhow::Result<Box<dyn ProverBackend>> {
        match kind {
            ProverKind::Agda => Ok(Box::new(agda::AgdaBackend::new(config))),
            ProverKind::Coq => Ok(Box::new(coq::CoqBackend::new(config))),
            ProverKind::Lean => Ok(Box::new(lean::LeanBackend::new(config))),
            ProverKind::Isabelle => Ok(Box::new(isabelle::IsabelleBackend::new(config))),
            ProverKind::Z3 => Ok(Box::new(z3::Z3Backend::new(config))),
            ProverKind::CVC5 => Ok(Box::new(cvc5::CVC5Backend::new(config))),
            ProverKind::Metamath => Ok(Box::new(metamath::MetamathBackend::new(config))),
            ProverKind::HOLLight => Ok(Box::new(hol_light::HolLightBackend::new(config))),
            ProverKind::Mizar => Ok(Box::new(mizar::MizarBackend::new(config))),
            ProverKind::PVS => Ok(Box::new(pvs::PVSBackend::new(config))),
            ProverKind::ACL2 => Ok(Box::new(acl2::ACL2Backend::new(config))),
            ProverKind::HOL4 => Ok(Box::new(hol4::Hol4Backend::new(config))),
            ProverKind::Idris2 => Ok(Box::new(idris2::Idris2Backend::new(config))),
            ProverKind::Vampire => Ok(Box::new(vampire::VampireBackend::new(config))),
            ProverKind::EProver => Ok(Box::new(eprover::EProverBackend::new(config))),
            ProverKind::SPASS => Ok(Box::new(spass::SPASSBackend::new(config))),
            ProverKind::AltErgo => Ok(Box::new(altergo::AltErgoBackend::new(config))),
            ProverKind::FStar => Ok(Box::new(fstar::FStarBackend::new(config))),
            ProverKind::Dafny => Ok(Box::new(dafny::DafnyBackend::new(config))),
            ProverKind::Why3 => Ok(Box::new(why3::Why3Backend::new(config))),
            ProverKind::TLAPS => Ok(Box::new(tlaps::TLAPSBackend::new(config))),
            ProverKind::Twelf => Ok(Box::new(twelf::TwelfBackend::new(config))),
            ProverKind::Nuprl => Ok(Box::new(nuprl::NuprlBackend::new(config))),
            ProverKind::Minlog => Ok(Box::new(minlog::MinlogBackend::new(config))),
            ProverKind::Imandra => Ok(Box::new(imandra::ImandraBackend::new(config))),
            ProverKind::GLPK => Ok(Box::new(glpk::GLPKBackend::new(config))),
            ProverKind::SCIP => Ok(Box::new(scip::SCIPBackend::new(config))),
            ProverKind::MiniZinc => Ok(Box::new(minizinc::MiniZincBackend::new(config))),
            ProverKind::Chuffed => Ok(Box::new(chuffed::ChuffedBackend::new(config))),
            ProverKind::ORTools => Ok(Box::new(ortools::ORToolsBackend::new(config))),
        }
    }

    /// Detect prover from file extension
    pub fn detect_from_file(path: &PathBuf) -> Option<ProverKind> {
        path.extension()?.to_str().and_then(|ext| match ext {
            "agda" => Some(ProverKind::Agda),
            "v" => Some(ProverKind::Coq),
            "lean" => Some(ProverKind::Lean),
            "thy" => Some(ProverKind::Isabelle),
            "smt2" => Some(ProverKind::Z3),  // Could be CVC5 too
            "mm" => Some(ProverKind::Metamath),
            "ml" => Some(ProverKind::HOLLight),
            "miz" => Some(ProverKind::Mizar),
            "pvs" => Some(ProverKind::PVS),
            "lisp" => Some(ProverKind::ACL2),
            "sml" => Some(ProverKind::HOL4),
            "idr" => Some(ProverKind::Idris2),
            "p" | "tptp" => Some(ProverKind::Vampire),  // TPTP format (could be E too)
            "dfg" => Some(ProverKind::SPASS),  // SPASS DFG format
            "ae" => Some(ProverKind::AltErgo),  // Alt-Ergo native format
            "why" | "mlw" => Some(ProverKind::Why3),  // Why3 / WhyML
            "fst" | "fsti" => Some(ProverKind::FStar),  // F* source / interface
            "dfy" => Some(ProverKind::Dafny),  // Dafny format
            "tla" => Some(ProverKind::TLAPS),  // TLA+ format
            "elf" => Some(ProverKind::Twelf),  // Twelf LF format
            "nuprl" => Some(ProverKind::Nuprl),  // Nuprl format
            "minlog" => Some(ProverKind::Minlog),  // Minlog format
            "iml" => Some(ProverKind::Imandra),  // Imandra ML format
            "lp" | "mps" => Some(ProverKind::GLPK),  // LP/MIP format
            "pip" | "zpl" => Some(ProverKind::SCIP),  // SCIP/ZIMPL format
            "mzn" | "dzn" => Some(ProverKind::MiniZinc),  // MiniZinc format
            "fzn" => Some(ProverKind::Chuffed),  // FlatZinc (Chuffed input)
            _ => None,
        })
    }
}
