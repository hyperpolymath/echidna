// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MPL-2.0

#![allow(dead_code)]

//! Theorem prover backend implementations
//!
//! Supports 12 theorem provers across 4 tiers

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

use crate::core::{ProofState, Tactic, TacticResult};

pub mod outcome;
pub use outcome::{classify_anyhow_error, ProverOutcome};

pub mod io;
pub use io::{bounded_read_corpus_file, bounded_read_proof_file, MAX_PROOF_BYTES};

pub mod abc;
pub mod abella;
pub mod acl2;
pub mod acl2s;
pub mod agda;
pub mod agsyhol;
pub mod alloy;
pub mod altergo;
pub mod aprove;
pub mod arend;
pub mod athena;
pub mod boogie;
pub mod cadical;
pub mod cameleer;
pub mod cbmc;
pub mod chuffed;
pub mod connection_method;
pub mod coq;
pub mod cryptoverif;
pub mod csi;
pub mod cubical_agda;
pub mod cvc5;
pub mod dafny;
pub mod dedukti;
pub mod dreal;
pub mod easycrypt;
pub mod elk;
pub mod eprover;
pub mod faial;
pub mod framac;
pub mod fstar;
pub mod glpk;
pub mod gnatprove;
pub mod gpuverify;
pub mod hol4;
pub mod hol_light;
pub mod hp_ecosystem;
pub mod idris2;
pub mod ileancop;
pub mod imandra;
pub mod iprover;
pub mod isabelle;
pub mod isabelle_zf;
pub mod key;
pub mod keymaerax;
pub mod kissat;
pub mod konclude;
pub mod lambda_prolog;
pub mod lash;
pub mod lean;
pub mod lean3;
pub mod leo3;
pub mod liquid_haskell;
pub mod matita;
pub mod mercury;
pub mod metamath;
pub mod metitarski;
pub mod mettel2;
pub mod minisat;
pub mod minizinc;
pub mod minlog;
pub mod mizar;
pub mod mizar_ar;
pub mod mleancop;
pub mod nanocop;
pub mod naproche;
pub mod nitpick;
pub mod nunchaku;
pub mod nuprl;
pub mod nusmv;
pub mod opensmt;
pub mod ortools;
pub mod princess;
pub mod prism;
pub mod prob;
pub mod prover9;
pub mod proverif;
pub mod pvs;
pub mod qepcad;
pub mod redlog;
pub mod rocq;
pub mod satallax;
pub mod scip;
pub mod seahorn;
pub mod smtrat;
pub mod spass;
pub mod spin_checker;
pub mod stainless;
pub mod storm;
pub mod tamarin;
pub mod tlaps;
pub mod tlc;
pub mod tptp_output;
pub mod twee;
pub mod twelf;
pub mod typed_wasm;
pub mod uppaal;
pub mod uppaal_stratego;
pub mod vampire;
pub mod viper;
pub mod why3;
pub mod z3;
pub mod zipperposition;

/// Enumeration of all supported provers; defined in `echidna-core` and
/// re-exported here so existing `crate::provers::ProverKind` paths keep working.
pub use echidna_core::prover_kind::ProverKind;

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

    /// Optional GNN inference server URL for neural tactic ranking.
    /// When set and `neural_enabled` is true, suggest_tactics calls the GNN.
    pub gnn_api_url: Option<String>,

    /// Project root directory (EI-1, 2026-04-26).
    ///
    /// When `Some(p)`, prover backends that support session-based builds
    /// (today: Isabelle) will treat `p` as the project root and resolve
    /// theory imports from `p/ROOT`. Without this, `echidna prove` only
    /// understands single-file goals importing `Main` — which made
    /// Burrower's `attempt` mode unusable on real project proofs.
    /// We deliberately did NOT repurpose `library_paths` because Lean
    /// and HOL-Light already use it differently.
    pub project_root: Option<PathBuf>,

    /// Sandbox mode for prover invocation (safe-learning b, 2026-04-26).
    ///
    /// `None` (the default) preserves backwards-compatible behaviour and
    /// runs the prover as a plain subprocess. `Bwrap` and `Podman` route
    /// through `crate::executor::sandbox::SandboxConfig` and run the
    /// prover under the named isolation layer. The wiring uses the
    /// existing executor module — we do not reimplement sandboxing here.
    pub sandbox: SandboxMode,
}

/// Sandbox mode for prover invocation.
///
/// Stays a separate enum from `executor::sandbox::SandboxKind` so the
/// CLI surface is stable across executor refactors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum SandboxMode {
    /// No sandbox — direct subprocess. Backwards-compatible default.
    #[default]
    None,
    /// Bubblewrap namespace isolation (lightweight, no daemon required).
    Bwrap,
    /// Podman container isolation (full-featured, requires podman daemon).
    Podman,
}

impl std::str::FromStr for SandboxMode {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_ascii_lowercase().as_str() {
            "none" | "off" | "" => Ok(SandboxMode::None),
            "bwrap" | "bubblewrap" => Ok(SandboxMode::Bwrap),
            "podman" | "container" => Ok(SandboxMode::Podman),
            other => Err(format!(
                "unknown sandbox mode: {other} (expected one of: none, bwrap, podman)"
            )),
        }
    }
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            executable: PathBuf::new(),
            library_paths: vec![],
            args: vec![],
            timeout: 300, // 5 minutes
            neural_enabled: true,
            gnn_api_url: None,
            project_root: None,
            sandbox: SandboxMode::None,
        }
    }
}

/// GNN-augmented tactic suggestions: calls the Julia GNN server to rank premises,
/// then prepends top-k `Apply` and prover-specific `apply` tactics to the list.
/// Falls back silently (returns `hints` unchanged) if the server is unreachable
/// or `neural_enabled` is false or `gnn_api_url` is unset.
///
/// # Arguments
/// * `config`      – prover config supplying the GNN URL and neural flag
/// * `state`       – current proof state (goals, context, theorems)
/// * `prover_name` – short prover identifier used in `Tactic::Custom` args
/// * `hints`       – heuristic suggestions already assembled by the caller
/// * `limit`       – maximum number of tactics to return
#[allow(dead_code)]
pub(crate) async fn gnn_augment_tactics(
    config: &ProverConfig,
    state: &ProofState,
    prover_name: &str,
    mut hints: Vec<Tactic>,
    limit: usize,
) -> Vec<Tactic> {
    let url = match config.gnn_api_url.as_deref() {
        Some(u) if config.neural_enabled => u.to_string(),
        _ => return hints.into_iter().take(limit).collect(),
    };

    use crate::gnn::client::{GnnClient, GnnConfig};
    use crate::gnn::graph::ProofGraphBuilder;

    let graph = ProofGraphBuilder::new(4).build_from_proof_state(state);
    let mut gnn = GnnClient::with_config(GnnConfig {
        api_url: url,
        timeout_ms: 2000,
        top_k: 8,
        min_score: 0.1,
        request_embeddings: false,
        num_gnn_layers: 3,
        use_attention: true,
    });

    // Extract goal aspects from state metadata (written by AgentCore::process_goal)
    // so Julia's /gnn/rank can apply per-domain weights from prior outcomes.
    // When metadata has no "aspects" key (e.g. direct REPL invocation), aspects
    // is empty and behaviour is identical to the no-hint path.
    // Ping the server so rank_premises_with_aspects sees server_available = true.
    // Graceful: if check_health errors (server down), gnn.server_available stays
    // false and rank_premises_with_aspects returns empty — no disruption to callers.
    let _ = gnn.check_health().await;

    let aspects: Vec<String> = state
        .metadata
        .get("aspects")
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();
    // Boundary filter: only dotted "category.aspect" strings reach the learning-loop
    // key space. Structural meta-tags without a dot (e.g. "axiom", "constructor")
    // are excluded here so they never pollute domain_hints or training records.
    let aspects: Vec<String> = aspects.into_iter().filter(|s| s.contains('.')).collect();
    let result = gnn.rank_premises_with_aspects(&graph, &aspects).await;
    // Prepend apply tactics for top premises (in score order, before heuristic hints)
    let mut gnn_tactics: Vec<Tactic> = result
        .ranked_premises
        .iter()
        .take(5)
        .map(|premise: &String| Tactic::Custom {
            prover: prover_name.to_string(),
            command: "apply".to_string(),
            args: vec![premise.clone()],
        })
        .collect();
    gnn_tactics.append(&mut hints);
    gnn_tactics.into_iter().take(limit).collect()
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
    async fn apply_tactic(
        &self,
        state: &ProofState,
        tactic: &Tactic,
    ) -> anyhow::Result<TacticResult>;

    /// Check if a proof is valid
    async fn verify_proof(&self, state: &ProofState) -> anyhow::Result<bool>;

    /// Rich variant of `verify_proof` — returns a `ProverOutcome` describing
    /// exactly *what kind* of result was produced (proved, no-proof-found,
    /// timeout, input error, inconsistent premises, prover crash, system
    /// failure).
    ///
    /// The default implementation wraps `verify_proof`: on `Ok(true)` it
    /// returns `Proved`, on `Ok(false)` `NoProofFound`, and on `Err(e)` it
    /// hands the error to `classify_anyhow_error` so the system distinguishes
    /// timeouts, parse errors, and prover crashes from each other.  Backends
    /// that can observe richer signals (e.g. the Z3 backend can spot
    /// `assertions` produce UNSAT in isolation → `InconsistentPremises`)
    /// override this method to produce better classifications.
    async fn check(&self, state: &ProofState) -> anyhow::Result<ProverOutcome> {
        let start = std::time::Instant::now();
        let limit = self.config().timeout;
        match self.verify_proof(state).await {
            Ok(true) => Ok(ProverOutcome::Proved {
                elapsed_ms: start.elapsed().as_millis() as u64,
            }),
            Ok(false) => Ok(ProverOutcome::NoProofFound {
                elapsed_ms: start.elapsed().as_millis() as u64,
                reason: None,
            }),
            Err(e) => Ok(classify_anyhow_error(&e, limit)),
        }
    }

    /// Export proof to prover-specific format
    async fn export(&self, state: &ProofState) -> anyhow::Result<String>;

    /// Get suggested tactics using neural premise selection
    async fn suggest_tactics(
        &self,
        state: &ProofState,
        limit: usize,
    ) -> anyhow::Result<Vec<Tactic>>;

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
    pub fn create(
        kind: ProverKind,
        config: ProverConfig,
    ) -> anyhow::Result<Box<dyn ProverBackend>> {
        // Fill in default executable if not specified
        let config = if config.executable.as_os_str().is_empty() {
            ProverConfig {
                executable: PathBuf::from(kind.default_executable()),
                ..config
            }
        } else {
            config
        };

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
            ProverKind::Lean3 => Ok(Box::new(lean3::Lean3Backend::new(config))),
            ProverKind::Abella => Ok(Box::new(abella::AbellaBackend::new(config))),
            ProverKind::Dedukti => Ok(Box::new(dedukti::DeduktiBackend::new(config))),
            ProverKind::Cameleer => Ok(Box::new(cameleer::CameleerBackend::new(config))),
            ProverKind::ACL2s => Ok(Box::new(acl2s::Acl2sBackend::new(config))),
            ProverKind::IsabelleZF => Ok(Box::new(isabelle_zf::IsabelleZfBackend::new(config))),
            ProverKind::Boogie => Ok(Box::new(boogie::BoogieBackend::new(config))),
            ProverKind::Naproche => Ok(Box::new(naproche::NaprocheBackend::new(config))),
            ProverKind::Matita => Ok(Box::new(matita::MatitaBackend::new(config))),
            ProverKind::Arend => Ok(Box::new(arend::ArendBackend::new(config))),
            ProverKind::Athena => Ok(Box::new(athena::AthenaBackend::new(config))),
            ProverKind::LambdaProlog => {
                Ok(Box::new(lambda_prolog::LambdaPrologBackend::new(config)))
            },
            ProverKind::Mercury => Ok(Box::new(mercury::MercuryBackend::new(config))),
            ProverKind::Nitpick => Ok(Box::new(nitpick::NitpickBackend::new(config))),
            ProverKind::Nunchaku => Ok(Box::new(nunchaku::NunchakuBackend::new(config))),
            ProverKind::Vampire => Ok(Box::new(vampire::VampireBackend::new(config))),
            ProverKind::EProver => Ok(Box::new(eprover::EProverBackend::new(config))),
            ProverKind::SPASS => Ok(Box::new(spass::SPASSBackend::new(config))),
            ProverKind::AltErgo => Ok(Box::new(altergo::AltErgoBackend::new(config))),

            ProverKind::FStar => Ok(Box::new(fstar::FStarBackend::new(config))),
            ProverKind::Dafny => Ok(Box::new(dafny::DafnyBackend::new(config))),
            ProverKind::Why3 => Ok(Box::new(why3::Why3Backend::new(config))),
            ProverKind::GNATprove => Ok(Box::new(gnatprove::GNATproveBackend::new(config))),
            ProverKind::Stainless => Ok(Box::new(stainless::StainlessBackend::new(config))),
            ProverKind::LiquidHaskell => {
                Ok(Box::new(liquid_haskell::LiquidHaskellBackend::new(config)))
            },
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
            ProverKind::TypedWasm => Ok(Box::new(typed_wasm::TypedWasmBackend::new(config))),
            ProverKind::SPIN => Ok(Box::new(spin_checker::SpinBackend::new(config))),
            ProverKind::CBMC => Ok(Box::new(cbmc::CBMCBackend::new(config))),
            ProverKind::SeaHorn => Ok(Box::new(seahorn::SeaHornBackend::new(config))),
            ProverKind::CaDiCaL => Ok(Box::new(cadical::CaDiCaLBackend::new(config))),
            ProverKind::Kissat => Ok(Box::new(kissat::KissatBackend::new(config))),
            ProverKind::MiniSat => Ok(Box::new(minisat::MiniSatBackend::new(config))),
            ProverKind::NuSMV => Ok(Box::new(nusmv::NuSMVBackend::new(config))),
            ProverKind::TLC => Ok(Box::new(tlc::TLCBackend::new(config))),
            ProverKind::Alloy => Ok(Box::new(alloy::AlloyBackend::new(config))),
            ProverKind::Prism => Ok(Box::new(prism::PrismBackend::new(config))),
            ProverKind::UPPAAL => Ok(Box::new(uppaal::UppaalBackend::new(config))),
            ProverKind::FramaC => Ok(Box::new(framac::FramaCBackend::new(config))),
            ProverKind::Viper => Ok(Box::new(viper::ViperBackend::new(config))),
            ProverKind::Tamarin => Ok(Box::new(tamarin::TamarinBackend::new(config))),
            ProverKind::ProVerif => Ok(Box::new(proverif::ProVerifBackend::new(config))),
            ProverKind::KeY => Ok(Box::new(key::KeyBackend::new(config))),
            ProverKind::DReal => Ok(Box::new(dreal::DRealBackend::new(config))),
            ProverKind::ABC => Ok(Box::new(abc::AbcBackend::new(config))),
            ProverKind::GPUVerify => Ok(Box::new(gpuverify::GpuVerifyBackend::new(config))),
            ProverKind::Faial => Ok(Box::new(faial::FaialBackend::new(config))),
            ProverKind::CubicalAgda => Ok(Box::new(cubical_agda::CubicalAgdaBackend::new(config))),
            ProverKind::Zipperposition => {
                Ok(Box::new(zipperposition::ZipperpositionBackend::new(config)))
            },
            ProverKind::Prover9 => Ok(Box::new(prover9::Prover9Backend::new(config))),
            ProverKind::OpenSmt => Ok(Box::new(opensmt::OpenSmtBackend::new(config))),
            ProverKind::SmtRat => Ok(Box::new(smtrat::SmtRatBackend::new(config))),
            ProverKind::Rocq => Ok(Box::new(rocq::RocqBackend::new(config))),
            ProverKind::UppaalStratego => Ok(Box::new(
                uppaal_stratego::UppaalStrategoBackend::new(config),
            )),
            ProverKind::MizAR => Ok(Box::new(mizar_ar::MizARBackend::new(config))),
            ProverKind::IProver => Ok(Box::new(iprover::IProverBackend::new(config))),
            ProverKind::Princess => Ok(Box::new(princess::PrincessBackend::new(config))),
            ProverKind::Twee => Ok(Box::new(twee::TweeBackend::new(config))),
            ProverKind::MetiTarski => Ok(Box::new(metitarski::MetiTarskiBackend::new(config))),
            ProverKind::CSI => Ok(Box::new(csi::CSIBackend::new(config))),
            ProverKind::AProVE => Ok(Box::new(aprove::AProVEBackend::new(config))),
            ProverKind::KeYmaeraX => Ok(Box::new(keymaerax::KeYmaeraXBackend::new(config))),
            ProverKind::Qepcad => Ok(Box::new(qepcad::QepcadBackend::new(config))),
            ProverKind::Redlog => Ok(Box::new(redlog::RedlogBackend::new(config))),
            ProverKind::MleanCoP => Ok(Box::new(mleancop::MleanCopBackend::new(config))),
            ProverKind::IleanCoP => Ok(Box::new(ileancop::IleanCopBackend::new(config))),
            ProverKind::NanoCoP => Ok(Box::new(nanocop::NanoCopBackend::new(config))),
            ProverKind::MetTeL2 => Ok(Box::new(mettel2::MetTeL2Backend::new(config))),
            ProverKind::ELK => Ok(Box::new(elk::ElkBackend::new(config))),
            ProverKind::Konclude => Ok(Box::new(konclude::KoncludeBackend::new(config))),
            ProverKind::Storm => Ok(Box::new(storm::StormBackend::new(config))),
            ProverKind::ProB => Ok(Box::new(prob::ProBBackend::new(config))),
            ProverKind::EasyCrypt => Ok(Box::new(easycrypt::EasyCryptBackend::new(config))),
            ProverKind::CryptoVerif => Ok(Box::new(cryptoverif::CryptoVerifBackend::new(config))),
            ProverKind::Leo3 => Ok(Box::new(leo3::Leo3Backend::new(config))),
            ProverKind::Satallax => Ok(Box::new(satallax::SatallaxBackend::new(config))),
            ProverKind::Lash => Ok(Box::new(lash::LashBackend::new(config))),
            ProverKind::AgsyHOL => Ok(Box::new(agsyhol::AgsyholBackend::new(config))),
            // TypeLL and KatagoriaVerifier are real HP upstream binaries —
            // they continue to dispatch through HPEcosystemBackend.
            ProverKind::TypeLL | ProverKind::KatagoriaVerifier => Ok(Box::new(
                hp_ecosystem::HPEcosystemBackend::new(kind, config),
            )),

            // S3 extraction (2026-04-22): the 39 *TypeChecker discipline
            // variants all route through the unified TypedWasm engine,
            // parametrised by a discipline-specific TypeInfo. See
            // `typed_wasm::type_info_for` for the level-set mapping.
            ProverKind::TropicalTypeChecker
            | ProverKind::ChoreographicTypeChecker
            | ProverKind::EpistemicTypeChecker
            | ProverKind::EchoTypeChecker
            | ProverKind::SessionTypeChecker
            | ProverKind::ModalTypeChecker
            | ProverKind::QTTTypeChecker
            | ProverKind::EffectRowTypeChecker
            | ProverKind::DependentTypeChecker
            | ProverKind::RefinementTypeChecker
            | ProverKind::OrdinaryTypeChecker
            | ProverKind::PhantomTypeChecker
            | ProverKind::PolymorphicTypeChecker
            | ProverKind::ExistentialTypeChecker
            | ProverKind::HigherKindedTypeChecker
            | ProverKind::RowTypeChecker
            | ProverKind::SubtypingTypeChecker
            | ProverKind::IntersectionTypeChecker
            | ProverKind::UnionTypeChecker
            | ProverKind::GradualTypeChecker
            | ProverKind::HoareTypeChecker
            | ProverKind::IndexedTypeChecker
            | ProverKind::LinearTypeChecker
            | ProverKind::AffineTypeChecker
            | ProverKind::RelevantTypeChecker
            | ProverKind::OrderedTypeChecker
            | ProverKind::UniquenessTypeChecker
            | ProverKind::ImmutableTypeChecker
            | ProverKind::CapabilityTypeChecker
            | ProverKind::BunchedTypeChecker
            | ProverKind::TemporalTypeChecker
            | ProverKind::ProvabilityTypeChecker
            | ProverKind::ImpureTypeChecker
            | ProverKind::CoeffectTypeChecker
            | ProverKind::ProbabilisticTypeChecker
            | ProverKind::DyadicTypeChecker
            | ProverKind::HomotopyTypeChecker
            | ProverKind::CubicalTypeChecker
            | ProverKind::NominalTypeChecker => Ok(Box::new(
                typed_wasm::TypedWasmBackend::for_kind(kind, config),
            )),
        }
    }

    /// Detect prover from file extension
    pub fn detect_from_file(path: &Path) -> Option<ProverKind> {
        path.extension()?.to_str().and_then(|ext| match ext {
            "agda" => Some(ProverKind::Agda),
            "v" => Some(ProverKind::Coq),
            "lean" => Some(ProverKind::Lean),
            "thy" => Some(ProverKind::Isabelle),
            "smt2" => Some(ProverKind::Z3), // Could be CVC5 too
            "mm" => Some(ProverKind::Metamath),
            "ml" => Some(ProverKind::HOLLight),
            "miz" => Some(ProverKind::Mizar),
            "pvs" => Some(ProverKind::PVS),
            "lisp" => Some(ProverKind::ACL2),
            "sml" => Some(ProverKind::HOL4),
            "idr" => Some(ProverKind::Idris2),
            "p" | "tptp" => Some(ProverKind::Vampire), // TPTP format (could be E too)
            "dfg" => Some(ProverKind::SPASS),          // SPASS DFG format
            "ae" => Some(ProverKind::AltErgo),         // Alt-Ergo native format
            "why" | "mlw" => Some(ProverKind::Why3),   // Why3 / WhyML
            "fst" | "fsti" => Some(ProverKind::FStar), // F* source / interface
            "dfy" => Some(ProverKind::Dafny),          // Dafny format
            "ads" | "adb" | "gpr" => Some(ProverKind::GNATprove), // SPARK/Ada
            // Note: ".scala" and ".hs" are NOT auto-mapped to Stainless /
            // Liquid Haskell because plain Scala/Haskell sources are not
            // necessarily refinement-typed.  Caller must pass explicit kind.
            "tla" => Some(ProverKind::TLAPS),        // TLA+ format
            "elf" => Some(ProverKind::Twelf),        // Twelf LF format
            "nuprl" => Some(ProverKind::Nuprl),      // Nuprl format
            "minlog" => Some(ProverKind::Minlog),    // Minlog format
            "iml" => Some(ProverKind::Imandra),      // Imandra ML format
            "lp" | "mps" => Some(ProverKind::GLPK),  // LP/MIP format
            "pip" | "zpl" => Some(ProverKind::SCIP), // SCIP/ZIMPL format
            "mzn" | "dzn" => Some(ProverKind::MiniZinc), // MiniZinc format
            "fzn" => Some(ProverKind::Chuffed),      // FlatZinc (Chuffed input)
            "twasm" => Some(ProverKind::TypedWasm),  // TypedWasm program
            "pml" => Some(ProverKind::SPIN),         // Promela model
            "smv" => Some(ProverKind::NuSMV),        // SMV specification
            "als" => Some(ProverKind::Alloy),        // Alloy specification
            "pm" | "prism" => Some(ProverKind::Prism), // PRISM model
            "vpr" => Some(ProverKind::Viper),        // Viper Silver language
            "spthy" => Some(ProverKind::Tamarin),    // Tamarin security protocol theory
            "pv" => Some(ProverKind::ProVerif),      // ProVerif applied pi-calculus
            "cnf" => Some(ProverKind::CaDiCaL),      // DIMACS CNF (default SAT solver)
            "dr" => Some(ProverKind::DReal),         // dReal SMT-LIB (.dr extension)
            "aig" => Some(ProverKind::ABC),          // AIGER format (And-Inverter Graph)
            "blif" => Some(ProverKind::ABC),         // Berkeley Logic Interchange Format
            // GPU source files — default to GPUVerify for extension-only detection.
            // Use detect_from_file_content() to distinguish GPUVerify vs Faial.
            "cu" => Some(ProverKind::GPUVerify), // CUDA source (GPUVerify or Faial)
            "cl" => Some(ProverKind::GPUVerify), // OpenCL source (GPUVerify)
            "key" => Some(ProverKind::KeY),      // KeY proof problem file (JavaDL)
            // Note: .java files with JML annotations can also be detected via content-aware detection
            // Note: .c files only map to CBMC when containing __CPROVER directives
            // Note: .lean is shared between Lean 3 and Lean 4; default is Lean 4.
            // Use detect_from_file_content() for Lean 3 vs 4 disambiguation.
            "lean3" => Some(ProverKind::Lean3), // explicit extension
            "thm" => Some(ProverKind::Abella),  // Abella .thm files
            // Dedukti uses .dk; .lp (lambdapi dialect) is shadowed by GLPK above
            // since LP/MIP files dominate that extension in the wild — a .lp
            // input ambiguous between lambdapi and linear programming is
            // resolved as GLPK.  Use detect_from_file_content() to disambiguate.
            "dk" => Some(ProverKind::Dedukti),   // Dedukti / λΠ
            "bpl" => Some(ProverKind::Boogie),   // Boogie intermediate language
            "ftl" => Some(ProverKind::Naproche), // Naproche controlled-NL
            "ma" => Some(ProverKind::Matita),    // Matita proof file
            "ard" => Some(ProverKind::Arend),    // Arend cubical HoTT
            "ath" => Some(ProverKind::Athena),   // Athena
            "mod" | "sig" => Some(ProverKind::LambdaProlog), // λProlog module / signature
            "nun" => Some(ProverKind::Nunchaku), // Nunchaku input
            // Mercury uses .m which collides with OCaml conventions in
            // some file sets; content-aware detection deferred to
            // phase 2 (look for Mercury `:- module`, `:- pred`, etc).
            "pri" => Some(ProverKind::Princess), // Princess native format
            "trs" => Some(ProverKind::CSI),      // TRS rewriting system format (CSI/AProVE)
            _ => None,
        })
    }

    /// Content-aware prover detection for ambiguous file extensions
    ///
    /// For .c files, checks whether the source contains __CPROVER directives
    /// to determine if CBMC is the appropriate prover. For .lean files,
    /// checks for Lean 3 vs Lean 4 syntax markers.
    pub fn detect_from_file_content(path: &Path, content: &str) -> Option<ProverKind> {
        // Lean 3 / Lean 4 disambiguation — both share `.lean`. Lean 4
        // introduced `by` tactic blocks in place of `begin … end`, uses
        // `section`/`namespace` with `end <name>` trailers, and commonly
        // imports from `Mathlib.*` (capitalised). Lean 3 uses lowercase
        // `mathlib` paths, `begin … end` blocks, and `universes u v`
        // without the `u v : Level` annotation.
        if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if ext == "lean" {
                let is_lean3 = content.contains("begin\n")
                    || content.contains("\nbegin ")
                    || content.contains("\nend.")
                    || (content.contains("universes ") && !content.contains(" : Level"))
                    || content.contains("import data.")
                    || content.contains("import tactic.");
                let is_lean4 = content.contains("import Mathlib.")
                    || content.contains(":= by\n")
                    || content.contains(":= by ")
                    || content.contains("theorem ") && content.contains("= by");
                if is_lean3 && !is_lean4 {
                    return Some(ProverKind::Lean3);
                }
                if is_lean4 {
                    return Some(ProverKind::Lean);
                }
                // Ambiguous → default to Lean 4 (current).
                return Some(ProverKind::Lean);
            }
        }

        // First try extension-based detection for non-Lean cases.
        if let Some(kind) = Self::detect_from_file(path) {
            return Some(kind);
        }

        // Content-aware fallback for .java and .c files
        if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            // Java files with JML annotations → KeY
            if ext == "java"
                && (content.contains("//@")
                    || content.contains("/*@")
                    || content.contains("requires") && content.contains("ensures"))
            {
                return Some(ProverKind::KeY);
            }

            if ext == "c" || ext == "h" {
                // Frama-C ACSL annotations take priority (deductive verification)
                if content.contains("/*@") || content.contains("//@") {
                    return Some(ProverKind::FramaC);
                }
                // SeaHorn sassert / seahorn.h (LLVM-based CHC verification)
                if content.contains("sassert(")
                    || content.contains("seahorn/seahorn.h")
                    || content.contains("nd_int(")
                {
                    return Some(ProverKind::SeaHorn);
                }
                // CBMC __CPROVER directives (bounded model checking)
                if content.contains("__CPROVER_assert")
                    || content.contains("__CPROVER_assume")
                    || content.contains("__CPROVER")
                {
                    return Some(ProverKind::CBMC);
                }
            }
        }

        None
    }
}
