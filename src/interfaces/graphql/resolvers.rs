// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL resolvers - wired to ECHIDNA core

use echidna::core::{
    ProofState as CoreProofState, Tactic as CoreTactic, TacticResult as CoreTacticResult, Term,
};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};

// Import FFI wrapper
use crate::ffi_wrapper;

/// Wrapper for FFI-based prover backend
struct FfiProverBackend {
    handle: i32,
    config: ProverConfig,
}

impl FfiProverBackend {
    pub fn new(handle: i32) -> Self {
        FfiProverBackend { handle, config: ProverConfig::default() }
    }
}

#[async_trait::async_trait]
impl ProverBackend for FfiProverBackend {
    async fn parse_file(&self, path: std::path::PathBuf) -> anyhow::Result<CoreProofState> {
        let content = std::fs::read_to_string(&path)?;
        ffi_wrapper::parse_string(self.handle, &content)?;
        Ok(CoreProofState::new(Term::Var(content)))
    }

    async fn parse_string(&self, content: &str) -> anyhow::Result<CoreProofState> {
        ffi_wrapper::parse_string(self.handle, content)?;
        Ok(CoreProofState::new(Term::Var(content.to_string())))
    }

    async fn verify_proof(&self, state: &CoreProofState) -> anyhow::Result<bool> {
        ffi_wrapper::verify_proof(self.handle)
    }

    async fn apply_tactic(
        &self,
        state: &CoreProofState,
        tactic: &CoreTactic,
    ) -> anyhow::Result<CoreTacticResult> {
        let tactic_str = format!("{:?}", tactic);
        if ffi_wrapper::apply_tactic(self.handle, &tactic_str)? {
            Ok(CoreTacticResult::Success(state.clone()))
        } else {
            Ok(CoreTacticResult::Error("Tactic failed".to_string()))
        }
    }

    async fn suggest_tactics(
        &self,
        state: &CoreProofState,
        limit: usize,
    ) -> anyhow::Result<Vec<CoreTactic>> {
        let tactic_names = ffi_wrapper::suggest_tactics(self.handle, limit)?;
        let tactics = tactic_names
            .into_iter()
            .map(|name| CoreTactic::Custom {
                prover: "ffi".to_string(),
                command: name,
                args: vec![],
            })
            .collect();
        Ok(tactics)
    }

    async fn export(&self, state: &CoreProofState) -> anyhow::Result<String> {
        ffi_wrapper::export_proof(self.handle)
    }

    async fn version(&self) -> anyhow::Result<String> {
        ffi_wrapper::get_version()
    }

    fn kind(&self) -> CoreProverKind {
        CoreProverKind::Lean
    }

    async fn search_theorems(&self, _pattern: &str) -> anyhow::Result<Vec<String>> {
        Ok(Vec::new())
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

/// Helper trait to convert between GraphQL and core types
pub trait ProverKindExt {
    fn from_core(kind: CoreProverKind) -> Self;
    fn to_core(&self) -> CoreProverKind;
}

impl ProverKindExt for crate::schema::ProverKind {
    fn from_core(kind: CoreProverKind) -> Self {
        match kind {
            CoreProverKind::Agda => crate::schema::ProverKind::Agda,
            CoreProverKind::Coq => crate::schema::ProverKind::Coq,
            CoreProverKind::Lean => crate::schema::ProverKind::Lean,
            CoreProverKind::Isabelle => crate::schema::ProverKind::Isabelle,
            CoreProverKind::Z3 => crate::schema::ProverKind::Z3,
            CoreProverKind::CVC5 => crate::schema::ProverKind::CVC5,
            CoreProverKind::Metamath => crate::schema::ProverKind::Metamath,
            CoreProverKind::HOLLight => crate::schema::ProverKind::HOLLight,
            CoreProverKind::Mizar => crate::schema::ProverKind::Mizar,
            CoreProverKind::PVS => crate::schema::ProverKind::PVS,
            CoreProverKind::ACL2 => crate::schema::ProverKind::ACL2,
            CoreProverKind::HOL4 => crate::schema::ProverKind::HOL4,
            CoreProverKind::Idris2 => crate::schema::ProverKind::Idris2,
            CoreProverKind::Vampire => crate::schema::ProverKind::Vampire,
            CoreProverKind::EProver => crate::schema::ProverKind::EProver,
            CoreProverKind::SPASS => crate::schema::ProverKind::SPASS,
            CoreProverKind::AltErgo => crate::schema::ProverKind::AltErgo,
            CoreProverKind::FStar => crate::schema::ProverKind::FStar,
            CoreProverKind::Dafny => crate::schema::ProverKind::Dafny,
            CoreProverKind::Why3 => crate::schema::ProverKind::Why3,
            CoreProverKind::TLAPS => crate::schema::ProverKind::TLAPS,
            CoreProverKind::Twelf => crate::schema::ProverKind::Twelf,
            CoreProverKind::Nuprl => crate::schema::ProverKind::Nuprl,
            CoreProverKind::Minlog => crate::schema::ProverKind::Minlog,
            CoreProverKind::Imandra => crate::schema::ProverKind::Imandra,
            CoreProverKind::GLPK => crate::schema::ProverKind::GLPK,
            CoreProverKind::SCIP => crate::schema::ProverKind::SCIP,
            CoreProverKind::MiniZinc => crate::schema::ProverKind::MiniZinc,
            CoreProverKind::Chuffed => crate::schema::ProverKind::Chuffed,
            CoreProverKind::ORTools => crate::schema::ProverKind::ORTools,
            CoreProverKind::Lean3 => crate::schema::ProverKind::Lean3,
            CoreProverKind::TypedWasm => crate::schema::ProverKind::TypedWasm,
            CoreProverKind::SPIN => crate::schema::ProverKind::SPIN,
            CoreProverKind::CBMC => crate::schema::ProverKind::CBMC,
            CoreProverKind::SeaHorn => crate::schema::ProverKind::SeaHorn,
            CoreProverKind::CaDiCaL => crate::schema::ProverKind::CaDiCaL,
            CoreProverKind::Kissat => crate::schema::ProverKind::Kissat,
            CoreProverKind::MiniSat => crate::schema::ProverKind::MiniSat,
            CoreProverKind::NuSMV => crate::schema::ProverKind::NuSMV,
            CoreProverKind::TLC => crate::schema::ProverKind::TLC,
            CoreProverKind::Alloy => crate::schema::ProverKind::Alloy,
            CoreProverKind::Prism => crate::schema::ProverKind::Prism,
            CoreProverKind::UPPAAL => crate::schema::ProverKind::UPPAAL,
            CoreProverKind::FramaC => crate::schema::ProverKind::FramaC,
            CoreProverKind::Viper => crate::schema::ProverKind::Viper,
            CoreProverKind::Tamarin => crate::schema::ProverKind::Tamarin,
            CoreProverKind::ProVerif => crate::schema::ProverKind::ProVerif,
            CoreProverKind::KeY => crate::schema::ProverKind::KeY,
            CoreProverKind::DReal => crate::schema::ProverKind::DReal,
            CoreProverKind::ABC => crate::schema::ProverKind::ABC,
            CoreProverKind::TypeLL => crate::schema::ProverKind::TypeLL,
            CoreProverKind::KatagoriaVerifier => crate::schema::ProverKind::KatagoriaVerifier,
            CoreProverKind::TropicalTypeChecker => crate::schema::ProverKind::TropicalTypeChecker,
            CoreProverKind::ChoreographicTypeChecker => crate::schema::ProverKind::ChoreographicTypeChecker,
            CoreProverKind::EpistemicTypeChecker => crate::schema::ProverKind::EpistemicTypeChecker,
            CoreProverKind::EchoTypeChecker => crate::schema::ProverKind::EchoTypeChecker,
            CoreProverKind::SessionTypeChecker => crate::schema::ProverKind::SessionTypeChecker,
            CoreProverKind::ModalTypeChecker => crate::schema::ProverKind::ModalTypeChecker,
            CoreProverKind::QTTTypeChecker => crate::schema::ProverKind::QTTTypeChecker,
            CoreProverKind::EffectRowTypeChecker => crate::schema::ProverKind::EffectRowTypeChecker,
            CoreProverKind::DependentTypeChecker => crate::schema::ProverKind::DependentTypeChecker,
            CoreProverKind::RefinementTypeChecker => crate::schema::ProverKind::RefinementTypeChecker,
            CoreProverKind::OrdinaryTypeChecker => crate::schema::ProverKind::OrdinaryTypeChecker,
            CoreProverKind::PhantomTypeChecker => crate::schema::ProverKind::PhantomTypeChecker,
            CoreProverKind::PolymorphicTypeChecker => crate::schema::ProverKind::PolymorphicTypeChecker,
            CoreProverKind::ExistentialTypeChecker => crate::schema::ProverKind::ExistentialTypeChecker,
            CoreProverKind::HigherKindedTypeChecker => crate::schema::ProverKind::HigherKindedTypeChecker,
            CoreProverKind::RowTypeChecker => crate::schema::ProverKind::RowTypeChecker,
            CoreProverKind::SubtypingTypeChecker => crate::schema::ProverKind::SubtypingTypeChecker,
            CoreProverKind::IntersectionTypeChecker => crate::schema::ProverKind::IntersectionTypeChecker,
            CoreProverKind::UnionTypeChecker => crate::schema::ProverKind::UnionTypeChecker,
            CoreProverKind::GradualTypeChecker => crate::schema::ProverKind::GradualTypeChecker,
            CoreProverKind::HoareTypeChecker => crate::schema::ProverKind::HoareTypeChecker,
            CoreProverKind::IndexedTypeChecker => crate::schema::ProverKind::IndexedTypeChecker,
            CoreProverKind::LinearTypeChecker => crate::schema::ProverKind::LinearTypeChecker,
            CoreProverKind::AffineTypeChecker => crate::schema::ProverKind::AffineTypeChecker,
            CoreProverKind::RelevantTypeChecker => crate::schema::ProverKind::RelevantTypeChecker,
            CoreProverKind::OrderedTypeChecker => crate::schema::ProverKind::OrderedTypeChecker,
            CoreProverKind::UniquenessTypeChecker => crate::schema::ProverKind::UniquenessTypeChecker,
            CoreProverKind::ImmutableTypeChecker => crate::schema::ProverKind::ImmutableTypeChecker,
            CoreProverKind::CapabilityTypeChecker => crate::schema::ProverKind::CapabilityTypeChecker,
            CoreProverKind::BunchedTypeChecker => crate::schema::ProverKind::BunchedTypeChecker,
            CoreProverKind::TemporalTypeChecker => crate::schema::ProverKind::TemporalTypeChecker,
            CoreProverKind::ProvabilityTypeChecker => crate::schema::ProverKind::ProvabilityTypeChecker,
            CoreProverKind::ImpureTypeChecker => crate::schema::ProverKind::ImpureTypeChecker,
            CoreProverKind::CoeffectTypeChecker => crate::schema::ProverKind::CoeffectTypeChecker,
            CoreProverKind::ProbabilisticTypeChecker => crate::schema::ProverKind::ProbabilisticTypeChecker,
            CoreProverKind::DyadicTypeChecker => crate::schema::ProverKind::DyadicTypeChecker,
            CoreProverKind::HomotopyTypeChecker => crate::schema::ProverKind::HomotopyTypeChecker,
            CoreProverKind::CubicalTypeChecker => crate::schema::ProverKind::CubicalTypeChecker,
            CoreProverKind::NominalTypeChecker => crate::schema::ProverKind::NominalTypeChecker,
            CoreProverKind::Abella => crate::schema::ProverKind::Abella,
            CoreProverKind::Dedukti => crate::schema::ProverKind::Dedukti,
            CoreProverKind::Cameleer => crate::schema::ProverKind::Cameleer,
            CoreProverKind::ACL2s => crate::schema::ProverKind::ACL2s,
            CoreProverKind::IsabelleZF => crate::schema::ProverKind::IsabelleZF,
            CoreProverKind::Boogie => crate::schema::ProverKind::Boogie,
            CoreProverKind::Naproche => crate::schema::ProverKind::Naproche,
            CoreProverKind::Matita => crate::schema::ProverKind::Matita,
            CoreProverKind::Arend => crate::schema::ProverKind::Arend,
            CoreProverKind::Athena => crate::schema::ProverKind::Athena,
            CoreProverKind::LambdaProlog => crate::schema::ProverKind::LambdaProlog,
            CoreProverKind::Mercury => crate::schema::ProverKind::Mercury,
            CoreProverKind::Nitpick => crate::schema::ProverKind::Nitpick,
            CoreProverKind::Nunchaku => crate::schema::ProverKind::Nunchaku,
            CoreProverKind::CubicalAgda => crate::schema::ProverKind::CubicalAgda,
            CoreProverKind::Zipperposition => crate::schema::ProverKind::Zipperposition,
            CoreProverKind::Prover9 => crate::schema::ProverKind::Prover9,
            CoreProverKind::OpenSmt => crate::schema::ProverKind::OpenSmt,
            CoreProverKind::SmtRat => crate::schema::ProverKind::SmtRat,
            CoreProverKind::Rocq => crate::schema::ProverKind::Rocq,
            CoreProverKind::UppaalStratego => crate::schema::ProverKind::UppaalStratego,
            CoreProverKind::MizAR => crate::schema::ProverKind::MizAR,
        }
    }

    fn to_core(&self) -> CoreProverKind {
        match self {
            crate::schema::ProverKind::Agda => CoreProverKind::Agda,
            crate::schema::ProverKind::Coq => CoreProverKind::Coq,
            crate::schema::ProverKind::Lean => CoreProverKind::Lean,
            crate::schema::ProverKind::Isabelle => CoreProverKind::Isabelle,
            crate::schema::ProverKind::Z3 => CoreProverKind::Z3,
            crate::schema::ProverKind::CVC5 => CoreProverKind::CVC5,
            crate::schema::ProverKind::Metamath => CoreProverKind::Metamath,
            crate::schema::ProverKind::HOLLight => CoreProverKind::HOLLight,
            crate::schema::ProverKind::Mizar => CoreProverKind::Mizar,
            crate::schema::ProverKind::PVS => CoreProverKind::PVS,
            crate::schema::ProverKind::ACL2 => CoreProverKind::ACL2,
            crate::schema::ProverKind::HOL4 => CoreProverKind::HOL4,
            crate::schema::ProverKind::Idris2 => CoreProverKind::Idris2,
            crate::schema::ProverKind::Vampire => CoreProverKind::Vampire,
            crate::schema::ProverKind::EProver => CoreProverKind::EProver,
            crate::schema::ProverKind::SPASS => CoreProverKind::SPASS,
            crate::schema::ProverKind::AltErgo => CoreProverKind::AltErgo,
            crate::schema::ProverKind::FStar => CoreProverKind::FStar,
            crate::schema::ProverKind::Dafny => CoreProverKind::Dafny,
            crate::schema::ProverKind::Why3 => CoreProverKind::Why3,
            crate::schema::ProverKind::TLAPS => CoreProverKind::TLAPS,
            crate::schema::ProverKind::Twelf => CoreProverKind::Twelf,
            crate::schema::ProverKind::Nuprl => CoreProverKind::Nuprl,
            crate::schema::ProverKind::Minlog => CoreProverKind::Minlog,
            crate::schema::ProverKind::Imandra => CoreProverKind::Imandra,
            crate::schema::ProverKind::GLPK => CoreProverKind::GLPK,
            crate::schema::ProverKind::SCIP => CoreProverKind::SCIP,
            crate::schema::ProverKind::MiniZinc => CoreProverKind::MiniZinc,
            crate::schema::ProverKind::Chuffed => CoreProverKind::Chuffed,
            crate::schema::ProverKind::ORTools => CoreProverKind::ORTools,
            crate::schema::ProverKind::Lean3 => CoreProverKind::Lean3,
            crate::schema::ProverKind::TypedWasm => CoreProverKind::TypedWasm,
            crate::schema::ProverKind::SPIN => CoreProverKind::SPIN,
            crate::schema::ProverKind::CBMC => CoreProverKind::CBMC,
            crate::schema::ProverKind::SeaHorn => CoreProverKind::SeaHorn,
            crate::schema::ProverKind::CaDiCaL => CoreProverKind::CaDiCaL,
            crate::schema::ProverKind::Kissat => CoreProverKind::Kissat,
            crate::schema::ProverKind::MiniSat => CoreProverKind::MiniSat,
            crate::schema::ProverKind::NuSMV => CoreProverKind::NuSMV,
            crate::schema::ProverKind::TLC => CoreProverKind::TLC,
            crate::schema::ProverKind::Alloy => CoreProverKind::Alloy,
            crate::schema::ProverKind::Prism => CoreProverKind::Prism,
            crate::schema::ProverKind::UPPAAL => CoreProverKind::UPPAAL,
            crate::schema::ProverKind::FramaC => CoreProverKind::FramaC,
            crate::schema::ProverKind::Viper => CoreProverKind::Viper,
            crate::schema::ProverKind::Tamarin => CoreProverKind::Tamarin,
            crate::schema::ProverKind::ProVerif => CoreProverKind::ProVerif,
            crate::schema::ProverKind::KeY => CoreProverKind::KeY,
            crate::schema::ProverKind::DReal => CoreProverKind::DReal,
            crate::schema::ProverKind::ABC => CoreProverKind::ABC,
            crate::schema::ProverKind::TypeLL => CoreProverKind::TypeLL,
            crate::schema::ProverKind::KatagoriaVerifier => CoreProverKind::KatagoriaVerifier,
            crate::schema::ProverKind::TropicalTypeChecker => CoreProverKind::TropicalTypeChecker,
            crate::schema::ProverKind::ChoreographicTypeChecker => CoreProverKind::ChoreographicTypeChecker,
            crate::schema::ProverKind::EpistemicTypeChecker => CoreProverKind::EpistemicTypeChecker,
            crate::schema::ProverKind::EchoTypeChecker => CoreProverKind::EchoTypeChecker,
            crate::schema::ProverKind::SessionTypeChecker => CoreProverKind::SessionTypeChecker,
            crate::schema::ProverKind::ModalTypeChecker => CoreProverKind::ModalTypeChecker,
            crate::schema::ProverKind::QTTTypeChecker => CoreProverKind::QTTTypeChecker,
            crate::schema::ProverKind::EffectRowTypeChecker => CoreProverKind::EffectRowTypeChecker,
            crate::schema::ProverKind::DependentTypeChecker => CoreProverKind::DependentTypeChecker,
            crate::schema::ProverKind::RefinementTypeChecker => CoreProverKind::RefinementTypeChecker,
            crate::schema::ProverKind::OrdinaryTypeChecker => CoreProverKind::OrdinaryTypeChecker,
            crate::schema::ProverKind::PhantomTypeChecker => CoreProverKind::PhantomTypeChecker,
            crate::schema::ProverKind::PolymorphicTypeChecker => CoreProverKind::PolymorphicTypeChecker,
            crate::schema::ProverKind::ExistentialTypeChecker => CoreProverKind::ExistentialTypeChecker,
            crate::schema::ProverKind::HigherKindedTypeChecker => CoreProverKind::HigherKindedTypeChecker,
            crate::schema::ProverKind::RowTypeChecker => CoreProverKind::RowTypeChecker,
            crate::schema::ProverKind::SubtypingTypeChecker => CoreProverKind::SubtypingTypeChecker,
            crate::schema::ProverKind::IntersectionTypeChecker => CoreProverKind::IntersectionTypeChecker,
            crate::schema::ProverKind::UnionTypeChecker => CoreProverKind::UnionTypeChecker,
            crate::schema::ProverKind::GradualTypeChecker => CoreProverKind::GradualTypeChecker,
            crate::schema::ProverKind::HoareTypeChecker => CoreProverKind::HoareTypeChecker,
            crate::schema::ProverKind::IndexedTypeChecker => CoreProverKind::IndexedTypeChecker,
            crate::schema::ProverKind::LinearTypeChecker => CoreProverKind::LinearTypeChecker,
            crate::schema::ProverKind::AffineTypeChecker => CoreProverKind::AffineTypeChecker,
            crate::schema::ProverKind::RelevantTypeChecker => CoreProverKind::RelevantTypeChecker,
            crate::schema::ProverKind::OrderedTypeChecker => CoreProverKind::OrderedTypeChecker,
            crate::schema::ProverKind::UniquenessTypeChecker => CoreProverKind::UniquenessTypeChecker,
            crate::schema::ProverKind::ImmutableTypeChecker => CoreProverKind::ImmutableTypeChecker,
            crate::schema::ProverKind::CapabilityTypeChecker => CoreProverKind::CapabilityTypeChecker,
            crate::schema::ProverKind::BunchedTypeChecker => CoreProverKind::BunchedTypeChecker,
            crate::schema::ProverKind::TemporalTypeChecker => CoreProverKind::TemporalTypeChecker,
            crate::schema::ProverKind::ProvabilityTypeChecker => CoreProverKind::ProvabilityTypeChecker,
            crate::schema::ProverKind::ImpureTypeChecker => CoreProverKind::ImpureTypeChecker,
            crate::schema::ProverKind::CoeffectTypeChecker => CoreProverKind::CoeffectTypeChecker,
            crate::schema::ProverKind::ProbabilisticTypeChecker => CoreProverKind::ProbabilisticTypeChecker,
            crate::schema::ProverKind::DyadicTypeChecker => CoreProverKind::DyadicTypeChecker,
            crate::schema::ProverKind::HomotopyTypeChecker => CoreProverKind::HomotopyTypeChecker,
            crate::schema::ProverKind::CubicalTypeChecker => CoreProverKind::CubicalTypeChecker,
            crate::schema::ProverKind::NominalTypeChecker => CoreProverKind::NominalTypeChecker,
            crate::schema::ProverKind::Abella => CoreProverKind::Abella,
            crate::schema::ProverKind::Dedukti => CoreProverKind::Dedukti,
            crate::schema::ProverKind::Cameleer => CoreProverKind::Cameleer,
            crate::schema::ProverKind::ACL2s => CoreProverKind::ACL2s,
            crate::schema::ProverKind::IsabelleZF => CoreProverKind::IsabelleZF,
            crate::schema::ProverKind::Boogie => CoreProverKind::Boogie,
            crate::schema::ProverKind::Naproche => CoreProverKind::Naproche,
            crate::schema::ProverKind::Matita => CoreProverKind::Matita,
            crate::schema::ProverKind::Arend => CoreProverKind::Arend,
            crate::schema::ProverKind::Athena => CoreProverKind::Athena,
            crate::schema::ProverKind::LambdaProlog => CoreProverKind::LambdaProlog,
            crate::schema::ProverKind::Mercury => CoreProverKind::Mercury,
            crate::schema::ProverKind::Nitpick => CoreProverKind::Nitpick,
            crate::schema::ProverKind::Nunchaku => CoreProverKind::Nunchaku,
            crate::schema::ProverKind::CubicalAgda => CoreProverKind::CubicalAgda,
            crate::schema::ProverKind::Zipperposition => CoreProverKind::Zipperposition,
            crate::schema::ProverKind::Prover9 => CoreProverKind::Prover9,
            crate::schema::ProverKind::OpenSmt => CoreProverKind::OpenSmt,
            crate::schema::ProverKind::SmtRat => CoreProverKind::SmtRat,
            crate::schema::ProverKind::Rocq => CoreProverKind::Rocq,
            crate::schema::ProverKind::UppaalStratego => CoreProverKind::UppaalStratego,
            crate::schema::ProverKind::MizAR => CoreProverKind::MizAR,
        }
    }
}

/// A proof session managed by the GraphQL server
pub struct ProofSession {
    pub id: String,
    pub prover_kind: CoreProverKind,
    pub prover: Box<dyn ProverBackend>,
    pub state: Option<CoreProofState>,
    pub goal: String,
    pub status: SessionStatus,
    pub history: Vec<String>,
    pub start_time: std::time::Instant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionStatus {
    Pending,
    InProgress,
    Success,
    Failed,
}

/// Shared state for GraphQL context
pub struct EchidnaContext {
    pub sessions: Arc<RwLock<HashMap<String, Arc<Mutex<ProofSession>>>>>,
    pub ml_client: reqwest::Client,
    pub ml_api_url: String,
    pub ffi_initialized: bool,
}

impl EchidnaContext {
    pub fn new() -> Self {
        let ml_client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(10))
            .build()
            .expect("Failed to create HTTP client");

        // Initialize FFI layer
        let ffi_initialized = ffi_wrapper::init_ffi().is_ok();
        if ffi_initialized {
            tracing::info!("FFI layer initialized successfully");
        } else {
            tracing::warn!("FFI layer initialization failed, falling back to direct Rust calls");
        }

        EchidnaContext {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            ml_client,
            ml_api_url: "http://127.0.0.1:8090".to_string(),
            ffi_initialized,
        }
    }

    pub async fn create_session(&self, goal: &str, kind: CoreProverKind) -> anyhow::Result<String> {
        let proof_id = uuid::Uuid::new_v4().to_string();

        if self.ffi_initialized {
            // Use FFI path
            let ffi_kind =
                ffi_wrapper::prover_kind_to_ffi(&crate::schema::ProverKind::from_core(kind));
            match ffi_wrapper::create_prover(ffi_kind) {
                Ok(handle) => {
                    // Parse via FFI
                    if ffi_wrapper::parse_string(handle, goal).is_ok() {
                        let session = ProofSession {
                            id: proof_id.clone(),
                            prover_kind: kind,
                            prover: Box::new(FfiProverBackend::new(handle)),
                            state: Some(CoreProofState::new(Term::Var(goal.to_string()))),
                            goal: goal.to_string(),
                            status: SessionStatus::InProgress,
                            history: vec![],
                            start_time: std::time::Instant::now(),
                        };

                        self.sessions
                            .write()
                            .await
                            .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

                        return Ok(proof_id);
                    }
                },
                Err(e) => {
                    tracing::warn!("FFI path failed, falling back to direct: {}", e);
                },
            }
        }

        // Fallback to direct Rust path
        let config = ProverConfig::default();
        let prover = ProverFactory::create(kind, config)?;

        let proof_state = prover.parse_string(goal).await?;

        let session = ProofSession {
            id: proof_id.clone(),
            prover_kind: kind,
            prover,
            state: Some(proof_state),
            goal: goal.to_string(),
            status: SessionStatus::InProgress,
            history: vec![],
            start_time: std::time::Instant::now(),
        };

        self.sessions
            .write()
            .await
            .insert(proof_id.clone(), Arc::new(Mutex::new(session)));

        Ok(proof_id)
    }

    pub async fn apply_tactic(
        &self,
        proof_id: &str,
        tactic: CoreTactic,
    ) -> anyhow::Result<CoreTacticResult> {
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(proof_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found: {}", proof_id))?
            .clone();
        drop(sessions);

        let mut session = session_arc.lock().await;
        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No proof state"))?;

        let result = session.prover.apply_tactic(proof_state, &tactic).await?;

        match &result {
            CoreTacticResult::Success(new_state) => {
                let complete = new_state.is_complete();
                session.state = Some(new_state.clone());
                session.history.push(format!("{:?}", tactic));
                if complete {
                    session.status = SessionStatus::Success;
                }
            },
            CoreTacticResult::QED => {
                session.status = SessionStatus::Success;
                if let Some(s) = session.state.as_mut() {
                    s.goals.clear();
                }
            },
            CoreTacticResult::Error(_) => {},
        }

        Ok(result)
    }

    pub async fn suggest_tactics(
        &self,
        proof_id: &str,
        limit: usize,
    ) -> anyhow::Result<Vec<CoreTactic>> {
        let sessions = self.sessions.read().await;
        let session_arc = sessions
            .get(proof_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found: {}", proof_id))?
            .clone();
        drop(sessions);

        let session = session_arc.lock().await;
        let proof_state = session
            .state
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No proof state"))?;

        // Try Julia ML first
        let goal_str = proof_state
            .goals
            .first()
            .map(|g| format!("{}", g.target))
            .unwrap_or_default();

        let julia_req = serde_json::json!({
            "goal": goal_str,
            "prover": format!("{:?}", session.prover_kind),
            "top_k": limit
        });

        if let Ok(resp) = self
            .ml_client
            .post(format!("{}/suggest", self.ml_api_url))
            .json(&julia_req)
            .send()
            .await
        {
            if resp.status().is_success() {
                if let Ok(ml_resp) = resp.json::<serde_json::Value>().await {
                    if let Some(suggestions_arr) = ml_resp["suggestions"].as_array() {
                        let tactics: Vec<CoreTactic> = suggestions_arr
                            .iter()
                            .filter_map(|s| {
                                let name = s["tactic"].as_str()?;
                                Some(CoreTactic::Custom {
                                    prover: "ml".to_string(),
                                    command: name.to_string(),
                                    args: vec![],
                                })
                            })
                            .collect();

                        if !tactics.is_empty() {
                            return Ok(tactics);
                        }
                    }
                }
            }
        }

        // Fallback to prover suggestions
        session.prover.suggest_tactics(proof_state, limit).await
    }
}
