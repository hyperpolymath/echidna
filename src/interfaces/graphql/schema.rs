// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL schema definitions - wired to ECHIDNA core

use async_graphql::{Context, Enum, Object, Result, SimpleObject};
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use echidna::provers::ProverKind as CoreProverKind;

use crate::resolvers::EchidnaContext;

/// Supported theorem provers in ECHIDNA
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProverKind {
    Agda,
    Coq,
    Lean,
    Isabelle,
    Z3,
    CVC5,
    Metamath,
    HOLLight,
    Mizar,
    PVS,
    ACL2,
    HOL4,
    Idris2,
    Vampire,
    EProver,
    SPASS,
    AltErgo,
    FStar,
    Dafny,
    Why3,
    TLAPS,
    Twelf,
    Nuprl,
    Minlog,
    Imandra,
    GLPK,
    SCIP,
    MiniZinc,
    Chuffed,
    ORTools,
    Lean3,
    TypedWasm,
    SPIN,
    CBMC,
    SeaHorn,
    CaDiCaL,
    Kissat,
    MiniSat,
    NuSMV,
    TLC,
    Alloy,
    Prism,
    UPPAAL,
    FramaC,
    Viper,
    Tamarin,
    ProVerif,
    KeY,
    DReal,
    ABC,
    TypeLL,
    KatagoriaVerifier,
    TropicalTypeChecker,
    ChoreographicTypeChecker,
    EpistemicTypeChecker,
    EchoTypeChecker,
    SessionTypeChecker,
    ModalTypeChecker,
    QTTTypeChecker,
    EffectRowTypeChecker,
    DependentTypeChecker,
    RefinementTypeChecker,
    OrdinaryTypeChecker,
    PhantomTypeChecker,
    PolymorphicTypeChecker,
    ExistentialTypeChecker,
    HigherKindedTypeChecker,
    RowTypeChecker,
    SubtypingTypeChecker,
    IntersectionTypeChecker,
    UnionTypeChecker,
    GradualTypeChecker,
    HoareTypeChecker,
    IndexedTypeChecker,
    LinearTypeChecker,
    AffineTypeChecker,
    RelevantTypeChecker,
    OrderedTypeChecker,
    UniquenessTypeChecker,
    ImmutableTypeChecker,
    CapabilityTypeChecker,
    BunchedTypeChecker,
    TemporalTypeChecker,
    ProvabilityTypeChecker,
    ImpureTypeChecker,
    CoeffectTypeChecker,
    ProbabilisticTypeChecker,
    DyadicTypeChecker,
    HomotopyTypeChecker,
    CubicalTypeChecker,
    NominalTypeChecker,
    Abella,
    Dedukti,
    Cameleer,
    ACL2s,
    IsabelleZF,
    Boogie,
    Naproche,
    Matita,
    Arend,
    Athena,
    LambdaProlog,
    Mercury,
    Nitpick,
    Nunchaku,
    CubicalAgda,
    Zipperposition,
    Prover9,
    OpenSmt,
    SmtRat,
    Rocq,
    UppaalStratego,
    MizAR,
    GPUVerify,
    Faial,
    Leo3,
    Satallax,
    Lash,
    AgsyHOL,
    IProver,
    Princess,
    Twee,
    MetiTarski,
    CSI,
    AProVE,
    GNATprove,
    Stainless,
    LiquidHaskell,
    KeYmaeraX,
    Qepcad,
    Redlog,
    MleanCoP,
    IleanCoP,
    NanoCoP,
    MetTeL2,
    ELK,
    Konclude,
    Storm,
    ProB,
    EasyCrypt,
    CryptoVerif,
}

/// Status of a proof attempt
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProofStatus {
    Pending,
    InProgress,
    Success,
    Failed,
    Timeout,
    Error,
}

/// Proof state representation
#[derive(Debug, Clone, SimpleObject)]
pub struct ProofState {
    pub id: String,
    pub prover: ProverKind,
    pub goal: String,
    pub status: ProofStatus,
    pub proof_script: Vec<String>,
    pub goals_remaining: i32,
    pub time_elapsed: Option<f64>,
    pub error_message: Option<String>,
}

/// Tactic representation
#[derive(Debug, Clone, SimpleObject)]
pub struct Tactic {
    pub name: String,
    pub args: Vec<String>,
    pub description: Option<String>,
    pub confidence: Option<f64>,
}

/// Prover information
#[derive(Debug, Clone, SimpleObject)]
pub struct ProverInfo {
    pub kind: ProverKind,
    pub version: String,
    pub tier: i32,
    pub complexity: i32,
    pub available: bool,
}

pub struct QueryRoot;

#[Object]
impl QueryRoot {
    /// Get all available provers (all 30)
    async fn provers(&self, _ctx: &Context<'_>) -> Result<Vec<ProverInfo>> {
        let provers: Vec<ProverInfo> = CoreProverKind::all()
            .into_iter()
            .map(|kind| ProverInfo {
                kind: core_to_gql(&kind),
                version: format!("{:?} (ECHIDNA v0.1.0)", kind),
                tier: kind.tier() as i32,
                complexity: kind.complexity() as i32,
                available: true,
            })
            .collect();
        Ok(provers)
    }

    /// Get proof state by ID
    async fn proof_state(&self, ctx: &Context<'_>, id: String) -> Result<Option<ProofState>> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let sessions = echidna_ctx.sessions.read().await;

        let session_arc = match sessions.get(&id) {
            Some(s) => s.clone(),
            None => return Ok(None),
        };
        drop(sessions);

        let session = session_arc.lock().await;
        let elapsed = session.start_time.elapsed().as_secs_f64();

        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        let goals_remaining = session
            .state
            .as_ref()
            .map(|s| s.goals.len() as i32)
            .unwrap_or(0);

        let status = match session.status {
            crate::resolvers::SessionStatus::Pending => ProofStatus::Pending,
            crate::resolvers::SessionStatus::InProgress => ProofStatus::InProgress,
            crate::resolvers::SessionStatus::Success => ProofStatus::Success,
            crate::resolvers::SessionStatus::Failed => ProofStatus::Failed,
        };

        Ok(Some(ProofState {
            id: session.id.clone(),
            prover: core_to_gql(&session.prover_kind),
            goal: session.goal.clone(),
            status,
            proof_script: script,
            goals_remaining,
            time_elapsed: Some(elapsed),
            error_message: None,
        }))
    }

    /// List all proof attempts
    async fn list_proofs(
        &self,
        ctx: &Context<'_>,
        limit: Option<i32>,
        _status: Option<ProofStatus>,
    ) -> Result<Vec<ProofState>> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let sessions = echidna_ctx.sessions.read().await;
        let max = limit.unwrap_or(100) as usize;

        let mut proofs = Vec::new();
        for (_, session_arc) in sessions.iter().take(max) {
            let session = session_arc.lock().await;
            let elapsed = session.start_time.elapsed().as_secs_f64();

            let script: Vec<String> = session
                .state
                .as_ref()
                .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
                .unwrap_or_default();

            let goals_remaining = session
                .state
                .as_ref()
                .map(|s| s.goals.len() as i32)
                .unwrap_or(0);

            let status = match session.status {
                crate::resolvers::SessionStatus::Pending => ProofStatus::Pending,
                crate::resolvers::SessionStatus::InProgress => ProofStatus::InProgress,
                crate::resolvers::SessionStatus::Success => ProofStatus::Success,
                crate::resolvers::SessionStatus::Failed => ProofStatus::Failed,
            };

            proofs.push(ProofState {
                id: session.id.clone(),
                prover: core_to_gql(&session.prover_kind),
                goal: session.goal.clone(),
                status,
                proof_script: script,
                goals_remaining,
                time_elapsed: Some(elapsed),
                error_message: None,
            });
        }

        Ok(proofs)
    }

    /// Get suggested tactics for a proof state
    async fn suggest_tactics(
        &self,
        ctx: &Context<'_>,
        proof_id: String,
        limit: Option<i32>,
    ) -> Result<Vec<Tactic>> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let max = limit.unwrap_or(5) as usize;

        let core_tactics = echidna_ctx
            .suggest_tactics(&proof_id, max)
            .await
            .map_err(|e| async_graphql::Error::new(e.to_string()))?;

        Ok(core_tactics
            .iter()
            .map(|t| Tactic {
                name: format!("{:?}", t),
                args: vec![],
                description: Some("Suggested tactic".to_string()),
                confidence: None,
            })
            .collect())
    }

    /// Health check
    async fn health(&self) -> String {
        "OK".to_string()
    }
}

pub struct MutationRoot;

#[Object]
impl MutationRoot {
    /// Submit a new proof goal
    async fn submit_proof(
        &self,
        ctx: &Context<'_>,
        goal: String,
        prover: ProverKind,
    ) -> Result<ProofState> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let core_kind = gql_to_core(&prover);

        let proof_id = echidna_ctx
            .create_session(&goal, core_kind)
            .await
            .map_err(|e| async_graphql::Error::new(e.to_string()))?;

        // Fetch back the created session state
        let sessions = echidna_ctx.sessions.read().await;
        let session_arc = sessions.get(&proof_id).unwrap().clone();
        drop(sessions);
        let session = session_arc.lock().await;

        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();

        let goals_remaining = session
            .state
            .as_ref()
            .map(|s| s.goals.len() as i32)
            .unwrap_or(0);

        Ok(ProofState {
            id: proof_id,
            prover,
            goal,
            status: ProofStatus::InProgress,
            proof_script: script,
            goals_remaining,
            time_elapsed: Some(0.0),
            error_message: None,
        })
    }

    /// Apply a tactic to a proof state
    async fn apply_tactic(
        &self,
        ctx: &Context<'_>,
        proof_id: String,
        tactic: String,
        args: Vec<String>,
    ) -> Result<ProofState> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;

        let core_tactic = parse_tactic(&tactic, &args);

        let result = echidna_ctx
            .apply_tactic(&proof_id, core_tactic)
            .await
            .map_err(|e| async_graphql::Error::new(e.to_string()))?;

        // Fetch updated state
        let sessions = echidna_ctx.sessions.read().await;
        let session_arc = sessions
            .get(&proof_id)
            .ok_or_else(|| async_graphql::Error::new("Session not found"))?
            .clone();
        drop(sessions);
        let session = session_arc.lock().await;

        let elapsed = session.start_time.elapsed().as_secs_f64();
        let script: Vec<String> = session
            .state
            .as_ref()
            .map(|s| s.proof_script.iter().map(|t| format!("{:?}", t)).collect())
            .unwrap_or_default();
        let goals_remaining = session
            .state
            .as_ref()
            .map(|s| s.goals.len() as i32)
            .unwrap_or(0);

        let status = match session.status {
            crate::resolvers::SessionStatus::Pending => ProofStatus::Pending,
            crate::resolvers::SessionStatus::InProgress => ProofStatus::InProgress,
            crate::resolvers::SessionStatus::Success => ProofStatus::Success,
            crate::resolvers::SessionStatus::Failed => ProofStatus::Failed,
        };

        Ok(ProofState {
            id: session.id.clone(),
            prover: core_to_gql(&session.prover_kind),
            goal: session.goal.clone(),
            status,
            proof_script: script,
            goals_remaining,
            time_elapsed: Some(elapsed),
            error_message: match &result {
                CoreTacticResult::Error(msg) => Some(msg.clone()),
                _ => None,
            },
        })
    }

    /// Cancel a proof attempt
    async fn cancel_proof(&self, ctx: &Context<'_>, proof_id: String) -> Result<bool> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let mut sessions = echidna_ctx.sessions.write().await;
        Ok(sessions.remove(&proof_id).is_some())
    }
}

// ========== Helpers ==========

fn parse_tactic(name: &str, args: &[String]) -> CoreTactic {
    match name.to_lowercase().as_str() {
        "apply" => CoreTactic::Apply(args.first().cloned().unwrap_or_default()),
        "intro" => CoreTactic::Intro(args.first().cloned()),
        "rewrite" => CoreTactic::Rewrite(args.first().cloned().unwrap_or_default()),
        "simplify" | "simp" => CoreTactic::Simplify,
        "reflexivity" | "refl" => CoreTactic::Reflexivity,
        "assumption" => CoreTactic::Assumption,
        "cases" => CoreTactic::Cases(Term::Var(args.first().cloned().unwrap_or_default())),
        "induction" => CoreTactic::Induction(Term::Var(args.first().cloned().unwrap_or_default())),
        "exact" => CoreTactic::Exact(Term::Var(args.first().cloned().unwrap_or_default())),
        _ => CoreTactic::Custom {
            prover: "graphql".to_string(),
            command: name.to_string(),
            args: args.to_vec(),
        },
    }
}

fn core_to_gql(kind: &CoreProverKind) -> ProverKind {
    match kind {
        CoreProverKind::Agda => ProverKind::Agda,
        CoreProverKind::Coq => ProverKind::Coq,
        CoreProverKind::Lean => ProverKind::Lean,
        CoreProverKind::Isabelle => ProverKind::Isabelle,
        CoreProverKind::Z3 => ProverKind::Z3,
        CoreProverKind::CVC5 => ProverKind::CVC5,
        CoreProverKind::Metamath => ProverKind::Metamath,
        CoreProverKind::HOLLight => ProverKind::HOLLight,
        CoreProverKind::Mizar => ProverKind::Mizar,
        CoreProverKind::PVS => ProverKind::PVS,
        CoreProverKind::ACL2 => ProverKind::ACL2,
        CoreProverKind::HOL4 => ProverKind::HOL4,
        CoreProverKind::Idris2 => ProverKind::Idris2,
        CoreProverKind::Vampire => ProverKind::Vampire,
        CoreProverKind::EProver => ProverKind::EProver,
        CoreProverKind::SPASS => ProverKind::SPASS,
        CoreProverKind::AltErgo => ProverKind::AltErgo,
        CoreProverKind::FStar => ProverKind::FStar,
        CoreProverKind::Dafny => ProverKind::Dafny,
        CoreProverKind::Why3 => ProverKind::Why3,
        CoreProverKind::TLAPS => ProverKind::TLAPS,
        CoreProverKind::Twelf => ProverKind::Twelf,
        CoreProverKind::Nuprl => ProverKind::Nuprl,
        CoreProverKind::Minlog => ProverKind::Minlog,
        CoreProverKind::Imandra => ProverKind::Imandra,
        CoreProverKind::GLPK => ProverKind::GLPK,
        CoreProverKind::SCIP => ProverKind::SCIP,
        CoreProverKind::MiniZinc => ProverKind::MiniZinc,
        CoreProverKind::Chuffed => ProverKind::Chuffed,
        CoreProverKind::ORTools => ProverKind::ORTools,
        CoreProverKind::Lean3 => ProverKind::Lean3,
        CoreProverKind::TypedWasm => ProverKind::TypedWasm,
        CoreProverKind::SPIN => ProverKind::SPIN,
        CoreProverKind::CBMC => ProverKind::CBMC,
        CoreProverKind::SeaHorn => ProverKind::SeaHorn,
        CoreProverKind::CaDiCaL => ProverKind::CaDiCaL,
        CoreProverKind::Kissat => ProverKind::Kissat,
        CoreProverKind::MiniSat => ProverKind::MiniSat,
        CoreProverKind::NuSMV => ProverKind::NuSMV,
        CoreProverKind::TLC => ProverKind::TLC,
        CoreProverKind::Alloy => ProverKind::Alloy,
        CoreProverKind::Prism => ProverKind::Prism,
        CoreProverKind::UPPAAL => ProverKind::UPPAAL,
        CoreProverKind::FramaC => ProverKind::FramaC,
        CoreProverKind::Viper => ProverKind::Viper,
        CoreProverKind::Tamarin => ProverKind::Tamarin,
        CoreProverKind::ProVerif => ProverKind::ProVerif,
        CoreProverKind::KeY => ProverKind::KeY,
        CoreProverKind::DReal => ProverKind::DReal,
        CoreProverKind::ABC => ProverKind::ABC,
        CoreProverKind::TypeLL => ProverKind::TypeLL,
        CoreProverKind::KatagoriaVerifier => ProverKind::KatagoriaVerifier,
        CoreProverKind::TropicalTypeChecker => ProverKind::TropicalTypeChecker,
        CoreProverKind::ChoreographicTypeChecker => ProverKind::ChoreographicTypeChecker,
        CoreProverKind::EpistemicTypeChecker => ProverKind::EpistemicTypeChecker,
        CoreProverKind::EchoTypeChecker => ProverKind::EchoTypeChecker,
        CoreProverKind::SessionTypeChecker => ProverKind::SessionTypeChecker,
        CoreProverKind::ModalTypeChecker => ProverKind::ModalTypeChecker,
        CoreProverKind::QTTTypeChecker => ProverKind::QTTTypeChecker,
        CoreProverKind::EffectRowTypeChecker => ProverKind::EffectRowTypeChecker,
        CoreProverKind::DependentTypeChecker => ProverKind::DependentTypeChecker,
        CoreProverKind::RefinementTypeChecker => ProverKind::RefinementTypeChecker,
        CoreProverKind::OrdinaryTypeChecker => ProverKind::OrdinaryTypeChecker,
        CoreProverKind::PhantomTypeChecker => ProverKind::PhantomTypeChecker,
        CoreProverKind::PolymorphicTypeChecker => ProverKind::PolymorphicTypeChecker,
        CoreProverKind::ExistentialTypeChecker => ProverKind::ExistentialTypeChecker,
        CoreProverKind::HigherKindedTypeChecker => ProverKind::HigherKindedTypeChecker,
        CoreProverKind::RowTypeChecker => ProverKind::RowTypeChecker,
        CoreProverKind::SubtypingTypeChecker => ProverKind::SubtypingTypeChecker,
        CoreProverKind::IntersectionTypeChecker => ProverKind::IntersectionTypeChecker,
        CoreProverKind::UnionTypeChecker => ProverKind::UnionTypeChecker,
        CoreProverKind::GradualTypeChecker => ProverKind::GradualTypeChecker,
        CoreProverKind::HoareTypeChecker => ProverKind::HoareTypeChecker,
        CoreProverKind::IndexedTypeChecker => ProverKind::IndexedTypeChecker,
        CoreProverKind::LinearTypeChecker => ProverKind::LinearTypeChecker,
        CoreProverKind::AffineTypeChecker => ProverKind::AffineTypeChecker,
        CoreProverKind::RelevantTypeChecker => ProverKind::RelevantTypeChecker,
        CoreProverKind::OrderedTypeChecker => ProverKind::OrderedTypeChecker,
        CoreProverKind::UniquenessTypeChecker => ProverKind::UniquenessTypeChecker,
        CoreProverKind::ImmutableTypeChecker => ProverKind::ImmutableTypeChecker,
        CoreProverKind::CapabilityTypeChecker => ProverKind::CapabilityTypeChecker,
        CoreProverKind::BunchedTypeChecker => ProverKind::BunchedTypeChecker,
        CoreProverKind::TemporalTypeChecker => ProverKind::TemporalTypeChecker,
        CoreProverKind::ProvabilityTypeChecker => ProverKind::ProvabilityTypeChecker,
        CoreProverKind::ImpureTypeChecker => ProverKind::ImpureTypeChecker,
        CoreProverKind::CoeffectTypeChecker => ProverKind::CoeffectTypeChecker,
        CoreProverKind::ProbabilisticTypeChecker => ProverKind::ProbabilisticTypeChecker,
        CoreProverKind::DyadicTypeChecker => ProverKind::DyadicTypeChecker,
        CoreProverKind::HomotopyTypeChecker => ProverKind::HomotopyTypeChecker,
        CoreProverKind::CubicalTypeChecker => ProverKind::CubicalTypeChecker,
        CoreProverKind::NominalTypeChecker => ProverKind::NominalTypeChecker,
        CoreProverKind::Abella => ProverKind::Abella,
        CoreProverKind::Dedukti => ProverKind::Dedukti,
        CoreProverKind::Cameleer => ProverKind::Cameleer,
        CoreProverKind::ACL2s => ProverKind::ACL2s,
        CoreProverKind::IsabelleZF => ProverKind::IsabelleZF,
        CoreProverKind::Boogie => ProverKind::Boogie,
        CoreProverKind::Naproche => ProverKind::Naproche,
        CoreProverKind::Matita => ProverKind::Matita,
        CoreProverKind::Arend => ProverKind::Arend,
        CoreProverKind::Athena => ProverKind::Athena,
        CoreProverKind::LambdaProlog => ProverKind::LambdaProlog,
        CoreProverKind::Mercury => ProverKind::Mercury,
        CoreProverKind::Nitpick => ProverKind::Nitpick,
        CoreProverKind::Nunchaku => ProverKind::Nunchaku,
        CoreProverKind::CubicalAgda => ProverKind::CubicalAgda,
        CoreProverKind::Zipperposition => ProverKind::Zipperposition,
        CoreProverKind::Prover9 => ProverKind::Prover9,
        CoreProverKind::OpenSmt => ProverKind::OpenSmt,
        CoreProverKind::SmtRat => ProverKind::SmtRat,
        CoreProverKind::Rocq => ProverKind::Rocq,
        CoreProverKind::UppaalStratego => ProverKind::UppaalStratego,
        CoreProverKind::MizAR => ProverKind::MizAR,
        CoreProverKind::GPUVerify => ProverKind::GPUVerify,
        CoreProverKind::Faial => ProverKind::Faial,
        CoreProverKind::Leo3 => ProverKind::Leo3,
        CoreProverKind::Satallax => ProverKind::Satallax,
        CoreProverKind::Lash => ProverKind::Lash,
        CoreProverKind::AgsyHOL => ProverKind::AgsyHOL,
        CoreProverKind::IProver => ProverKind::IProver,
        CoreProverKind::Princess => ProverKind::Princess,
        CoreProverKind::Twee => ProverKind::Twee,
        CoreProverKind::MetiTarski => ProverKind::MetiTarski,
        CoreProverKind::CSI => ProverKind::CSI,
        CoreProverKind::AProVE => ProverKind::AProVE,
        CoreProverKind::GNATprove => ProverKind::GNATprove,
        CoreProverKind::Stainless => ProverKind::Stainless,
        CoreProverKind::LiquidHaskell => ProverKind::LiquidHaskell,
        CoreProverKind::KeYmaeraX => ProverKind::KeYmaeraX,
        CoreProverKind::Qepcad => ProverKind::Qepcad,
        CoreProverKind::Redlog => ProverKind::Redlog,
        CoreProverKind::MleanCoP => ProverKind::MleanCoP,
        CoreProverKind::IleanCoP => ProverKind::IleanCoP,
        CoreProverKind::NanoCoP => ProverKind::NanoCoP,
        CoreProverKind::MetTeL2 => ProverKind::MetTeL2,
        CoreProverKind::ELK => ProverKind::ELK,
        CoreProverKind::Konclude => ProverKind::Konclude,
        CoreProverKind::Storm => ProverKind::Storm,
        CoreProverKind::ProB => ProverKind::ProB,
        CoreProverKind::EasyCrypt => ProverKind::EasyCrypt,
        CoreProverKind::CryptoVerif => ProverKind::CryptoVerif,
    }
}

fn gql_to_core(kind: &ProverKind) -> CoreProverKind {
    match kind {
        ProverKind::Agda => CoreProverKind::Agda,
        ProverKind::Coq => CoreProverKind::Coq,
        ProverKind::Lean => CoreProverKind::Lean,
        ProverKind::Isabelle => CoreProverKind::Isabelle,
        ProverKind::Z3 => CoreProverKind::Z3,
        ProverKind::CVC5 => CoreProverKind::CVC5,
        ProverKind::Metamath => CoreProverKind::Metamath,
        ProverKind::HOLLight => CoreProverKind::HOLLight,
        ProverKind::Mizar => CoreProverKind::Mizar,
        ProverKind::PVS => CoreProverKind::PVS,
        ProverKind::ACL2 => CoreProverKind::ACL2,
        ProverKind::HOL4 => CoreProverKind::HOL4,
        ProverKind::Idris2 => CoreProverKind::Idris2,
        ProverKind::Vampire => CoreProverKind::Vampire,
        ProverKind::EProver => CoreProverKind::EProver,
        ProverKind::SPASS => CoreProverKind::SPASS,
        ProverKind::AltErgo => CoreProverKind::AltErgo,
        ProverKind::FStar => CoreProverKind::FStar,
        ProverKind::Dafny => CoreProverKind::Dafny,
        ProverKind::Why3 => CoreProverKind::Why3,
        ProverKind::TLAPS => CoreProverKind::TLAPS,
        ProverKind::Twelf => CoreProverKind::Twelf,
        ProverKind::Nuprl => CoreProverKind::Nuprl,
        ProverKind::Minlog => CoreProverKind::Minlog,
        ProverKind::Imandra => CoreProverKind::Imandra,
        ProverKind::GLPK => CoreProverKind::GLPK,
        ProverKind::SCIP => CoreProverKind::SCIP,
        ProverKind::MiniZinc => CoreProverKind::MiniZinc,
        ProverKind::Chuffed => CoreProverKind::Chuffed,
        ProverKind::ORTools => CoreProverKind::ORTools,
        ProverKind::Lean3 => CoreProverKind::Lean3,
        ProverKind::TypedWasm => CoreProverKind::TypedWasm,
        ProverKind::SPIN => CoreProverKind::SPIN,
        ProverKind::CBMC => CoreProverKind::CBMC,
        ProverKind::SeaHorn => CoreProverKind::SeaHorn,
        ProverKind::CaDiCaL => CoreProverKind::CaDiCaL,
        ProverKind::Kissat => CoreProverKind::Kissat,
        ProverKind::MiniSat => CoreProverKind::MiniSat,
        ProverKind::NuSMV => CoreProverKind::NuSMV,
        ProverKind::TLC => CoreProverKind::TLC,
        ProverKind::Alloy => CoreProverKind::Alloy,
        ProverKind::Prism => CoreProverKind::Prism,
        ProverKind::UPPAAL => CoreProverKind::UPPAAL,
        ProverKind::FramaC => CoreProverKind::FramaC,
        ProverKind::Viper => CoreProverKind::Viper,
        ProverKind::Tamarin => CoreProverKind::Tamarin,
        ProverKind::ProVerif => CoreProverKind::ProVerif,
        ProverKind::KeY => CoreProverKind::KeY,
        ProverKind::DReal => CoreProverKind::DReal,
        ProverKind::ABC => CoreProverKind::ABC,
        ProverKind::TypeLL => CoreProverKind::TypeLL,
        ProverKind::KatagoriaVerifier => CoreProverKind::KatagoriaVerifier,
        ProverKind::TropicalTypeChecker => CoreProverKind::TropicalTypeChecker,
        ProverKind::ChoreographicTypeChecker => CoreProverKind::ChoreographicTypeChecker,
        ProverKind::EpistemicTypeChecker => CoreProverKind::EpistemicTypeChecker,
        ProverKind::EchoTypeChecker => CoreProverKind::EchoTypeChecker,
        ProverKind::SessionTypeChecker => CoreProverKind::SessionTypeChecker,
        ProverKind::ModalTypeChecker => CoreProverKind::ModalTypeChecker,
        ProverKind::QTTTypeChecker => CoreProverKind::QTTTypeChecker,
        ProverKind::EffectRowTypeChecker => CoreProverKind::EffectRowTypeChecker,
        ProverKind::DependentTypeChecker => CoreProverKind::DependentTypeChecker,
        ProverKind::RefinementTypeChecker => CoreProverKind::RefinementTypeChecker,
        ProverKind::OrdinaryTypeChecker => CoreProverKind::OrdinaryTypeChecker,
        ProverKind::PhantomTypeChecker => CoreProverKind::PhantomTypeChecker,
        ProverKind::PolymorphicTypeChecker => CoreProverKind::PolymorphicTypeChecker,
        ProverKind::ExistentialTypeChecker => CoreProverKind::ExistentialTypeChecker,
        ProverKind::HigherKindedTypeChecker => CoreProverKind::HigherKindedTypeChecker,
        ProverKind::RowTypeChecker => CoreProverKind::RowTypeChecker,
        ProverKind::SubtypingTypeChecker => CoreProverKind::SubtypingTypeChecker,
        ProverKind::IntersectionTypeChecker => CoreProverKind::IntersectionTypeChecker,
        ProverKind::UnionTypeChecker => CoreProverKind::UnionTypeChecker,
        ProverKind::GradualTypeChecker => CoreProverKind::GradualTypeChecker,
        ProverKind::HoareTypeChecker => CoreProverKind::HoareTypeChecker,
        ProverKind::IndexedTypeChecker => CoreProverKind::IndexedTypeChecker,
        ProverKind::LinearTypeChecker => CoreProverKind::LinearTypeChecker,
        ProverKind::AffineTypeChecker => CoreProverKind::AffineTypeChecker,
        ProverKind::RelevantTypeChecker => CoreProverKind::RelevantTypeChecker,
        ProverKind::OrderedTypeChecker => CoreProverKind::OrderedTypeChecker,
        ProverKind::UniquenessTypeChecker => CoreProverKind::UniquenessTypeChecker,
        ProverKind::ImmutableTypeChecker => CoreProverKind::ImmutableTypeChecker,
        ProverKind::CapabilityTypeChecker => CoreProverKind::CapabilityTypeChecker,
        ProverKind::BunchedTypeChecker => CoreProverKind::BunchedTypeChecker,
        ProverKind::TemporalTypeChecker => CoreProverKind::TemporalTypeChecker,
        ProverKind::ProvabilityTypeChecker => CoreProverKind::ProvabilityTypeChecker,
        ProverKind::ImpureTypeChecker => CoreProverKind::ImpureTypeChecker,
        ProverKind::CoeffectTypeChecker => CoreProverKind::CoeffectTypeChecker,
        ProverKind::ProbabilisticTypeChecker => CoreProverKind::ProbabilisticTypeChecker,
        ProverKind::DyadicTypeChecker => CoreProverKind::DyadicTypeChecker,
        ProverKind::HomotopyTypeChecker => CoreProverKind::HomotopyTypeChecker,
        ProverKind::CubicalTypeChecker => CoreProverKind::CubicalTypeChecker,
        ProverKind::NominalTypeChecker => CoreProverKind::NominalTypeChecker,
        ProverKind::Abella => CoreProverKind::Abella,
        ProverKind::Dedukti => CoreProverKind::Dedukti,
        ProverKind::Cameleer => CoreProverKind::Cameleer,
        ProverKind::ACL2s => CoreProverKind::ACL2s,
        ProverKind::IsabelleZF => CoreProverKind::IsabelleZF,
        ProverKind::Boogie => CoreProverKind::Boogie,
        ProverKind::Naproche => CoreProverKind::Naproche,
        ProverKind::Matita => CoreProverKind::Matita,
        ProverKind::Arend => CoreProverKind::Arend,
        ProverKind::Athena => CoreProverKind::Athena,
        ProverKind::LambdaProlog => CoreProverKind::LambdaProlog,
        ProverKind::Mercury => CoreProverKind::Mercury,
        ProverKind::Nitpick => CoreProverKind::Nitpick,
        ProverKind::Nunchaku => CoreProverKind::Nunchaku,
        ProverKind::CubicalAgda => CoreProverKind::CubicalAgda,
        ProverKind::Zipperposition => CoreProverKind::Zipperposition,
        ProverKind::Prover9 => CoreProverKind::Prover9,
        ProverKind::OpenSmt => CoreProverKind::OpenSmt,
        ProverKind::SmtRat => CoreProverKind::SmtRat,
        ProverKind::Rocq => CoreProverKind::Rocq,
        ProverKind::UppaalStratego => CoreProverKind::UppaalStratego,
        ProverKind::MizAR => CoreProverKind::MizAR,
        ProverKind::GPUVerify => CoreProverKind::GPUVerify,
        ProverKind::Faial => CoreProverKind::Faial,
        ProverKind::Leo3 => CoreProverKind::Leo3,
        ProverKind::Satallax => CoreProverKind::Satallax,
        ProverKind::Lash => CoreProverKind::Lash,
        ProverKind::AgsyHOL => CoreProverKind::AgsyHOL,
        ProverKind::IProver => CoreProverKind::IProver,
        ProverKind::Princess => CoreProverKind::Princess,
        ProverKind::Twee => CoreProverKind::Twee,
        ProverKind::MetiTarski => CoreProverKind::MetiTarski,
        ProverKind::CSI => CoreProverKind::CSI,
        ProverKind::AProVE => CoreProverKind::AProVE,
        ProverKind::GNATprove => CoreProverKind::GNATprove,
        ProverKind::Stainless => CoreProverKind::Stainless,
        ProverKind::LiquidHaskell => CoreProverKind::LiquidHaskell,
        ProverKind::KeYmaeraX => CoreProverKind::KeYmaeraX,
        ProverKind::Qepcad => CoreProverKind::Qepcad,
        ProverKind::Redlog => CoreProverKind::Redlog,
        ProverKind::MleanCoP => CoreProverKind::MleanCoP,
        ProverKind::IleanCoP => CoreProverKind::IleanCoP,
        ProverKind::NanoCoP => CoreProverKind::NanoCoP,
        ProverKind::MetTeL2 => CoreProverKind::MetTeL2,
        ProverKind::ELK => CoreProverKind::ELK,
        ProverKind::Konclude => CoreProverKind::Konclude,
        ProverKind::Storm => CoreProverKind::Storm,
        ProverKind::ProB => CoreProverKind::ProB,
        ProverKind::EasyCrypt => CoreProverKind::EasyCrypt,
        ProverKind::CryptoVerif => CoreProverKind::CryptoVerif,
    }
}
