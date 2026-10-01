// SPDX-License-Identifier: MPL-2.0
// GraphQL schema definitions - wired to ECHIDNA core

use async_graphql::{Context, Enum, Object, Result, SimpleObject};
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};
use echidna::provers::{ProverConfig, ProverFactory, ProverKind as CoreProverKind};
use std::str::FromStr;
use std::time::Instant;

use crate::resolvers::EchidnaContext;

/// Supported theorem provers in ECHIDNA.
//
// Variant names mirror the well-known prover acronyms (PVS, SPASS, TLAPS,
// GLPK, …); keeping them upper-case matches the core `ProverKind` and every
// other place these tools are referenced.
#[allow(clippy::upper_case_acronyms)]
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

// =============================================================================
// Types added 2026-06-01 for echidnabot ↔ echidna seam (issue #180).
//
// These mirror the typed taxonomy now surfaced by REST `/api/verify`
// (`outcome`, optional `mode` / `smt_status`) and the suggestion shape
// the echidnabot Julia-ML client expects (`tactic` / `confidence` /
// `explanation`).
// =============================================================================

/// Typed outcome from a verifyProof call.
///
/// Mirrors the `outcome` field on REST `/api/verify` so GraphQL clients
/// can distinguish e.g. `Timeout` from `NoProofFound` without parsing
/// strings. Added 2026-06-01 (issue #180).
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum VerifyOutcome {
    /// Prover returned a verified proof.
    Proved,
    /// Prover finished without a proof.
    NoProofFound,
    /// Input could not be parsed or was empty.
    InvalidInput,
    /// Prover does not support a feature in the input.
    UnsupportedFeature,
    /// Prover exhausted its time budget.
    Timeout,
    /// Premises are mutually inconsistent.
    InconsistentPremises,
    /// Prover exited with an error.
    ProverError,
    /// Echidna-side error (FFI / I/O / sandbox).
    SystemError,
}

impl VerifyOutcome {
    /// Map the REST `outcome: String` representation onto the enum.
    pub fn from_rest_str(s: &str) -> VerifyOutcome {
        match s.to_uppercase().as_str() {
            "PROVED" => VerifyOutcome::Proved,
            "NO_PROOF_FOUND" => VerifyOutcome::NoProofFound,
            "INVALID_INPUT" => VerifyOutcome::InvalidInput,
            "UNSUPPORTED_FEATURE" => VerifyOutcome::UnsupportedFeature,
            "TIMEOUT" => VerifyOutcome::Timeout,
            "INCONSISTENT_PREMISES" => VerifyOutcome::InconsistentPremises,
            "PROVER_ERROR" => VerifyOutcome::ProverError,
            _ => VerifyOutcome::SystemError,
        }
    }

    /// Loose status string for echidnabot's existing GraphQL deserializer,
    /// which calls `parse_proof_status` and maps `"VERIFIED" | "PASS" |
    /// "SUCCESS"` → `Verified`, `"FAILED" | "FAIL"` → `Failed`, etc.
    pub fn loose_status(self) -> &'static str {
        match self {
            VerifyOutcome::Proved => "VERIFIED",
            VerifyOutcome::NoProofFound => "FAILED",
            VerifyOutcome::InvalidInput => "FAILED",
            VerifyOutcome::UnsupportedFeature => "ERROR",
            VerifyOutcome::Timeout => "TIMEOUT",
            VerifyOutcome::InconsistentPremises => "ERROR",
            VerifyOutcome::ProverError => "ERROR",
            VerifyOutcome::SystemError => "ERROR",
        }
    }
}

/// Result of the `verifyProof` mutation.
///
/// The `status`, `message`, `proverOutput`, `durationMs`, and `artifacts`
/// fields match echidnabot's existing client-side `VerifyProofData`. The
/// `outcome`, `mode`, and `smtStatus` fields surface the typed REST
/// taxonomy so future clients no longer need to round-trip via `/api/verify`
/// to disambiguate Timeout vs NoProofFound.
#[derive(Debug, Clone, SimpleObject)]
pub struct VerifyProofResult {
    /// Loose status string for backward compatibility with echidnabot's
    /// existing client (`"VERIFIED" | "FAILED" | "TIMEOUT" | "ERROR"`).
    pub status: String,
    /// Human-readable message.
    pub message: String,
    /// Captured stdout/stderr from the prover backend.
    pub prover_output: String,
    /// Wall-clock duration in milliseconds.
    pub duration_ms: u64,
    /// Output artifacts (proof certificates, intermediate files).
    pub artifacts: Vec<String>,
    /// Typed outcome — see `VerifyOutcome`.
    pub outcome: VerifyOutcome,
    /// Optional dispatch mode (e.g. `"smt-query"` for raw SMT-LIB).
    pub mode: Option<String>,
    /// Optional SMT solver status (`"sat" | "unsat" | "unknown"`).
    pub smt_status: Option<String>,
}

/// A single suggested tactic from the Julia ML coprocessor (or fallback).
///
/// Distinct from the existing `Tactic` SimpleObject (which is returned by
/// `suggestTacticsByProofId`) — that one carries `name`/`args`/`description`,
/// this one carries the rank-aware `tactic`/`confidence`/`explanation` shape
/// the echidnabot client expects.
#[derive(Debug, Clone, SimpleObject)]
pub struct SuggestedTactic {
    /// The tactic name (e.g. `"intro"`, `"apply foo"`).
    pub tactic: String,
    /// Confidence score from the ML coprocessor in `[0.0, 1.0]`.
    pub confidence: f64,
    /// Optional natural-language explanation for the suggestion.
    pub explanation: Option<String>,
}

/// Per-prover status, as returned by the `proverStatus` query.
///
/// Complements the existing `provers` list-query, which returns availability
/// for every prover. Use `proverStatus` when you only care about a single
/// prover and want to avoid the full list cost.
#[derive(Debug, Clone, SimpleObject)]
pub struct ProverStatusInfo {
    /// True when the prover backend is constructable and its executable
    /// is reachable.
    pub available: bool,
    /// Diagnostic message — version string when available, error text
    /// when not.
    pub message: Option<String>,
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
            .unwrap_or_else(|| 0);

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
                .unwrap_or_else(|| 0);

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

    /// Get suggested tactics for an existing proof session by ID.
    ///
    /// **Renamed 2026-06-01 (issue #180)**: this operation used to be
    /// exposed as `suggestTactics`. It was renamed to
    /// `suggestTacticsByProofId` to free the `suggestTactics` name for the
    /// new mutation that the echidnabot client expects (which takes
    /// `prover`/`context`/`goalState` and returns
    /// `[SuggestedTactic]`). Callers that were using the old
    /// `query { suggestTactics(proofId, limit) }` shape must update to
    /// `query { suggestTacticsByProofId(proofId, limit) }`.
    async fn suggest_tactics_by_proof_id(
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

    /// Per-prover availability/health.
    ///
    /// Added 2026-06-01 for issue #180. Complements the `provers`
    /// list-query for the common single-prover case. Backend construction
    /// + a `version()` probe is the strongest "available right now"
    /// signal we can give without actually dispatching a proof.
    async fn prover_status(&self, _ctx: &Context<'_>, prover: String) -> Result<ProverStatusInfo> {
        let core_kind = match CoreProverKind::from_str(&prover) {
            Ok(k) => k,
            Err(e) => {
                return Ok(ProverStatusInfo {
                    available: false,
                    message: Some(format!("Unknown prover '{}': {}", prover, e)),
                });
            },
        };

        let config = ProverConfig::default();
        let backend = match ProverFactory::create(core_kind, config) {
            Ok(b) => b,
            Err(e) => {
                return Ok(ProverStatusInfo {
                    available: false,
                    message: Some(format!("Failed to construct backend: {}", e)),
                });
            },
        };

        match backend.version().await {
            Ok(v) => Ok(ProverStatusInfo {
                available: true,
                message: Some(v),
            }),
            Err(e) => Ok(ProverStatusInfo {
                available: false,
                message: Some(format!("Version probe failed: {}", e)),
            }),
        }
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
            .unwrap_or_else(|| 0);

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
            .unwrap_or_else(|| 0);

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

    /// Synchronous one-shot proof verification.
    ///
    /// Added 2026-06-01 (issue #180). Matches the echidnabot client's
    /// `verifyProof(prover, content)` signature and returns the same
    /// fields the client already deserializes (`status`, `message`,
    /// `proverOutput`, `durationMs`, `artifacts`), plus the typed
    /// `outcome` / `mode` / `smtStatus` fields that surface the REST
    /// `/api/verify` taxonomy through GraphQL.
    ///
    /// `prover` is a free-form string parsed via `CoreProverKind::from_str`
    /// (same set of aliases as the REST handler). Unknown prover names
    /// produce a `SystemError` outcome rather than a GraphQL error so the
    /// client gets a structured response in every case.
    async fn verify_proof(
        &self,
        _ctx: &Context<'_>,
        prover: String,
        content: String,
    ) -> Result<VerifyProofResult> {
        let started = Instant::now();

        let core_kind = match CoreProverKind::from_str(&prover) {
            Ok(k) => k,
            Err(e) => {
                let duration_ms = started.elapsed().as_millis() as u64;
                return Ok(VerifyProofResult {
                    status: VerifyOutcome::SystemError.loose_status().to_string(),
                    message: format!("Unknown prover '{}': {}", prover, e),
                    prover_output: String::new(),
                    duration_ms,
                    artifacts: Vec::new(),
                    outcome: VerifyOutcome::SystemError,
                    mode: None,
                    smt_status: None,
                });
            },
        };

        let config = ProverConfig::default();
        let backend = match ProverFactory::create(core_kind, config) {
            Ok(b) => b,
            Err(e) => {
                let duration_ms = started.elapsed().as_millis() as u64;
                return Ok(VerifyProofResult {
                    status: VerifyOutcome::SystemError.loose_status().to_string(),
                    message: format!("Failed to construct backend: {}", e),
                    prover_output: String::new(),
                    duration_ms,
                    artifacts: Vec::new(),
                    outcome: VerifyOutcome::SystemError,
                    mode: None,
                    smt_status: None,
                });
            },
        };

        // Parse — failures map onto INVALID_INPUT, matching REST semantics.
        let state = match backend.parse_string(&content).await {
            Ok(s) => s,
            Err(_) => {
                let duration_ms = started.elapsed().as_millis() as u64;
                return Ok(VerifyProofResult {
                    status: VerifyOutcome::InvalidInput.loose_status().to_string(),
                    message: "Parse failed".to_string(),
                    prover_output: String::new(),
                    duration_ms,
                    artifacts: Vec::new(),
                    outcome: VerifyOutcome::InvalidInput,
                    mode: None,
                    smt_status: None,
                });
            },
        };

        match backend.verify_proof(&state).await {
            Ok(valid) => {
                let duration_ms = started.elapsed().as_millis() as u64;
                let outcome = if valid {
                    VerifyOutcome::Proved
                } else {
                    VerifyOutcome::NoProofFound
                };
                Ok(VerifyProofResult {
                    status: outcome.loose_status().to_string(),
                    message: if valid {
                        "Proof verified successfully".to_string()
                    } else {
                        "Proof verification failed".to_string()
                    },
                    prover_output: String::new(),
                    duration_ms,
                    artifacts: Vec::new(),
                    outcome,
                    mode: None,
                    smt_status: None,
                })
            },
            Err(e) => {
                let duration_ms = started.elapsed().as_millis() as u64;
                Ok(VerifyProofResult {
                    status: VerifyOutcome::ProverError.loose_status().to_string(),
                    message: format!("Verification error: {}", e),
                    prover_output: String::new(),
                    duration_ms,
                    artifacts: Vec::new(),
                    outcome: VerifyOutcome::ProverError,
                    mode: None,
                    smt_status: None,
                })
            },
        }
    }

    /// Request tactic suggestions for an ad-hoc goal, without a proof
    /// session.
    ///
    /// **Added 2026-06-01 (issue #180)**. Matches the echidnabot client's
    /// `suggestTactics(prover, context, goalState)` signature. The
    /// previous query named `suggestTactics(proofId, limit)` has been
    /// renamed to `suggestTacticsByProofId` (see that resolver's docstring).
    ///
    /// This is a mutation rather than a query because it can trigger
    /// expensive ML-coprocessor work, mirroring the client's contract.
    async fn suggest_tactics(
        &self,
        ctx: &Context<'_>,
        prover: String,
        context: String,
        goal_state: String,
    ) -> Result<Vec<SuggestedTactic>> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;
        let suggestions = echidna_ctx
            .suggest_tactics_for_goal(&prover, &context, &goal_state, 5)
            .await
            .map_err(|e| async_graphql::Error::new(e.to_string()))?;
        Ok(suggestions)
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

// =============================================================================
// Tests for the operations added/renamed for echidnabot ↔ echidna seam (#180).
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolvers::EchidnaContext;
    use async_graphql::{EmptySubscription, Request, Schema, Value};

    fn build_schema() -> Schema<QueryRoot, MutationRoot, EmptySubscription> {
        Schema::build(QueryRoot, MutationRoot, EmptySubscription)
            .data(EchidnaContext::new())
            .finish()
    }

    /// `verify_outcome_from_rest_str` round-trip — every taxon the REST
    /// `/api/verify` handler emits must map onto a distinct enum variant.
    #[test]
    fn verify_outcome_from_rest_str_covers_taxonomy() {
        assert_eq!(
            VerifyOutcome::from_rest_str("PROVED"),
            VerifyOutcome::Proved
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("NO_PROOF_FOUND"),
            VerifyOutcome::NoProofFound
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("INVALID_INPUT"),
            VerifyOutcome::InvalidInput
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("UNSUPPORTED_FEATURE"),
            VerifyOutcome::UnsupportedFeature
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("TIMEOUT"),
            VerifyOutcome::Timeout
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("INCONSISTENT_PREMISES"),
            VerifyOutcome::InconsistentPremises
        );
        assert_eq!(
            VerifyOutcome::from_rest_str("PROVER_ERROR"),
            VerifyOutcome::ProverError
        );
        // Unknown / non-canonical falls through to SystemError.
        assert_eq!(
            VerifyOutcome::from_rest_str("WAT"),
            VerifyOutcome::SystemError
        );
        assert_eq!(VerifyOutcome::from_rest_str(""), VerifyOutcome::SystemError);
    }

    /// `loose_status` covers the four labels echidnabot's existing
    /// `parse_proof_status` already maps onto `ProofStatus`.
    #[test]
    fn verify_outcome_loose_status_matches_client() {
        assert_eq!(VerifyOutcome::Proved.loose_status(), "VERIFIED");
        assert_eq!(VerifyOutcome::NoProofFound.loose_status(), "FAILED");
        assert_eq!(VerifyOutcome::Timeout.loose_status(), "TIMEOUT");
        assert_eq!(VerifyOutcome::ProverError.loose_status(), "ERROR");
    }

    /// `verifyProof` mutation — unknown prover names return a structured
    /// `SystemError` outcome rather than a GraphQL error, so the client
    /// always gets the contract-shaped response.
    #[tokio::test]
    async fn verify_proof_mutation_unknown_prover_returns_system_error() {
        let schema = build_schema();
        let query = r#"
            mutation {
                verifyProof(prover: "definitely-not-a-prover", content: "x") {
                    status
                    outcome
                    message
                    durationMs
                    artifacts
                    mode
                    smtStatus
                }
            }
        "#;
        let resp = schema.execute(Request::new(query)).await;
        assert!(resp.errors.is_empty(), "errors: {:?}", resp.errors);

        let data = match resp.data {
            Value::Object(ref m) => m,
            other => panic!("expected object, got {:?}", other),
        };
        let vp = match data.get("verifyProof").expect("verifyProof field") {
            Value::Object(m) => m,
            other => panic!("expected object, got {:?}", other),
        };

        assert_eq!(vp.get("status"), Some(&Value::String("ERROR".to_string())));
        match vp.get("outcome") {
            Some(Value::Enum(name)) => assert_eq!(name.as_str(), "SYSTEM_ERROR"),
            other => panic!("expected enum SYSTEM_ERROR, got {:?}", other),
        }
        // mode/smtStatus should be null on this error path.
        assert!(matches!(vp.get("mode"), Some(Value::Null)));
        assert!(matches!(vp.get("smtStatus"), Some(Value::Null)));
        // artifacts is an empty list, not null.
        assert!(matches!(vp.get("artifacts"), Some(Value::List(v)) if v.is_empty()));
    }

    /// `proverStatus` query — same SystemError-shape behaviour for an
    /// unknown prover string (available: false, message populated).
    #[tokio::test]
    async fn prover_status_unknown_prover_reports_unavailable() {
        let schema = build_schema();
        let query = r#"
            query {
                proverStatus(prover: "no-such-prover") {
                    available
                    message
                }
            }
        "#;
        let resp = schema.execute(Request::new(query)).await;
        assert!(resp.errors.is_empty(), "errors: {:?}", resp.errors);

        let data = match resp.data {
            Value::Object(ref m) => m,
            other => panic!("expected object, got {:?}", other),
        };
        let ps = match data.get("proverStatus").expect("proverStatus field") {
            Value::Object(m) => m,
            other => panic!("expected object, got {:?}", other),
        };
        assert_eq!(ps.get("available"), Some(&Value::Boolean(false)));
        match ps.get("message") {
            Some(Value::String(msg)) => assert!(
                msg.contains("Unknown prover"),
                "message should mention unknown prover, got: {}",
                msg
            ),
            other => panic!("expected non-null message, got {:?}", other),
        }
    }

    /// `suggestTactics(prover, context, goalState)` mutation — same
    /// SystemError path for unknown provers: the call fails *before*
    /// dialing the ML coprocessor, so the response shape stays
    /// `errors`-populated (a GraphQL error is acceptable here because
    /// the client expects `[SuggestedTactic!]!`, a non-null list, and
    /// has no field to encode "unknown prover").
    #[tokio::test]
    async fn suggest_tactics_mutation_unknown_prover_errors() {
        let schema = build_schema();
        let query = r#"
            mutation {
                suggestTactics(prover: "no-such-prover", context: "", goalState: "x") {
                    tactic
                    confidence
                    explanation
                }
            }
        "#;
        let resp = schema.execute(Request::new(query)).await;
        // Unknown prover -> resolver Err -> top-level GraphQL error.
        assert!(
            !resp.errors.is_empty(),
            "expected an error for unknown prover"
        );
        assert!(resp.errors[0].message.contains("Unknown prover"));
    }

    /// `suggestTactics(prover, context, goalState)` is a *mutation*, not
    /// a query — guard against accidental kind drift (the rename trick
    /// only works if the new operation lives on MutationRoot, freeing
    /// the QueryRoot name).
    #[tokio::test]
    async fn suggest_tactics_is_a_mutation() {
        let schema = build_schema();
        // Same name, but issued as a *query* — must fail with "Unknown
        // field" because the query root no longer exposes it.
        let query = r#"
            query {
                suggestTactics(prover: "coq", context: "", goalState: "x") {
                    tactic
                }
            }
        "#;
        let resp = schema.execute(Request::new(query)).await;
        assert!(
            !resp.errors.is_empty(),
            "suggestTactics on QueryRoot must not resolve"
        );
    }

    /// `suggestTacticsByProofId` — the renamed legacy query — must
    /// continue to exist on QueryRoot so callers can update their
    /// schema with a pure name change.
    #[tokio::test]
    async fn suggest_tactics_by_proof_id_is_a_query() {
        let schema = build_schema();
        // Missing session ID, so we expect an error from the resolver
        // body (not a "field not found" error) — that's how we know
        // the field is registered.
        let query = r#"
            query {
                suggestTacticsByProofId(proofId: "no-such-session", limit: 1) {
                    name
                }
            }
        "#;
        let resp = schema.execute(Request::new(query)).await;
        assert!(!resp.errors.is_empty());
        let msg = &resp.errors[0].message;
        assert!(
            msg.contains("Session not found") || msg.contains("session"),
            "expected a session-not-found error from the resolver, got: {}",
            msg
        );
    }

    /// Schema introspection — all three new operations must show up
    /// under the right roots with the expected argument names. This is
    /// the "contract assertion" the issue body asked for.
    #[tokio::test]
    async fn introspection_exposes_all_three_new_operations() {
        let schema = build_schema();

        // Mutations: verifyProof + suggestTactics (new shape).
        let q = r#"
            {
                __type(name: "MutationRoot") {
                    fields {
                        name
                        args { name type { name kind ofType { name kind } } }
                    }
                }
            }
        "#;
        let resp = schema.execute(Request::new(q)).await;
        assert!(
            resp.errors.is_empty(),
            "introspection errors: {:?}",
            resp.errors
        );
        let body = serde_json::to_string(&resp.data).unwrap();
        assert!(
            body.contains("\"verifyProof\""),
            "missing verifyProof mutation"
        );
        assert!(
            body.contains("\"suggestTactics\""),
            "missing new suggestTactics mutation"
        );
        // verifyProof must take (prover, content); suggestTactics must
        // take (prover, context, goalState).
        assert!(body.contains("\"prover\""));
        assert!(body.contains("\"content\""));
        assert!(body.contains("\"context\""));
        assert!(body.contains("\"goalState\""));

        // Queries: proverStatus + suggestTacticsByProofId.
        let q = r#"
            {
                __type(name: "QueryRoot") {
                    fields { name args { name } }
                }
            }
        "#;
        let resp = schema.execute(Request::new(q)).await;
        assert!(resp.errors.is_empty());
        let body = serde_json::to_string(&resp.data).unwrap();
        assert!(
            body.contains("\"proverStatus\""),
            "missing proverStatus query"
        );
        assert!(
            body.contains("\"suggestTacticsByProofId\""),
            "missing renamed suggestTacticsByProofId query"
        );
        // The query-side `suggestTactics` (old name) must NOT exist on QueryRoot.
        // Crude but sufficient: assert that the literal `"name":"suggestTactics"`
        // pair does not appear among the QueryRoot fields (it would otherwise
        // shadow the new mutation by introspection ambiguity).
        assert!(
            !body.contains("\"name\":\"suggestTactics\""),
            "old suggestTactics query must be renamed away from QueryRoot"
        );
    }
}
