// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL schema definitions - wired to ECHIDNA core

use async_graphql::{Context, Object, Result, SimpleObject, Enum};
use echidna::provers::ProverKind as CoreProverKind;
use echidna::core::{Tactic as CoreTactic, TacticResult as CoreTacticResult, Term};

use crate::resolvers::EchidnaContext;

/// Supported theorem provers in ECHIDNA
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProverKind {
    Agda, Coq, Lean, Isabelle, Z3, CVC5,
    Metamath, HOLLight, Mizar,
    PVS, ACL2, HOL4, Idris2,
    Vampire, EProver, SPASS, AltErgo,
    FStar, Dafny, Why3,
    TLAPS, Twelf, Nuprl, Minlog, Imandra,
    GLPK, SCIP, MiniZinc, Chuffed, ORTools,
}

/// Status of a proof attempt
#[derive(Debug, Clone, Copy, Enum, Eq, PartialEq)]
pub enum ProofStatus {
    Pending, InProgress, Success, Failed, Timeout, Error,
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
    async fn list_proofs(&self, ctx: &Context<'_>, limit: Option<i32>, _status: Option<ProofStatus>) -> Result<Vec<ProofState>> {
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
    async fn suggest_tactics(&self, ctx: &Context<'_>, proof_id: String, limit: Option<i32>) -> Result<Vec<Tactic>> {
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
    async fn submit_proof(&self, ctx: &Context<'_>, goal: String, prover: ProverKind) -> Result<ProofState> {
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
    async fn apply_tactic(&self, ctx: &Context<'_>, proof_id: String, tactic: String, args: Vec<String>) -> Result<ProofState> {
        let echidna_ctx = ctx.data::<EchidnaContext>()?;

        let core_tactic = parse_tactic(&tactic, &args);

        let result = echidna_ctx
            .apply_tactic(&proof_id, core_tactic)
            .await
            .map_err(|e| async_graphql::Error::new(e.to_string()))?;

        // Fetch updated state
        let sessions = echidna_ctx.sessions.read().await;
        let session_arc = sessions.get(&proof_id)
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
    }
}
