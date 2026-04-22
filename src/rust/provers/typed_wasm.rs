// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

#![allow(dead_code)]

//! TypedWasm prover oracle adapter.
//!
//! The pure parse/analyse engine lives in the standalone `typed-wasm` crate
//! at `crates/typed_wasm`. This file is the echidna-side adapter: it wraps
//! the engine, maps [`typed_wasm::Analysis`] onto echidna's core types
//! (`ProofState`, `Goal`, …), and exposes the backend to the prover factory.
//!
//! Discipline routing — S3 extraction (2026-04-22):
//!   The engine is parametrised by a [`typed_wasm::TypeInfo`]. `TypedWasmBackend`
//!   carries a [`ProverKind`] and a [`TypeInfo`], so the 39 `*TypeChecker`
//!   variants (`LinearTypeChecker`, `AffineTypeChecker`, `ModalTypeChecker`,
//!   `TemporalTypeChecker`, `RefinementTypeChecker`, `DependentTypeChecker`,
//!   `SessionTypeChecker`, …) all route through one backend with
//!   discipline-specific active-level sets, replacing the catch-all
//!   `HPEcosystemBackend` route previously used for them.

use anyhow::{Context, Result};
use async_trait::async_trait;
use std::collections::HashMap;
use std::path::PathBuf;
use tokio::sync::Mutex;

use crate::core::{
    Context as ProofContext, Definition, Goal, Hypothesis, ProofState, Tactic, TacticResult, Term,
    Theorem,
};
use crate::provers::{ProverBackend, ProverConfig, ProverKind};

pub use typed_wasm::{
    analyse, generate_proof_obligations, parse_twasm, parse_wasm_type, Analysis, Field,
    LevelProof, SafetyLevel, Schema, TwasmInstruction, TypeInfo, WasmType,
};

// ---------------------------------------------------------------------------
// Discipline → TypeInfo mapping
// ---------------------------------------------------------------------------

/// Map a [`ProverKind`] to the [`TypeInfo`] that configures the engine for
/// that discipline. Disciplines enforce a subset of the 10 safety levels;
/// every discipline implicitly enforces Level 1 (InstructionValidity).
///
/// For `TypedWasm` itself, this returns [`TypeInfo::full`] — the original
/// 10-level oracle behaviour. For any non-discipline kind, the full set is
/// returned as a safe default.
pub fn type_info_for(kind: ProverKind) -> TypeInfo {
    use SafetyLevel::*;

    // Baseline: every discipline cares about parsing, field-binding,
    // type-compatibility, and statically-known result types.
    let base = [RegionBinding, TypeCompatible, ResultType];

    let (name, extra): (&str, Vec<SafetyLevel>) = match kind {
        // Substructural family
        ProverKind::LinearTypeChecker => ("linear", vec![AliasSafe, Linear]),
        ProverKind::AffineTypeChecker => ("affine", vec![AliasSafe]),
        ProverKind::RelevantTypeChecker => ("relevant", vec![AliasSafe]),
        ProverKind::OrderedTypeChecker => ("ordered", vec![AliasSafe]),
        ProverKind::UniquenessTypeChecker => ("uniqueness", vec![AliasSafe, Linear]),
        ProverKind::QTTTypeChecker => ("qtt", vec![AliasSafe, Linear]),

        // Modal / temporal / provability
        ProverKind::ModalTypeChecker => ("modal", vec![EffectSafe]),
        ProverKind::EpistemicTypeChecker => ("epistemic", vec![EffectSafe]),
        ProverKind::TemporalTypeChecker => ("temporal", vec![LifetimeSafe]),
        ProverKind::ProvabilityTypeChecker => ("provability", vec![]),

        // Effect / coeffect
        ProverKind::EffectRowTypeChecker => ("effect-row", vec![EffectSafe]),
        ProverKind::ImpureTypeChecker => ("impure", vec![EffectSafe]),
        ProverKind::CoeffectTypeChecker => ("coeffect", vec![EffectSafe]),
        ProverKind::ProbabilisticTypeChecker => ("probabilistic", vec![EffectSafe]),

        // Dependent / refinement
        ProverKind::DependentTypeChecker => ("dependent", vec![]),
        ProverKind::RefinementTypeChecker => ("refinement", vec![BoundsProof]),
        ProverKind::HoareTypeChecker => ("hoare", vec![BoundsProof]),
        ProverKind::IndexedTypeChecker => ("indexed", vec![BoundsProof]),

        // Polymorphism / foundations
        ProverKind::OrdinaryTypeChecker => ("ordinary", vec![]),
        ProverKind::PhantomTypeChecker => ("phantom", vec![]),
        ProverKind::PolymorphicTypeChecker => ("polymorphic", vec![]),
        ProverKind::ExistentialTypeChecker => ("existential", vec![]),
        ProverKind::HigherKindedTypeChecker => ("higher-kinded", vec![]),
        ProverKind::RowTypeChecker => ("row", vec![]),

        // Subtyping
        ProverKind::SubtypingTypeChecker => ("subtyping", vec![]),
        ProverKind::IntersectionTypeChecker => ("intersection", vec![]),
        ProverKind::UnionTypeChecker => ("union", vec![]),
        ProverKind::GradualTypeChecker => ("gradual", vec![NullSafe]),

        // Mutability / capability
        ProverKind::ImmutableTypeChecker => ("immutable", vec![AliasSafe]),
        ProverKind::CapabilityTypeChecker => ("capability", vec![AliasSafe, EffectSafe]),
        ProverKind::BunchedTypeChecker => ("bunched", vec![AliasSafe]),

        // Process / communication
        ProverKind::SessionTypeChecker => ("session", vec![AliasSafe, Linear]),
        ProverKind::DyadicTypeChecker => ("dyadic", vec![AliasSafe]),
        ProverKind::ChoreographicTypeChecker => ("choreographic", vec![EffectSafe]),
        ProverKind::EchoTypeChecker => ("echo", vec![EffectSafe]),

        // Homotopy / cubical
        ProverKind::HomotopyTypeChecker => ("homotopy", vec![]),
        ProverKind::CubicalTypeChecker => ("cubical", vec![]),

        // Tropical
        ProverKind::TropicalTypeChecker => ("tropical", vec![]),

        // Nominal
        ProverKind::NominalTypeChecker => ("nominal", vec![LifetimeSafe]),

        // TypedWasm itself and anything else falls back to the full engine.
        _ => return TypeInfo::full(),
    };

    let mut levels: Vec<SafetyLevel> = base.to_vec();
    levels.extend(extra);
    TypeInfo::with_levels(name, levels)
}

// ---------------------------------------------------------------------------
// Backend
// ---------------------------------------------------------------------------

/// TypedWasm prover oracle backend — thin adapter over the pure
/// [`typed_wasm`] engine.
pub struct TypedWasmBackend {
    /// Which discipline this instance serves — drives `.kind()` and the
    /// default [`TypeInfo`]. For the legacy `TypedWasm` oracle, this is
    /// [`ProverKind::TypedWasm`]; for dispatched discipline instances,
    /// this is the specific `*TypeChecker` variant.
    kind: ProverKind,
    /// Engine configuration (which levels are active, discipline name).
    type_info: TypeInfo,
    /// Echidna prover configuration (executable path, args, …).
    config: ProverConfig,
    /// Monotonic counter for generating fresh meta-variable identifiers.
    meta_counter: Mutex<usize>,
}

impl TypedWasmBackend {
    /// Legacy constructor — defaults to the full 10-level oracle and
    /// [`ProverKind::TypedWasm`]. Preserved so existing call sites compile.
    pub fn new(config: ProverConfig) -> Self {
        TypedWasmBackend {
            kind: ProverKind::TypedWasm,
            type_info: TypeInfo::full(),
            config,
            meta_counter: Mutex::new(0),
        }
    }

    /// Construct a backend parametrised by an explicit [`TypeInfo`].
    /// `kind` records which discipline this instance serves so that
    /// `.kind()` reports the right `ProverKind` back to the dispatcher.
    pub fn with_type_info(kind: ProverKind, config: ProverConfig, type_info: TypeInfo) -> Self {
        TypedWasmBackend {
            kind,
            type_info,
            config,
            meta_counter: Mutex::new(0),
        }
    }

    /// Convenience: build a backend by resolving [`type_info_for`] at the
    /// given kind. This is what the prover factory uses when dispatching
    /// a `*TypeChecker` variant.
    pub fn for_kind(kind: ProverKind, config: ProverConfig) -> Self {
        let type_info = type_info_for(kind);
        TypedWasmBackend::with_type_info(kind, config, type_info)
    }

    fn run(&self, content: &str) -> Result<Analysis> {
        analyse(content, &self.type_info)
    }

    fn obligation_to_goal(&self, obligation: &LevelProof) -> Goal {
        let level = obligation.level.level();
        let label = obligation.level.label();

        let target = Term::App {
            func: Box::new(Term::Const(format!("TypedWasm.Level{}", level))),
            args: vec![Term::Const(obligation.description.clone())],
        };

        let mut hypotheses = Vec::new();
        if let Some(ref witness) = obligation.witness {
            hypotheses.push(Hypothesis {
                name: format!("{}_witness", label),
                ty: Term::Const(format!("Witness({})", witness)),
                body: None,
                type_info: None,
            });
        }

        Goal {
            id: format!(
                "twasm[{}]_L{}_{}_line{}",
                self.type_info.discipline, level, label, obligation.source_line
            ),
            target,
            hypotheses,
        }
    }

    fn analysis_to_proof_state(&self, analysis: &Analysis) -> ProofState {
        let goals: Vec<Goal> = analysis
            .obligations
            .iter()
            .map(|o| self.obligation_to_goal(o))
            .collect();

        let mut context = ProofContext::default();

        for instr in &analysis.instructions {
            if let TwasmInstruction::RegionDef(schema) = instr {
                let fields_term = Term::App {
                    func: Box::new(Term::Const("Schema".to_string())),
                    args: schema
                        .fields
                        .iter()
                        .map(|f| Term::App {
                            func: Box::new(Term::Const("Field".to_string())),
                            args: vec![Term::Const(f.name.clone()), Term::Const(f.ty.to_string())],
                        })
                        .collect(),
                };

                context.definitions.push(Definition {
                    name: format!("region_{}", schema.name),
                    ty: Term::Const("Schema".to_string()),
                    body: fields_term,
                    type_info: None,
                });
            }
        }

        let mut theorems = Vec::new();
        for obligation in &analysis.obligations {
            if obligation.verified {
                theorems.push(Theorem {
                    name: format!("L{}_{}", obligation.level.level(), obligation.level.label()),
                    statement: Term::Const(obligation.description.clone()),
                    proof: Some(vec![Tactic::Reflexivity]),
                    aspects: vec![
                        "typed-wasm".to_string(),
                        format!("discipline-{}", analysis.type_info.discipline),
                        format!("level-{}", obligation.level.level()),
                    ],
                });
            }
        }
        context.theorems = theorems;

        let mut metadata = HashMap::new();
        let total = analysis.obligations.len();
        let verified = analysis.obligations.iter().filter(|o| o.verified).count();
        let failed = total - verified;
        metadata.insert(
            "twasm_discipline".to_string(),
            serde_json::Value::String(analysis.type_info.discipline.clone()),
        );
        metadata.insert(
            "twasm_total_obligations".to_string(),
            serde_json::Value::Number(serde_json::Number::from(total)),
        );
        metadata.insert(
            "twasm_verified".to_string(),
            serde_json::Value::Number(serde_json::Number::from(verified)),
        );
        metadata.insert(
            "twasm_failed".to_string(),
            serde_json::Value::Number(serde_json::Number::from(failed)),
        );
        metadata.insert(
            "twasm_all_levels_satisfied".to_string(),
            serde_json::Value::Bool(failed == 0),
        );

        let mut level_summary = serde_json::Map::new();
        for level in SafetyLevel::all() {
            if !analysis.type_info.active_levels.contains(&level) {
                continue;
            }
            let level_obligations: Vec<&LevelProof> = analysis
                .obligations
                .iter()
                .filter(|o| o.level == level)
                .collect();
            let level_verified = level_obligations.iter().filter(|o| o.verified).count();
            let level_total = level_obligations.len();
            level_summary.insert(
                format!("L{}_{}", level.level(), level.label()),
                serde_json::Value::String(format!("{}/{}", level_verified, level_total)),
            );
        }
        metadata.insert(
            "twasm_level_breakdown".to_string(),
            serde_json::Value::Object(level_summary),
        );

        ProofState {
            goals,
            context,
            proof_script: Vec::new(),
            metadata,
        }
    }

    async fn fresh_meta(&self) -> usize {
        let mut counter = self.meta_counter.lock().await;
        let id = *counter;
        *counter += 1;
        id
    }
}

// ---------------------------------------------------------------------------
// ProverBackend trait implementation
// ---------------------------------------------------------------------------

#[async_trait]
impl ProverBackend for TypedWasmBackend {
    fn kind(&self) -> ProverKind {
        self.kind
    }

    async fn version(&self) -> Result<String> {
        Ok(format!(
            "typed-wasm-oracle 1.0.0 [{}] (ECHIDNA built-in)",
            self.type_info.discipline
        ))
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .context("Failed to read .twasm file")?;
        self.parse_string(&content).await
    }

    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let analysis = self.run(content)?;
        Ok(self.analysis_to_proof_state(&analysis))
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        match tactic {
            Tactic::Reflexivity | Tactic::Assumption => {
                let remaining: Vec<Goal> = state
                    .goals
                    .iter()
                    .filter(|g| g.hypotheses.is_empty())
                    .cloned()
                    .collect();
                let mut new_state = state.clone();
                new_state.goals = remaining;
                Ok(TacticResult::Success(new_state))
            },
            Tactic::Custom {
                prover, command, ..
            } if prover == "typed_wasm" && command == "auto" => {
                let mut new_state = state.clone();
                new_state.goals = Vec::new();
                Ok(TacticResult::Success(new_state))
            },
            _ => Ok(TacticResult::Error(format!(
                "Tactic {:?} not applicable to TypedWasm oracle proofs",
                tactic
            ))),
        }
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let all_satisfied = state
            .metadata
            .get("twasm_all_levels_satisfied")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);

        if !all_satisfied {
            return Ok(false);
        }

        let all_witnessed = state.goals.iter().all(|g| !g.hypotheses.is_empty());
        Ok(all_witnessed)
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let mut output = String::new();
        output.push_str(";; TypedWasm Proof Certificate\n");
        output.push_str(";; Generated by ECHIDNA TypedWasm Oracle\n");
        if let Some(d) = state.metadata.get("twasm_discipline") {
            output.push_str(&format!(";; Discipline: {}\n", d));
        }
        output.push('\n');

        if let Some(total) = state.metadata.get("twasm_total_obligations") {
            output.push_str(&format!(";; Total obligations: {}\n", total));
        }
        if let Some(verified) = state.metadata.get("twasm_verified") {
            output.push_str(&format!(";; Verified: {}\n", verified));
        }
        if let Some(failed) = state.metadata.get("twasm_failed") {
            output.push_str(&format!(";; Failed: {}\n", failed));
        }
        output.push('\n');

        if let Some(breakdown) = state.metadata.get("twasm_level_breakdown") {
            output.push_str(";; Level breakdown:\n");
            if let Some(obj) = breakdown.as_object() {
                for (level_key, status) in obj {
                    output.push_str(&format!(";;   {}: {}\n", level_key, status));
                }
            }
        }
        output.push('\n');

        for goal in &state.goals {
            output.push_str(&format!(
                "(obligation \"{}\" {})\n",
                goal.id,
                if goal.hypotheses.is_empty() {
                    "UNRESOLVED"
                } else {
                    "DISCHARGED"
                }
            ));
        }

        Ok(output)
    }

    async fn suggest_tactics(&self, state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        let mut suggestions = Vec::new();
        let has_witnessed = state.goals.iter().any(|g| !g.hypotheses.is_empty());
        if has_witnessed {
            suggestions.push(Tactic::Reflexivity);
            suggestions.push(Tactic::Assumption);
        }
        suggestions.push(Tactic::Custom {
            prover: "typed_wasm".to_string(),
            command: "auto".to_string(),
            args: vec![],
        });
        Ok(suggestions)
    }

    async fn search_theorems(&self, pattern: &str) -> Result<Vec<String>> {
        let pattern_lower = pattern.to_lowercase();
        let results: Vec<String> = SafetyLevel::all()
            .iter()
            .filter(|level| self.type_info.active_levels.contains(level))
            .filter(|level| level.label().to_lowercase().contains(&pattern_lower))
            .map(|level| {
                format!(
                    "TypedWasm.Level{}: {} (level {}, discipline {})",
                    level.level(),
                    level.label(),
                    level.level(),
                    self.type_info.discipline
                )
            })
            .collect();
        Ok(results)
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }

    fn prove(&self, goal: &crate::core::Goal) -> Result<ProofState> {
        Ok(ProofState {
            goals: vec![goal.clone()],
            context: ProofContext::default(),
            proof_script: vec![],
            metadata: HashMap::new(),
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const VALID_TWASM: &str = r#"
region Particles { x: f32; y: f32; mass: f64 } [1024]
effect Particles { read; write }
region.get Particles[0] .x
region.get Particles[512] .mass
region.set Particles .y, 3.14
linear.acquire Particles
linear.release Particles
"#;

    const BAD_FIELD_TWASM: &str = r#"
region Foo { bar: i32 } [10]
region.get Foo[0] .nonexistent
"#;

    #[tokio::test]
    async fn test_backend_parse_string() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        assert!(!state.goals.is_empty());
        assert!(!state.context.definitions.is_empty());
        let all_satisfied = state
            .metadata
            .get("twasm_all_levels_satisfied")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        assert!(all_satisfied);
    }

    #[tokio::test]
    async fn test_backend_verify_valid() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        assert!(backend.verify_proof(&state).await.unwrap());
    }

    #[tokio::test]
    async fn test_backend_verify_invalid() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let state = backend.parse_string(BAD_FIELD_TWASM).await.unwrap();
        assert!(!backend.verify_proof(&state).await.unwrap());
    }

    #[tokio::test]
    async fn test_backend_export() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        let exported = backend.export(&state).await.unwrap();
        assert!(exported.contains("TypedWasm Proof Certificate"));
        assert!(exported.contains("DISCHARGED"));
    }

    #[tokio::test]
    async fn test_backend_suggest_tactics() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        let tactics = backend.suggest_tactics(&state, 5).await.unwrap();
        assert!(!tactics.is_empty());
    }

    #[tokio::test]
    async fn test_search_theorems() {
        let backend = TypedWasmBackend::new(ProverConfig::default());
        let results = backend.search_theorems("linear").await.unwrap();
        assert!(!results.is_empty());
        assert!(results[0].contains("Linear"));
    }

    #[tokio::test]
    async fn test_kind_reflects_dispatched_variant() {
        let backend = TypedWasmBackend::for_kind(
            ProverKind::LinearTypeChecker,
            ProverConfig::default(),
        );
        assert_eq!(backend.kind(), ProverKind::LinearTypeChecker);
        assert_eq!(backend.type_info.discipline, "linear");
    }

    #[tokio::test]
    async fn test_linear_discipline_filters_bounds() {
        let backend = TypedWasmBackend::for_kind(
            ProverKind::LinearTypeChecker,
            ProverConfig::default(),
        );
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        // Linear discipline doesn't include BoundsProof — so no goal IDs
        // mentioning BoundsProof should be present.
        let has_bounds = state
            .goals
            .iter()
            .any(|g| g.id.contains("BoundsProof"));
        assert!(!has_bounds, "linear discipline should not emit BoundsProof goals");
    }

    #[tokio::test]
    async fn test_refinement_discipline_includes_bounds() {
        let backend = TypedWasmBackend::for_kind(
            ProverKind::RefinementTypeChecker,
            ProverConfig::default(),
        );
        let state = backend.parse_string(VALID_TWASM).await.unwrap();
        let has_bounds = state
            .goals
            .iter()
            .any(|g| g.id.contains("BoundsProof"));
        assert!(has_bounds, "refinement discipline should emit BoundsProof goals");
    }

    #[test]
    fn test_type_info_for_unknown_returns_full() {
        let ti = type_info_for(ProverKind::Z3);
        assert_eq!(ti.discipline, "typed-wasm");
        assert_eq!(ti.active_levels.len(), 10);
    }
}
