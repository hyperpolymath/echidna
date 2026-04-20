// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Unified HP type-checker ecosystem backend.
//!
//! The HP stack ships forty type-discipline "provers" that are really
//! views on three upstream projects. Two are named entry points and the
//! remainder are discipline flags passed to `typell`:
//!
//! | Upstream                                          | CLI                     |
//! |---------------------------------------------------|-------------------------|
//! | `developer-ecosystem/katagoria`                   | `katagoria`             |
//! | `verification-ecosystem/tropical-resource-typing` | `tropical-type-check`   |
//! | `verification-ecosystem/typell` (all others)      | `typell --discipline=X` |
//!
//! The forty disciplines, grouped by family (see `src/rust/disciplines/`
//! for authoritative taxonomy):
//!
//! - **Entry points**: TypeLL, KatagoriaVerifier, TropicalTypeChecker
//! - **Foundations**: Ordinary
//! - **Polymorphism**: Phantom, Polymorphic, Existential, HigherKinded, Row
//! - **Subtyping**: Subtyping, Intersection, Union, Gradual
//! - **Dependent/refinement**: Dependent, Refinement, Hoare, Indexed
//! - **Substructural**: QTT, Linear, Affine, Relevant, Ordered, Uniqueness
//! - **Mutability/capability**: Immutable, Capability, Bunched
//! - **Modal**: Modal, Epistemic, Temporal, Provability
//! - **Effects/coeffects**: EffectRow, Impure, Coeffect, Probabilistic
//! - **Process/communication**: Session, Choreographic, Dyadic, Echo
//! - **Homotopy**: Homotopy, Cubical
//!
//! Rather than maintain forty shell-out wrappers, this single backend
//! dispatches on its `ProverKind` at method boundaries and injects the
//! right discipline flag when it shells out to the underlying tool.
//!
//! All forty ProverKind variants register through
//! `ProverFactory::create` -> `HPEcosystemBackend::new`.

#![allow(dead_code)]

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use std::path::PathBuf;
use std::process::Stdio;
use tokio::process::Command;

use super::{ProverBackend, ProverConfig, ProverKind};
use crate::core::{Goal, ProofState, Tactic, TacticResult, Term};

/// Unified HP-ecosystem backend.
pub struct HPEcosystemBackend {
    kind: ProverKind,
    config: ProverConfig,
}

impl HPEcosystemBackend {
    pub fn new(kind: ProverKind, config: ProverConfig) -> Self {
        HPEcosystemBackend { kind, config }
    }

    /// Which upstream project this discipline lives in. Returns the CLI
    /// name that should be invoked and the `--discipline` string that
    /// selects the specific type-checking mode.
    fn upstream(&self) -> (&'static str, &'static str) {
        match self.kind {
            ProverKind::TypeLL => ("typell", "typell"),
            ProverKind::KatagoriaVerifier => ("katagoria", "verify"),
            ProverKind::TropicalTypeChecker => ("tropical-type-check", "tropical"),
            ProverKind::ChoreographicTypeChecker => ("typell", "choreographic"),
            ProverKind::EpistemicTypeChecker => ("typell", "epistemic"),
            ProverKind::EchoTypeChecker => ("typell", "echo"),
            ProverKind::SessionTypeChecker => ("typell", "session"),
            ProverKind::ModalTypeChecker => ("typell", "modal"),
            ProverKind::QTTTypeChecker => ("typell", "qtt"),
            ProverKind::EffectRowTypeChecker => ("typell", "effect-row"),
            ProverKind::DependentTypeChecker => ("typell", "dependent"),
            ProverKind::RefinementTypeChecker => ("typell", "refinement"),
            // Foundations
            ProverKind::OrdinaryTypeChecker => ("typell", "ordinary"),
            // Polymorphism family
            ProverKind::PhantomTypeChecker => ("typell", "phantom"),
            ProverKind::PolymorphicTypeChecker => ("typell", "polymorphic"),
            ProverKind::ExistentialTypeChecker => ("typell", "existential"),
            ProverKind::HigherKindedTypeChecker => ("typell", "higher-kinded"),
            ProverKind::RowTypeChecker => ("typell", "row"),
            // Subtyping family
            ProverKind::SubtypingTypeChecker => ("typell", "subtyping"),
            ProverKind::IntersectionTypeChecker => ("typell", "intersection"),
            ProverKind::UnionTypeChecker => ("typell", "union"),
            ProverKind::GradualTypeChecker => ("typell", "gradual"),
            // Dependent / refinement family
            ProverKind::HoareTypeChecker => ("typell", "hoare"),
            ProverKind::IndexedTypeChecker => ("typell", "indexed"),
            // Substructural family
            ProverKind::LinearTypeChecker => ("typell", "linear"),
            ProverKind::AffineTypeChecker => ("typell", "affine"),
            ProverKind::RelevantTypeChecker => ("typell", "relevant"),
            ProverKind::OrderedTypeChecker => ("typell", "ordered"),
            ProverKind::UniquenessTypeChecker => ("typell", "uniqueness"),
            // Mutability / capability family
            ProverKind::ImmutableTypeChecker => ("typell", "immutable"),
            ProverKind::CapabilityTypeChecker => ("typell", "capability"),
            ProverKind::BunchedTypeChecker => ("typell", "bunched"),
            // Modal family
            ProverKind::TemporalTypeChecker => ("typell", "temporal"),
            ProverKind::ProvabilityTypeChecker => ("typell", "provability"),
            // Effects / coeffects family
            ProverKind::ImpureTypeChecker => ("typell", "impure"),
            ProverKind::CoeffectTypeChecker => ("typell", "coeffect"),
            ProverKind::ProbabilisticTypeChecker => ("typell", "probabilistic"),
            // Process / communication family
            ProverKind::DyadicTypeChecker => ("typell", "dyadic"),
            // Homotopy foundations
            ProverKind::HomotopyTypeChecker => ("typell", "homotopy"),
            ProverKind::CubicalTypeChecker => ("typell", "cubical"),
            // Binder-management family (nominal logic / HOAS / λ-tree syntax).
            ProverKind::NominalTypeChecker => ("typell", "nominal"),
            other => {
                debug_assert!(
                    false,
                    "non-HP kind routed to HPEcosystemBackend: {:?}",
                    other
                );
                ("typell", "typell")
            },
        }
    }

    fn discipline_tag(&self) -> &'static str {
        self.upstream().1
    }

    /// Build the command that the upstream CLI should run to check
    /// a proof state serialised to `input_path`.
    fn check_command(&self, input_path: &std::path::Path) -> Command {
        let (cli, discipline) = self.upstream();
        let exe = if self.config.executable.as_os_str().is_empty() {
            PathBuf::from(cli)
        } else {
            self.config.executable.clone()
        };
        let mut cmd = Command::new(exe);
        cmd.arg("check")
            .arg("--discipline")
            .arg(discipline)
            .arg(input_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for arg in &self.config.args {
            cmd.arg(arg);
        }
        cmd
    }
}

#[async_trait]
impl ProverBackend for HPEcosystemBackend {
    fn kind(&self) -> ProverKind {
        self.kind
    }

    async fn version(&self) -> Result<String> {
        let (cli, _) = self.upstream();
        let exe = if self.config.executable.as_os_str().is_empty() {
            PathBuf::from(cli)
        } else {
            self.config.executable.clone()
        };
        let output = Command::new(exe).arg("--version").output().await;
        match output {
            Ok(out) => {
                let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
                if s.is_empty() {
                    Ok(format!("{}@hp-ecosystem", self.discipline_tag()))
                } else {
                    Ok(s)
                }
            },
            Err(_) => Ok(format!(
                "{}@hp-ecosystem:unreachable",
                self.discipline_tag()
            )),
        }
    }

    async fn parse_file(&self, path: PathBuf) -> Result<ProofState> {
        let content = tokio::fs::read_to_string(&path)
            .await
            .with_context(|| format!("HP ecosystem: reading {}", path.display()))?;
        self.parse_string(&content).await
    }

    /// Parse a discipline-tagged proof source. The HP stack expects a
    /// header line `#discipline: <tag>` followed by the body; if absent,
    /// we inject one using this backend's discipline.
    async fn parse_string(&self, content: &str) -> Result<ProofState> {
        let has_header = content
            .lines()
            .next()
            .map(|l| l.trim_start().starts_with("#discipline:"))
            .unwrap_or(false);
        let body = if has_header {
            content.to_string()
        } else {
            format!("#discipline: {}\n{}", self.discipline_tag(), content)
        };

        // Single-goal placeholder — the real parse happens in the upstream
        // when verify_proof shells out. We keep the body in metadata so
        // downstream tactics can consult it.
        let mut state = ProofState::default();
        state.goals.push(Goal {
            id: format!("hp-{}", self.discipline_tag()),
            target: Term::Const(body.clone()),
            hypotheses: vec![],
        });
        state.metadata.insert(
            "hp_discipline".to_string(),
            serde_json::Value::String(self.discipline_tag().to_string()),
        );
        state
            .metadata
            .insert("hp_body".to_string(), serde_json::Value::String(body));
        Ok(state)
    }

    async fn apply_tactic(&self, state: &ProofState, tactic: &Tactic) -> Result<TacticResult> {
        // HP tools are batch-verifiers, not interactive tactic engines.
        // We record the tactic on the proof script so the final
        // `verify_proof` call sees the whole history.
        let mut new_state = state.clone();
        new_state.proof_script.push(tactic.clone());
        Ok(TacticResult::Success(new_state))
    }

    async fn verify_proof(&self, state: &ProofState) -> Result<bool> {
        let body: String = state
            .metadata
            .get("hp_body")
            .and_then(|v| v.as_str())
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| {
                state
                    .goals
                    .first()
                    .map(|g| format!("{}", g.target))
                    .unwrap_or_default()
            });

        let tmp_dir = tempfile::Builder::new()
            .prefix("echidna-hp-")
            .tempdir()
            .context("HP ecosystem: tempdir")?;
        let input = tmp_dir
            .path()
            .join(format!("check.{}.src", self.discipline_tag()));
        tokio::fs::write(&input, body.as_bytes())
            .await
            .context("HP ecosystem: writing input")?;

        let mut cmd = self.check_command(&input);
        match cmd.output().await {
            Ok(out) if out.status.success() => Ok(true),
            Ok(out) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                tracing::debug!(
                    discipline = self.discipline_tag(),
                    status = ?out.status.code(),
                    "HP ecosystem: verify_proof rejected"
                );
                tracing::trace!(discipline = self.discipline_tag(), stderr = %stderr);
                Ok(false)
            },
            Err(e) => Err(anyhow!(
                "HP ecosystem ({}): upstream CLI not runnable: {}",
                self.discipline_tag(),
                e
            )),
        }
    }

    async fn export(&self, state: &ProofState) -> Result<String> {
        let cached = state.metadata.get("hp_body").and_then(|v| v.as_str());
        Ok(match cached {
            Some(s) => s.to_owned(),
            None => format!(
                "#discipline: {}\n{}",
                self.discipline_tag(),
                state
                    .goals
                    .iter()
                    .map(|g| format!("{}", g.target))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        })
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> Result<Vec<Tactic>> {
        // Type-checkers don't suggest tactics — they either accept or
        // reject the body. Training-time premise selection will populate
        // this list from the corpus in future.
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> Result<Vec<String>> {
        Ok(vec![])
    }

    fn config(&self) -> &ProverConfig {
        &self.config
    }

    fn set_config(&mut self, config: ProverConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn upstream_routing_distinguishes_disciplines() {
        let tll = HPEcosystemBackend::new(ProverKind::TypeLL, ProverConfig::default());
        let kat = HPEcosystemBackend::new(ProverKind::KatagoriaVerifier, ProverConfig::default());
        let trop =
            HPEcosystemBackend::new(ProverKind::TropicalTypeChecker, ProverConfig::default());
        let modal = HPEcosystemBackend::new(ProverKind::ModalTypeChecker, ProverConfig::default());

        assert_eq!(tll.upstream().0, "typell");
        assert_eq!(kat.upstream().0, "katagoria");
        assert_eq!(trop.upstream().0, "tropical-type-check");
        assert_eq!(modal.upstream().0, "typell");
        assert_eq!(modal.discipline_tag(), "modal");
    }

    #[test]
    fn all_discipline_kinds_are_hp() {
        use ProverKind::*;
        let all = all_hp_discipline_kinds();
        assert_eq!(
            all.len(),
            41,
            "expected forty-one HP ecosystem discipline variants, got {}",
            all.len()
        );
        for k in all {
            assert!(k.is_hp_ecosystem(), "{:?} should be hp_ecosystem", k);
            // Every discipline must route to a known CLI.
            let backend = HPEcosystemBackend::new(k, ProverConfig::default());
            let (cli, tag) = backend.upstream();
            assert!(
                matches!(cli, "typell" | "katagoria" | "tropical-type-check"),
                "{:?} routed to unexpected CLI {}",
                k,
                cli
            );
            assert!(!tag.is_empty(), "{:?} has empty discipline tag", k);
        }
        // Spot-check specific disciplines.
        let linear = HPEcosystemBackend::new(LinearTypeChecker, ProverConfig::default());
        assert_eq!(linear.discipline_tag(), "linear");
        let cubical = HPEcosystemBackend::new(CubicalTypeChecker, ProverConfig::default());
        assert_eq!(cubical.discipline_tag(), "cubical");
        let dyadic = HPEcosystemBackend::new(DyadicTypeChecker, ProverConfig::default());
        assert_eq!(dyadic.discipline_tag(), "dyadic");
    }

    #[test]
    fn discipline_tags_are_unique() {
        let mut tags: Vec<&'static str> = all_hp_discipline_kinds()
            .iter()
            .map(|k| HPEcosystemBackend::new(*k, ProverConfig::default()).discipline_tag())
            .collect();
        tags.sort_unstable();
        let before = tags.len();
        tags.dedup();
        assert_eq!(before, tags.len(), "duplicate discipline tag detected");
    }

    /// Canonical list of every HP ecosystem discipline variant. Kept in sync
    /// with `ProverKind::is_hp_ecosystem` and the `upstream()` dispatch table.
    fn all_hp_discipline_kinds() -> Vec<ProverKind> {
        use ProverKind::*;
        vec![
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
        ]
    }
}
