// SPDX-License-Identifier: PMPL-1.0-or-later
// Health diagnostics and monitoring for echidna

pub mod corpus_monitor;
pub mod health;
pub mod gnn_training;
pub mod proof_failure;
pub mod nesy_validation;
pub mod fallback_monitor;

pub use corpus_monitor::{CorpusMetrics, CorpusMonitor};
pub use health::{HealthStatus, ProverHealth, ModelHealth, CorpusHealth, DegradationMode, CircuitBreakerStateSnapshot};
pub use gnn_training::{GnnTrainingMetrics, load_training_metrics, update_health_with_metrics};
pub use proof_failure::{diagnose, diagnose_from_outcome, DiagnosticReport, FailureKind, SourceLocation};
pub use nesy_validation::{NeSyRankingContract, NeSyMetrics, compute_agreement_rate, is_gnn_suspect, compute_metrics, can_claim_gnn_verified};
pub use fallback_monitor::{FallbackMonitor, FallbackSLAConfig, FallbackInvocation, FallbackTimer};
