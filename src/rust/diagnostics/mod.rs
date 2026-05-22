// SPDX-License-Identifier: MPL-2.0
// Health diagnostics and monitoring for echidna

pub mod corpus_monitor;
pub mod fallback_monitor;
pub mod gnn_training;
pub mod health;
pub mod nesy_validation;
pub mod proof_failure;

pub use corpus_monitor::{CorpusMetrics, CorpusMonitor};
pub use fallback_monitor::{FallbackInvocation, FallbackMonitor, FallbackSLAConfig, FallbackTimer};
pub use gnn_training::{load_training_metrics, update_health_with_metrics, GnnTrainingMetrics};
pub use health::{
    CircuitBreakerStateSnapshot, CorpusHealth, DegradationMode, HealthStatus, ModelHealth,
    ProverHealth,
};
pub use nesy_validation::{
    can_claim_gnn_verified, compute_agreement_rate, compute_metrics, is_gnn_suspect, NeSyMetrics,
    NeSyRankingContract,
};
pub use proof_failure::{
    diagnose, diagnose_from_outcome, DiagnosticReport, FailureKind, SourceLocation,
};
