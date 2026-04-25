// SPDX-License-Identifier: PMPL-1.0-or-later
// Health diagnostics and monitoring for echidna

pub mod corpus_monitor;
pub mod health;
pub mod gnn_training;
pub mod proof_failure;

pub use corpus_monitor::{CorpusMetrics, CorpusMonitor};
pub use health::{HealthStatus, ProverHealth, ModelHealth, CorpusHealth, DegradationMode};
pub use gnn_training::{GnnTrainingMetrics, load_training_metrics, update_health_with_metrics};
pub use proof_failure::{diagnose, DiagnosticReport, FailureKind, SourceLocation};
