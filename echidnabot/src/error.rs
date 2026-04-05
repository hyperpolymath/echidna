// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Error types for echidnabot

use thiserror::Error;

/// Result type alias using our Error type
pub type Result<T> = std::result::Result<T, Error>;

/// Main error type for echidnabot
#[derive(Error, Debug)]
pub enum Error {
    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("SQL error: {0}")]
    Sqlx(sqlx::Error),

    #[error("Invalid input: {0}")]
    InvalidInput(String),

    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("GitHub API error: {0}")]
    GitHub(String),

    #[error("Unsupported operation: {0}")]
    Unsupported(String),

    #[error("ECHIDNA communication error: {0}")]
    Echidna(String),

    #[error("Webhook verification failed: {0}")]
    WebhookVerification(String),

    #[error("Invalid prover: {0}")]
    InvalidProver(String),

    #[error("Job not found: {0}")]
    JobNotFound(uuid::Uuid),

    #[error("Repository not found: {0}")]
    RepoNotFound(String),

    #[error("Proof verification timeout")]
    Timeout,

    #[error("Internal error: {0}")]
    Internal(String),
}

impl From<config::ConfigError> for Error {
    fn from(err: config::ConfigError) -> Self {
        Error::Config(err.to_string())
    }
}
