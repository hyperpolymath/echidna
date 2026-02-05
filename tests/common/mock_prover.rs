// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Mock prover backend for testing

use async_trait::async_trait;
use echidna::core::{ProofState, Tactic, TacticResult, Term};
use echidna::provers::{ProverBackend, ProverConfig, ProverKind};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

/// A mock prover backend for testing
pub struct MockProver {
    pub kind: ProverKind,
    pub version_string: String,
    pub config: ProverConfig,
    pub parse_results: Arc<Mutex<Vec<anyhow::Result<ProofState>>>>,
    pub verify_results: Arc<Mutex<Vec<anyhow::Result<bool>>>>,
    pub tactic_results: Arc<Mutex<Vec<anyhow::Result<TacticResult>>>>,
    pub export_results: Arc<Mutex<Vec<anyhow::Result<String>>>>,
}

impl MockProver {
    /// Create a new mock prover
    pub fn new(kind: ProverKind) -> Self {
        MockProver {
            kind,
            version_string: "Mock 1.0.0".to_string(),
            config: ProverConfig::default(),
            parse_results: Arc::new(Mutex::new(vec![])),
            verify_results: Arc::new(Mutex::new(vec![])),
            tactic_results: Arc::new(Mutex::new(vec![])),
            export_results: Arc::new(Mutex::new(vec![])),
        }
    }

    /// Add a parse result to return
    pub fn add_parse_result(&self, result: anyhow::Result<ProofState>) {
        self.parse_results.lock().unwrap().push(result);
    }

    /// Add a verify result to return
    pub fn add_verify_result(&self, result: anyhow::Result<bool>) {
        self.verify_results.lock().unwrap().push(result);
    }

    /// Add a tactic result to return
    pub fn add_tactic_result(&self, result: anyhow::Result<TacticResult>) {
        self.tactic_results.lock().unwrap().push(result);
    }

    /// Add an export result to return
    pub fn add_export_result(&self, result: anyhow::Result<String>) {
        self.export_results.lock().unwrap().push(result);
    }

    /// Pop the next parse result
    fn pop_parse_result(&self) -> anyhow::Result<ProofState> {
        self.parse_results
            .lock()
            .unwrap()
            .pop()
            .unwrap_or_else(|| {
                Ok(crate::common::simple_proof_state())
            })
    }

    /// Pop the next verify result
    fn pop_verify_result(&self) -> anyhow::Result<bool> {
        self.verify_results
            .lock()
            .unwrap()
            .pop()
            .unwrap_or(Ok(true))
    }

    /// Pop the next tactic result
    fn pop_tactic_result(&self) -> anyhow::Result<TacticResult> {
        self.tactic_results
            .lock()
            .unwrap()
            .pop()
            .unwrap_or_else(|| {
                Ok(TacticResult::Success(crate::common::simple_proof_state()))
            })
    }

    /// Pop the next export result
    fn pop_export_result(&self) -> anyhow::Result<String> {
        self.export_results
            .lock()
            .unwrap()
            .pop()
            .unwrap_or_else(|| Ok("-- Generated proof".to_string()))
    }
}

#[async_trait]
impl ProverBackend for MockProver {
    fn kind(&self) -> ProverKind {
        self.kind
    }

    async fn version(&self) -> anyhow::Result<String> {
        Ok(self.version_string.clone())
    }

    async fn parse_file(&self, _path: PathBuf) -> anyhow::Result<ProofState> {
        self.pop_parse_result()
    }

    async fn parse_string(&self, _content: &str) -> anyhow::Result<ProofState> {
        self.pop_parse_result()
    }

    async fn apply_tactic(
        &self,
        _state: &ProofState,
        _tactic: &Tactic,
    ) -> anyhow::Result<TacticResult> {
        self.pop_tactic_result()
    }

    async fn verify_proof(&self, _state: &ProofState) -> anyhow::Result<bool> {
        self.pop_verify_result()
    }

    async fn export(&self, _state: &ProofState) -> anyhow::Result<String> {
        self.pop_export_result()
    }

    async fn suggest_tactics(&self, _state: &ProofState, _limit: usize) -> anyhow::Result<Vec<Tactic>> {
        Ok(vec![])
    }

    async fn search_theorems(&self, _pattern: &str) -> anyhow::Result<Vec<String>> {
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
    use echidna::provers::ProverKind;

    #[tokio::test]
    async fn test_mock_prover_version() {
        let mock = MockProver::new(ProverKind::Agda);
        let version = mock.version().await.unwrap();
        assert_eq!(version, "Mock 1.0.0");
    }

    #[tokio::test]
    async fn test_mock_prover_parse() {
        let mock = MockProver::new(ProverKind::Agda);
        let result = mock.parse_string("test").await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_mock_prover_custom_result() {
        let mock = MockProver::new(ProverKind::Agda);
        mock.add_verify_result(Ok(false));

        let state = crate::common::simple_proof_state();
        let result = mock.verify_proof(&state).await.unwrap();
        assert!(!result);
    }
}
