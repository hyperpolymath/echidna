// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! Solver integrity verification
//!
//! Before dispatching proofs to ECHIDNA, verifies that the solver binaries
//! have not been tampered with by checking against a SHA-256 manifest.
//!
//! The manifest maps solver names to their expected SHA-256 hashes. This
//! prevents attacks where a compromised solver binary could falsely report
//! proofs as verified.
//!
//! Note: Uses SHA-256 for file integrity (not cryptographic signing).
//! Future work: switch to BLAKE3 for performance on large binaries.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::dispatcher::ProverKind;

/// Status of a solver integrity check
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntegrityStatus {
    /// Binary hash matches the manifest
    Verified,
    /// Binary hash does not match (possible tampering)
    Tampered,
    /// Solver binary not found on system
    NotFound,
    /// No manifest entry for this solver (can't verify)
    Unchecked,
    /// Error reading binary or computing hash
    Error,
}

impl IntegrityStatus {
    /// Whether the solver is safe to use for proof verification
    pub fn is_safe(&self) -> bool {
        matches!(self, IntegrityStatus::Verified)
    }

    /// Human-readable label
    pub fn label(&self) -> &'static str {
        match self {
            Self::Verified => "Integrity verified",
            Self::Tampered => "TAMPERED - binary hash mismatch",
            Self::NotFound => "Binary not found",
            Self::Unchecked => "No manifest entry (unchecked)",
            Self::Error => "Error checking integrity",
        }
    }
}

impl std::fmt::Display for IntegrityStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label())
    }
}

/// Report from an integrity check of a solver binary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IntegrityReport {
    /// Prover that was checked
    pub prover: ProverKind,
    /// Result of the integrity check
    pub status: IntegrityStatus,
    /// Expected hash from manifest (if available)
    pub expected_hash: Option<String>,
    /// Actual hash of the binary (if readable)
    pub actual_hash: Option<String>,
    /// Path to the binary that was checked
    pub binary_path: Option<String>,
    /// Justification or error message
    pub message: String,
}

/// Solver integrity verifier.
///
/// Maintains a SHA-256 hash manifest for solver binaries and checks
/// them before dispatching proof verification requests.
pub struct SolverIntegrity {
    /// Map from prover name to expected SHA-256 hash
    manifest: HashMap<String, String>,
}

impl SolverIntegrity {
    /// Create a new integrity verifier with an empty manifest.
    pub fn new() -> Self {
        Self {
            manifest: HashMap::new(),
        }
    }

    /// Create an integrity verifier from a hash manifest.
    ///
    /// The manifest maps solver names (lowercase) to SHA-256 hex strings.
    pub fn with_manifest(manifest: HashMap<String, String>) -> Self {
        Self { manifest }
    }

    /// Load a manifest from a JSON string.
    ///
    /// Expected format:
    /// ```json
    /// {
    ///     "coq": "a1b2c3d4...",
    ///     "lean": "e5f6a7b8...",
    ///     "z3": "c9d0e1f2..."
    /// }
    /// ```
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        let manifest: HashMap<String, String> = serde_json::from_str(json)?;
        Ok(Self::with_manifest(manifest))
    }

    /// Add or update a manifest entry for a specific prover.
    pub fn set_expected_hash(&mut self, prover: ProverKind, hash: impl Into<String>) {
        self.manifest
            .insert(prover_key(prover), hash.into());
    }

    /// Check if a manifest entry exists for a prover.
    pub fn has_manifest_entry(&self, prover: ProverKind) -> bool {
        self.manifest.contains_key(&prover_key(prover))
    }

    /// Get the expected hash for a prover (if in manifest).
    pub fn expected_hash(&self, prover: ProverKind) -> Option<&str> {
        self.manifest.get(&prover_key(prover)).map(|s| s.as_str())
    }

    /// Verify a solver binary against its manifest entry.
    ///
    /// # Arguments
    /// * `prover` - Which prover to verify
    /// * `actual_hash` - The SHA-256 hash of the binary on disk
    /// * `binary_path` - Path to the binary (for reporting)
    pub fn verify(
        &self,
        prover: ProverKind,
        actual_hash: &str,
        binary_path: &str,
    ) -> IntegrityReport {
        let key = prover_key(prover);

        match self.manifest.get(&key) {
            Some(expected) => {
                // Constant-time comparison to prevent timing attacks
                let matches = constant_time_eq(expected.as_bytes(), actual_hash.as_bytes());

                if matches {
                    IntegrityReport {
                        prover,
                        status: IntegrityStatus::Verified,
                        expected_hash: Some(expected.clone()),
                        actual_hash: Some(actual_hash.to_string()),
                        binary_path: Some(binary_path.to_string()),
                        message: format!(
                            "{} binary integrity verified (SHA-256 matches manifest)",
                            prover.display_name()
                        ),
                    }
                } else {
                    IntegrityReport {
                        prover,
                        status: IntegrityStatus::Tampered,
                        expected_hash: Some(expected.clone()),
                        actual_hash: Some(actual_hash.to_string()),
                        binary_path: Some(binary_path.to_string()),
                        message: format!(
                            "WARNING: {} binary hash mismatch! Expected {} but got {}. \
                             Possible tampering detected.",
                            prover.display_name(),
                            &expected[..16.min(expected.len())],
                            &actual_hash[..16.min(actual_hash.len())],
                        ),
                    }
                }
            }
            None => IntegrityReport {
                prover,
                status: IntegrityStatus::Unchecked,
                expected_hash: None,
                actual_hash: Some(actual_hash.to_string()),
                binary_path: Some(binary_path.to_string()),
                message: format!(
                    "No manifest entry for {} -- integrity not verified",
                    prover.display_name()
                ),
            },
        }
    }

    /// Create a report for a solver that was not found on the system.
    pub fn report_not_found(&self, prover: ProverKind) -> IntegrityReport {
        IntegrityReport {
            prover,
            status: IntegrityStatus::NotFound,
            expected_hash: self.expected_hash(prover).map(|s| s.to_string()),
            actual_hash: None,
            binary_path: None,
            message: format!(
                "{} binary not found on system",
                prover.display_name()
            ),
        }
    }

    /// Create a report for an error during integrity checking.
    pub fn report_error(&self, prover: ProverKind, error: &str) -> IntegrityReport {
        IntegrityReport {
            prover,
            status: IntegrityStatus::Error,
            expected_hash: self.expected_hash(prover).map(|s| s.to_string()),
            actual_hash: None,
            binary_path: None,
            message: format!(
                "Error checking {} integrity: {}",
                prover.display_name(),
                error
            ),
        }
    }

    /// Get the number of entries in the manifest.
    pub fn manifest_size(&self) -> usize {
        self.manifest.len()
    }
}

impl Default for SolverIntegrity {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert a prover kind to a manifest key (lowercase name).
fn prover_key(prover: ProverKind) -> String {
    format!("{:?}", prover).to_lowercase()
}

/// Constant-time byte comparison to prevent timing side channels.
///
/// Returns true if both slices are equal in length and content.
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        result |= x ^ y;
    }
    result == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_manifest() -> SolverIntegrity {
        let mut manifest = HashMap::new();
        manifest.insert("coq".to_string(), "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890".to_string());
        manifest.insert("lean".to_string(), "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_string());
        manifest.insert("z3".to_string(), "fedcba0987654321fedcba0987654321fedcba0987654321fedcba0987654321".to_string());
        SolverIntegrity::with_manifest(manifest)
    }

    #[test]
    fn test_integrity_verified() {
        let integrity = sample_manifest();
        let report = integrity.verify(
            ProverKind::Coq,
            "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
            "/usr/bin/coqc",
        );
        assert_eq!(report.status, IntegrityStatus::Verified);
        assert!(report.status.is_safe());
    }

    #[test]
    fn test_integrity_tampered() {
        let integrity = sample_manifest();
        let report = integrity.verify(
            ProverKind::Coq,
            "0000000000000000000000000000000000000000000000000000000000000000",
            "/usr/bin/coqc",
        );
        assert_eq!(report.status, IntegrityStatus::Tampered);
        assert!(!report.status.is_safe());
        assert!(report.message.contains("mismatch"));
    }

    #[test]
    fn test_integrity_unchecked() {
        let integrity = sample_manifest();
        let report = integrity.verify(
            ProverKind::Agda, // Not in manifest
            "somehashvalue",
            "/usr/bin/agda",
        );
        assert_eq!(report.status, IntegrityStatus::Unchecked);
        assert!(!report.status.is_safe());
    }

    #[test]
    fn test_integrity_not_found() {
        let integrity = sample_manifest();
        let report = integrity.report_not_found(ProverKind::Isabelle);
        assert_eq!(report.status, IntegrityStatus::NotFound);
        assert!(!report.status.is_safe());
    }

    #[test]
    fn test_integrity_error() {
        let integrity = sample_manifest();
        let report = integrity.report_error(ProverKind::Z3, "Permission denied");
        assert_eq!(report.status, IntegrityStatus::Error);
        assert!(report.message.contains("Permission denied"));
    }

    #[test]
    fn test_manifest_from_json() {
        let json = r#"{"coq": "abc123", "lean": "def456"}"#;
        let integrity = SolverIntegrity::from_json(json).unwrap();
        assert_eq!(integrity.manifest_size(), 2);
        assert!(integrity.has_manifest_entry(ProverKind::Coq));
        assert!(integrity.has_manifest_entry(ProverKind::Lean));
        assert!(!integrity.has_manifest_entry(ProverKind::Z3));
    }

    #[test]
    fn test_set_expected_hash() {
        let mut integrity = SolverIntegrity::new();
        assert!(!integrity.has_manifest_entry(ProverKind::Metamath));

        integrity.set_expected_hash(ProverKind::Metamath, "hash123");
        assert!(integrity.has_manifest_entry(ProverKind::Metamath));
        assert_eq!(integrity.expected_hash(ProverKind::Metamath), Some("hash123"));
    }

    #[test]
    fn test_constant_time_eq() {
        assert!(constant_time_eq(b"hello", b"hello"));
        assert!(!constant_time_eq(b"hello", b"world"));
        assert!(!constant_time_eq(b"hello", b"hell"));
        assert!(constant_time_eq(b"", b""));
    }

    #[test]
    fn test_integrity_status_display() {
        assert_eq!(IntegrityStatus::Verified.label(), "Integrity verified");
        assert!(IntegrityStatus::Tampered.label().contains("TAMPERED"));
    }
}
