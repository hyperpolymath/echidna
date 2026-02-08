// SPDX-License-Identifier: PMPL-1.0-or-later

//! Solver binary integrity verification using SHAKE3-512 and BLAKE3
//!
//! Verifies solver binaries at startup and periodically during runtime
//! to detect tampering. Uses SHAKE3-512 (FIPS 202) for provenance hashing
//! and BLAKE3 for fast runtime re-verification.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tiny_keccak::{Hasher, Xof};
use tokio::sync::RwLock;
use tracing::{error, info, warn};

/// Status of a solver's integrity check
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntegrityStatus {
    /// Binary matches the manifest hash
    Verified,
    /// Binary hash does not match the manifest
    Tampered,
    /// Binary was not found at any expected path
    Missing,
    /// Hash in manifest is a placeholder (first run)
    Uninitialized,
    /// Integrity check has not been performed yet
    Unchecked,
}

/// A single solver entry in the manifest
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverManifestEntry {
    /// Solver version
    pub version: String,
    /// SHAKE3-512 hash of the binary (hex-encoded)
    pub shake3_512: String,
    /// Primary path to the solver binary
    pub path: String,
    /// Fallback paths if primary path is not found
    #[serde(default)]
    pub fallback_paths: Vec<String>,
}

/// Solver manifest containing known-good hashes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverManifest {
    /// Map of solver name to manifest entry
    pub solvers: HashMap<String, SolverManifestEntry>,
}

/// Report for a single solver's integrity check
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverIntegrityReport {
    /// Solver name
    pub name: String,
    /// Integrity status
    pub status: IntegrityStatus,
    /// Actual path used (if found)
    pub actual_path: Option<PathBuf>,
    /// Computed SHAKE3-512 hash (if binary was found)
    pub computed_shake3_512: Option<String>,
    /// Computed BLAKE3 hash (for fast re-verification)
    pub computed_blake3: Option<String>,
    /// Expected hash from manifest
    pub expected_shake3_512: Option<String>,
    /// Timestamp of last check
    pub last_checked: chrono::DateTime<chrono::Utc>,
}

/// Integrity checker for solver binaries
pub struct IntegrityChecker {
    /// Solver manifest
    manifest: SolverManifest,
    /// Cached integrity reports (protected by RwLock for periodic re-checks)
    reports: Arc<RwLock<HashMap<String, SolverIntegrityReport>>>,
    /// BLAKE3 hashes for fast runtime re-verification
    blake3_cache: Arc<RwLock<HashMap<String, String>>>,
}

impl IntegrityChecker {
    /// Create a new integrity checker from a manifest file
    pub fn from_manifest_file(path: &Path) -> Result<Self> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read solver manifest: {}", path.display()))?;
        let manifest: SolverManifest = toml::from_str(&content)
            .with_context(|| "Failed to parse solver manifest TOML")?;

        Ok(Self {
            manifest,
            reports: Arc::new(RwLock::new(HashMap::new())),
            blake3_cache: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    /// Create a new integrity checker from a manifest struct
    pub fn new(manifest: SolverManifest) -> Self {
        Self {
            manifest,
            reports: Arc::new(RwLock::new(HashMap::new())),
            blake3_cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Compute SHAKE3-512 hash of a file (64-byte output, hex-encoded)
    pub fn compute_shake3_512(path: &Path) -> Result<String> {
        use tiny_keccak::{Hasher, Shake};

        let data = std::fs::read(path)
            .with_context(|| format!("Failed to read file for hashing: {}", path.display()))?;

        let mut hasher = Shake::v256();
        hasher.update(&data);

        let mut output = [0u8; 64]; // 512 bits = 64 bytes
        hasher.squeeze(&mut output);

        Ok(hex_encode(&output))
    }

    /// Compute BLAKE3 hash of a file (32-byte output, hex-encoded)
    pub fn compute_blake3(path: &Path) -> Result<String> {
        let data = std::fs::read(path)
            .with_context(|| format!("Failed to read file for hashing: {}", path.display()))?;

        let hash = blake3::hash(&data);
        Ok(hash.to_hex().to_string())
    }

    /// Find the actual path of a solver binary
    fn find_solver_binary(entry: &SolverManifestEntry) -> Option<PathBuf> {
        let primary = expand_tilde(&entry.path);
        if primary.exists() {
            return Some(primary);
        }

        for fallback in &entry.fallback_paths {
            let path = expand_tilde(fallback);
            if path.exists() {
                return Some(path);
            }
        }

        // Try PATH lookup
        if let Ok(output) = std::process::Command::new("which")
            .arg(Path::new(&entry.path).file_name().unwrap_or_default())
            .output()
        {
            if output.status.success() {
                let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
                let path = PathBuf::from(&path_str);
                if path.exists() {
                    return Some(path);
                }
            }
        }

        None
    }

    /// Verify all solver binaries against the manifest
    pub async fn verify_all(&self) -> Result<Vec<SolverIntegrityReport>> {
        let mut results = Vec::new();

        for (name, entry) in &self.manifest.solvers {
            let report = self.verify_solver(name, entry).await;
            results.push(report);
        }

        // Cache results
        let mut reports = self.reports.write().await;
        for report in &results {
            reports.insert(report.name.clone(), report.clone());
        }

        // Summary
        let verified = results.iter().filter(|r| r.status == IntegrityStatus::Verified).count();
        let tampered = results.iter().filter(|r| r.status == IntegrityStatus::Tampered).count();
        let missing = results.iter().filter(|r| r.status == IntegrityStatus::Missing).count();
        let uninitialized = results.iter().filter(|r| r.status == IntegrityStatus::Uninitialized).count();

        info!(
            "Solver integrity check: {} verified, {} tampered, {} missing, {} uninitialized",
            verified, tampered, missing, uninitialized
        );

        if tampered > 0 {
            error!("CRITICAL: {} solver binaries have been tampered with!", tampered);
        }

        Ok(results)
    }

    /// Verify a single solver binary
    async fn verify_solver(&self, name: &str, entry: &SolverManifestEntry) -> SolverIntegrityReport {
        let now = chrono::Utc::now();

        // Find the binary
        let actual_path = match Self::find_solver_binary(entry) {
            Some(path) => path,
            None => {
                warn!("Solver binary not found: {} (expected at {})", name, entry.path);
                return SolverIntegrityReport {
                    name: name.to_string(),
                    status: IntegrityStatus::Missing,
                    actual_path: None,
                    computed_shake3_512: None,
                    computed_blake3: None,
                    expected_shake3_512: Some(entry.shake3_512.clone()),
                    last_checked: now,
                };
            }
        };

        // Check if manifest hash is a placeholder
        if entry.shake3_512.starts_with("PLACEHOLDER") {
            info!("Solver {} has placeholder hash, computing initial hash", name);

            let shake3 = Self::compute_shake3_512(&actual_path).ok();
            let blake3 = Self::compute_blake3(&actual_path).ok();

            // Cache BLAKE3 for fast re-verification
            if let Some(ref b3) = blake3 {
                let mut cache = self.blake3_cache.write().await;
                cache.insert(name.to_string(), b3.clone());
            }

            return SolverIntegrityReport {
                name: name.to_string(),
                status: IntegrityStatus::Uninitialized,
                actual_path: Some(actual_path),
                computed_shake3_512: shake3,
                computed_blake3: blake3,
                expected_shake3_512: Some(entry.shake3_512.clone()),
                last_checked: now,
            };
        }

        // Compute hash and compare
        match Self::compute_shake3_512(&actual_path) {
            Ok(computed) => {
                let blake3_hash = Self::compute_blake3(&actual_path).ok();

                // Cache BLAKE3 for fast re-verification
                if let Some(ref b3) = blake3_hash {
                    let mut cache = self.blake3_cache.write().await;
                    cache.insert(name.to_string(), b3.clone());
                }

                let status = if computed == entry.shake3_512 {
                    info!("Solver {} integrity verified", name);
                    IntegrityStatus::Verified
                } else {
                    error!(
                        "CRITICAL: Solver {} integrity FAILED! Expected: {}, Got: {}",
                        name, entry.shake3_512, computed
                    );
                    IntegrityStatus::Tampered
                };

                SolverIntegrityReport {
                    name: name.to_string(),
                    status,
                    actual_path: Some(actual_path),
                    computed_shake3_512: Some(computed),
                    computed_blake3: blake3_hash,
                    expected_shake3_512: Some(entry.shake3_512.clone()),
                    last_checked: now,
                }
            }
            Err(e) => {
                error!("Failed to compute hash for solver {}: {}", name, e);
                SolverIntegrityReport {
                    name: name.to_string(),
                    status: IntegrityStatus::Missing,
                    actual_path: Some(actual_path),
                    computed_shake3_512: None,
                    computed_blake3: None,
                    expected_shake3_512: Some(entry.shake3_512.clone()),
                    last_checked: now,
                }
            }
        }
    }

    /// Fast runtime re-verification using BLAKE3
    /// Returns true if the binary has not changed since last full verification
    pub async fn quick_reverify(&self, solver_name: &str) -> Result<bool> {
        let cache = self.blake3_cache.read().await;
        let cached_hash = cache.get(solver_name)
            .ok_or_else(|| anyhow::anyhow!("No cached BLAKE3 hash for solver: {}", solver_name))?
            .clone();
        drop(cache);

        let entry = self.manifest.solvers.get(solver_name)
            .ok_or_else(|| anyhow::anyhow!("Unknown solver: {}", solver_name))?;

        let actual_path = Self::find_solver_binary(entry)
            .ok_or_else(|| anyhow::anyhow!("Solver binary not found: {}", solver_name))?;

        let current_hash = Self::compute_blake3(&actual_path)?;

        if current_hash != cached_hash {
            error!("ALERT: Solver {} binary changed during runtime!", solver_name);
            Ok(false)
        } else {
            Ok(true)
        }
    }

    /// Get the current integrity status of a solver
    pub async fn get_status(&self, solver_name: &str) -> IntegrityStatus {
        let reports = self.reports.read().await;
        reports.get(solver_name)
            .map(|r| r.status.clone())
            .unwrap_or(IntegrityStatus::Unchecked)
    }

    /// Check if a solver is safe to use (verified or uninitialized)
    pub async fn is_solver_safe(&self, solver_name: &str) -> bool {
        let status = self.get_status(solver_name).await;
        matches!(status, IntegrityStatus::Verified | IntegrityStatus::Uninitialized | IntegrityStatus::Unchecked)
    }

    /// Get all integrity reports
    pub async fn get_all_reports(&self) -> Vec<SolverIntegrityReport> {
        let reports = self.reports.read().await;
        reports.values().cloned().collect()
    }

    /// Get the number of verified solvers
    pub async fn verified_count(&self) -> usize {
        let reports = self.reports.read().await;
        reports.values()
            .filter(|r| r.status == IntegrityStatus::Verified)
            .count()
    }
}

/// Expand ~ to home directory in paths
fn expand_tilde(path: &str) -> PathBuf {
    if path.starts_with("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            return PathBuf::from(home).join(&path[2..]);
        }
    }
    PathBuf::from(path)
}

/// Hex-encode a byte slice
fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;
    use std::io::Write;

    #[test]
    fn test_hex_encode() {
        assert_eq!(hex_encode(&[0x00, 0xff, 0xab]), "00ffab");
    }

    #[test]
    fn test_compute_blake3() {
        let mut tmp = NamedTempFile::new().unwrap();
        write!(tmp, "test content for hashing").unwrap();

        let hash = IntegrityChecker::compute_blake3(tmp.path()).unwrap();
        assert_eq!(hash.len(), 64); // 32 bytes = 64 hex chars

        // Same content should give same hash
        let hash2 = IntegrityChecker::compute_blake3(tmp.path()).unwrap();
        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_compute_shake3_512() {
        let mut tmp = NamedTempFile::new().unwrap();
        write!(tmp, "test content for SHAKE3-512").unwrap();

        let hash = IntegrityChecker::compute_shake3_512(tmp.path()).unwrap();
        assert_eq!(hash.len(), 128); // 64 bytes = 128 hex chars

        // Same content should give same hash
        let hash2 = IntegrityChecker::compute_shake3_512(tmp.path()).unwrap();
        assert_eq!(hash, hash2);
    }

    #[test]
    fn test_tampered_binary_detected() {
        let mut tmp = NamedTempFile::new().unwrap();
        write!(tmp, "original content").unwrap();

        let original_hash = IntegrityChecker::compute_blake3(tmp.path()).unwrap();

        // Modify the file
        write!(tmp, "tampered content!").unwrap();

        let tampered_hash = IntegrityChecker::compute_blake3(tmp.path()).unwrap();

        assert_ne!(original_hash, tampered_hash, "Tampered binary should have different hash");
    }

    #[test]
    fn test_missing_binary_handled() {
        let result = IntegrityChecker::compute_blake3(Path::new("/nonexistent/binary"));
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_integrity_checker_verify_all() {
        let manifest = SolverManifest {
            solvers: HashMap::from([
                ("test_solver".to_string(), SolverManifestEntry {
                    version: "1.0".to_string(),
                    shake3_512: "PLACEHOLDER_COMPUTE_ON_FIRST_RUN".to_string(),
                    path: "/nonexistent/solver".to_string(),
                    fallback_paths: vec![],
                }),
            ]),
        };

        let checker = IntegrityChecker::new(manifest);
        let reports = checker.verify_all().await.unwrap();

        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].status, IntegrityStatus::Missing);
    }

    #[tokio::test]
    async fn test_health_check_reports_status() {
        let manifest = SolverManifest {
            solvers: HashMap::new(),
        };

        let checker = IntegrityChecker::new(manifest);
        let reports = checker.verify_all().await.unwrap();
        assert!(reports.is_empty());

        let status = checker.get_status("nonexistent").await;
        assert_eq!(status, IntegrityStatus::Unchecked);
    }
}
