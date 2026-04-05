// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//! ReScript Migration Pattern Scanner
//!
//! Scans ReScript source files and configuration for deprecated API usage
//! patterns that indicate migration is required. Produces findings with
//! MIGRATION_REQUIRED severity for the fleet dispatch pipeline.
//!
//! Detected patterns:
//! - Deprecated Js.* APIs (Js.Array2, Js.String2, Js.Dict, etc.)
//! - Deprecated Belt.* APIs (Belt.Array, Belt.List, Belt.Map, etc.)
//! - bsconfig.json presence (should be rescript.json)
//! - Old JSX syntax / curried defaults
//!
//! These findings feed into VeriSimDB via the Hypatia → ScanIngester pipeline
//! and are used by the migration observatory (feedback-o-tron).

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Severity of a migration pattern detection
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MigrationSeverity {
    /// Must be resolved before migration can complete
    Required,
    /// Should be resolved but not blocking
    Recommended,
    /// Informational — already using modern API
    Info,
}

impl MigrationSeverity {
    /// Numeric severity (higher = more urgent)
    pub fn level(&self) -> u8 {
        match self {
            Self::Required => 3,
            Self::Recommended => 2,
            Self::Info => 1,
        }
    }

    /// Human-readable label
    pub fn label(&self) -> &'static str {
        match self {
            Self::Required => "MIGRATION_REQUIRED",
            Self::Recommended => "MIGRATION_RECOMMENDED",
            Self::Info => "MIGRATION_INFO",
        }
    }
}

impl std::fmt::Display for MigrationSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label())
    }
}

/// Category of deprecated pattern
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DeprecatedCategory {
    /// Js.* namespace APIs (Js.Array2, Js.String2, Js.Dict, etc.)
    JsApi,
    /// Belt.* namespace APIs (Belt.Array, Belt.List, Belt.Map, etc.)
    BeltApi,
    /// bsconfig.json instead of rescript.json
    BsConfig,
    /// Curried-by-default function style
    CurriedDefault,
    /// Old JSX version (v3 or earlier)
    OldJsx,
    /// Unsafe type coercion patterns
    UnsafeCoercion,
}

impl std::fmt::Display for DeprecatedCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::JsApi => write!(f, "Deprecated Js.* API"),
            Self::BeltApi => write!(f, "Deprecated Belt.* API"),
            Self::BsConfig => write!(f, "bsconfig.json (use rescript.json)"),
            Self::CurriedDefault => write!(f, "Curried-by-default function"),
            Self::OldJsx => write!(f, "Old JSX version"),
            Self::UnsafeCoercion => write!(f, "Unsafe type coercion"),
        }
    }
}

/// A single deprecated pattern match in a file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrationPatternMatch {
    /// File where the pattern was found
    pub file: PathBuf,
    /// Line number (1-indexed)
    pub line: usize,
    /// The deprecated pattern that was matched
    pub pattern: String,
    /// What it should be replaced with
    pub replacement: String,
    /// Category of the deprecated pattern
    pub category: DeprecatedCategory,
    /// Severity of this finding
    pub severity: MigrationSeverity,
}

/// Report from scanning a repository or file for migration patterns
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrationScanReport {
    /// Path to the scanned target
    pub target: PathBuf,
    /// All detected deprecated patterns
    pub patterns: Vec<MigrationPatternMatch>,
    /// Count of MIGRATION_REQUIRED findings
    pub required_count: usize,
    /// Count of MIGRATION_RECOMMENDED findings
    pub recommended_count: usize,
    /// Whether bsconfig.json was found
    pub has_bsconfig: bool,
    /// Whether rescript.json was found
    pub has_rescript_json: bool,
    /// Overall assessment: true if no required migrations remain
    pub migration_clean: bool,
}

impl MigrationScanReport {
    /// Format as a human-readable summary
    pub fn summary(&self) -> String {
        if self.migration_clean {
            return "No deprecated patterns detected (migration clean)".to_string();
        }

        let mut parts = Vec::new();
        if self.required_count > 0 {
            parts.push(format!("{} required migration(s)", self.required_count));
        }
        if self.recommended_count > 0 {
            parts.push(format!("{} recommended", self.recommended_count));
        }
        if self.has_bsconfig && !self.has_rescript_json {
            parts.push("bsconfig.json needs migration to rescript.json".to_string());
        }
        parts.join(", ")
    }
}

/// Deprecated Js.* API patterns with their modern replacements
const JS_DEPRECATED_PATTERNS: &[(&str, &str)] = &[
    ("Js.Array2", "Array"),
    ("Js.String2", "String"),
    ("Js.Dict", "Dict"),
    ("Js.Console", "Console"),
    ("Js.log", "Console.log"),
    ("Js.log2", "Console.log2"),
    ("Js.Promise", "Promise"),
    ("Js.Nullable", "Nullable"),
    ("Js.Float", "Float"),
    ("Js.Int", "Int"),
    ("Js.Math", "Math"),
    ("Js.Json", "JSON"),
    ("Js.Re", "RegExp"),
    ("Js.Date", "Date"),
    ("Js.Array.", "Array"),
    ("Js.String.", "String"),
];

/// Deprecated Belt.* API patterns with their modern replacements
const BELT_DEPRECATED_PATTERNS: &[(&str, &str)] = &[
    ("Belt.Array", "Array"),
    ("Belt.List", "List"),
    ("Belt.Map", "Map"),
    ("Belt.Set", "Set"),
    ("Belt.Option", "Option"),
    ("Belt.Result", "Result"),
    ("Belt.Int", "Int"),
    ("Belt.Float", "Float"),
    ("Belt.SortArray", "Array (with sort)"),
    ("Belt.HashMap", "Map / Dict"),
    ("Belt.HashSet", "Set"),
    ("Belt.MutableMap", "Map"),
    ("Belt.MutableSet", "Set"),
];

/// ReScript Migration Pattern Scanner
///
/// Scans source code text for deprecated ReScript patterns. Unlike
/// AxiomTracker (which scans prover output), this scanner works on
/// raw ReScript source files and configuration.
pub struct MigrationScanner;

impl MigrationScanner {
    /// Scan a source file's content for deprecated migration patterns.
    ///
    /// # Arguments
    /// * `file` - Path to the file being scanned (for location reporting)
    /// * `content` - Raw source file content
    pub fn scan_source(file: &Path, content: &str) -> Vec<MigrationPatternMatch> {
        let mut matches = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let line_1indexed = line_num + 1;

            // Scan for deprecated Js.* patterns
            for &(pattern, replacement) in JS_DEPRECATED_PATTERNS {
                if line.contains(pattern) {
                    matches.push(MigrationPatternMatch {
                        file: file.to_path_buf(),
                        line: line_1indexed,
                        pattern: pattern.to_string(),
                        replacement: replacement.to_string(),
                        category: DeprecatedCategory::JsApi,
                        severity: MigrationSeverity::Required,
                    });
                }
            }

            // Scan for deprecated Belt.* patterns
            for &(pattern, replacement) in BELT_DEPRECATED_PATTERNS {
                if line.contains(pattern) {
                    matches.push(MigrationPatternMatch {
                        file: file.to_path_buf(),
                        line: line_1indexed,
                        pattern: pattern.to_string(),
                        replacement: replacement.to_string(),
                        category: DeprecatedCategory::BeltApi,
                        severity: MigrationSeverity::Required,
                    });
                }
            }

            // Scan for unsafe coercion patterns
            if line.contains("Obj.magic") || line.contains("%identity") {
                matches.push(MigrationPatternMatch {
                    file: file.to_path_buf(),
                    line: line_1indexed,
                    pattern: if line.contains("Obj.magic") {
                        "Obj.magic".to_string()
                    } else {
                        "%identity".to_string()
                    },
                    replacement: "Type-safe alternative".to_string(),
                    category: DeprecatedCategory::UnsafeCoercion,
                    severity: MigrationSeverity::Recommended,
                });
            }
        }

        matches
    }

    /// Scan a config file (bsconfig.json or rescript.json) for migration issues.
    ///
    /// Checks for:
    /// - bsconfig.json presence (should be rescript.json)
    /// - Old JSX version settings
    /// - bs-dependencies (should be dependencies)
    /// - Curried-by-default absence
    pub fn scan_config(file: &Path, content: &str) -> Vec<MigrationPatternMatch> {
        let mut matches = Vec::new();
        let filename = file.file_name().and_then(|n| n.to_str()).unwrap_or("");

        // bsconfig.json should be rescript.json
        if filename == "bsconfig.json" {
            matches.push(MigrationPatternMatch {
                file: file.to_path_buf(),
                line: 1,
                pattern: "bsconfig.json".to_string(),
                replacement: "rescript.json".to_string(),
                category: DeprecatedCategory::BsConfig,
                severity: MigrationSeverity::Required,
            });
        }

        for (line_num, line) in content.lines().enumerate() {
            let line_1indexed = line_num + 1;

            // bs-dependencies → dependencies
            if line.contains("\"bs-dependencies\"") {
                matches.push(MigrationPatternMatch {
                    file: file.to_path_buf(),
                    line: line_1indexed,
                    pattern: "bs-dependencies".to_string(),
                    replacement: "dependencies".to_string(),
                    category: DeprecatedCategory::BsConfig,
                    severity: MigrationSeverity::Required,
                });
            }

            // bs-dev-dependencies → (remove, use package.json)
            if line.contains("\"bs-dev-dependencies\"") {
                matches.push(MigrationPatternMatch {
                    file: file.to_path_buf(),
                    line: line_1indexed,
                    pattern: "bs-dev-dependencies".to_string(),
                    replacement: "dev-dependencies or package.json devDependencies".to_string(),
                    category: DeprecatedCategory::BsConfig,
                    severity: MigrationSeverity::Required,
                });
            }

            // Old JSX version
            if line.contains("\"react-jsx\": 3") || line.contains("\"react-jsx\":3") {
                matches.push(MigrationPatternMatch {
                    file: file.to_path_buf(),
                    line: line_1indexed,
                    pattern: "react-jsx v3".to_string(),
                    replacement: "react-jsx v4".to_string(),
                    category: DeprecatedCategory::OldJsx,
                    severity: MigrationSeverity::Required,
                });
            }
        }

        // Check for absence of uncurried mode (recommended in v11+)
        if !content.contains("\"uncurried\"") {
            matches.push(MigrationPatternMatch {
                file: file.to_path_buf(),
                line: 1,
                pattern: "Missing uncurried mode".to_string(),
                replacement: "\"uncurried\": true".to_string(),
                category: DeprecatedCategory::CurriedDefault,
                severity: MigrationSeverity::Recommended,
            });
        }

        matches
    }

    /// Scan a repository directory for all migration patterns.
    ///
    /// Walks the directory looking for .res/.resi files and config files,
    /// producing a complete MigrationScanReport.
    pub fn scan_repo(target: &Path) -> MigrationScanReport {
        let mut all_patterns = Vec::new();
        let mut has_bsconfig = false;
        let mut has_rescript_json = false;

        // Check for config files at root
        let bsconfig_path = target.join("bsconfig.json");
        let rescript_json_path = target.join("rescript.json");

        if bsconfig_path.exists() {
            has_bsconfig = true;
            if let Ok(content) = std::fs::read_to_string(&bsconfig_path) {
                all_patterns.extend(Self::scan_config(&bsconfig_path, &content));
            }
        }
        if rescript_json_path.exists() {
            has_rescript_json = true;
            if let Ok(content) = std::fs::read_to_string(&rescript_json_path) {
                all_patterns.extend(Self::scan_config(&rescript_json_path, &content));
            }
        }

        // Walk source files
        if let Ok(entries) = std::fs::read_dir(target) {
            Self::walk_source_files(target, entries, &mut all_patterns);
        }

        let required_count = all_patterns
            .iter()
            .filter(|p| p.severity == MigrationSeverity::Required)
            .count();
        let recommended_count = all_patterns
            .iter()
            .filter(|p| p.severity == MigrationSeverity::Recommended)
            .count();
        let migration_clean = required_count == 0;

        MigrationScanReport {
            target: target.to_path_buf(),
            patterns: all_patterns,
            required_count,
            recommended_count,
            has_bsconfig,
            has_rescript_json,
            migration_clean,
        }
    }

    /// Recursively walk source files in a directory
    fn walk_source_files(
        _root: &Path,
        entries: std::fs::ReadDir,
        patterns: &mut Vec<MigrationPatternMatch>,
    ) {
        for entry in entries.flatten() {
            let path = entry.path();

            if path.is_dir() {
                // Skip node_modules, .git, lib (build output)
                let dir_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                if dir_name == "node_modules"
                    || dir_name == ".git"
                    || dir_name == "lib"
                    || dir_name == "_build"
                {
                    continue;
                }
                if let Ok(sub_entries) = std::fs::read_dir(&path) {
                    Self::walk_source_files(&path, sub_entries, patterns);
                }
                continue;
            }

            // Only scan ReScript source files
            let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
            if ext == "res" || ext == "resi" {
                if let Ok(content) = std::fs::read_to_string(&path) {
                    patterns.extend(Self::scan_source(&path, &content));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scan_js_deprecated_apis() {
        let source = r#"
let arr = Js.Array2.map(items, fn)
let str = Js.String2.trim(s)
let d = Js.Dict.fromArray(pairs)
Js.log("hello")
"#;
        let matches = MigrationScanner::scan_source(Path::new("test.res"), source);
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|m| m.pattern == "Js.Array2"));
        assert!(matches.iter().any(|m| m.pattern == "Js.String2"));
        assert!(matches.iter().any(|m| m.pattern == "Js.Dict"));
        assert!(matches.iter().any(|m| m.pattern == "Js.log"));
        assert!(matches
            .iter()
            .all(|m| m.severity == MigrationSeverity::Required));
    }

    #[test]
    fn test_scan_belt_deprecated_apis() {
        let source = r#"
let sorted = Belt.Array.sort(arr, cmp)
let lst = Belt.List.map(items, fn)
let opt = Belt.Option.getExn(value)
"#;
        let matches = MigrationScanner::scan_source(Path::new("test.res"), source);
        assert!(matches.iter().any(|m| m.pattern == "Belt.Array"));
        assert!(matches.iter().any(|m| m.pattern == "Belt.List"));
        assert!(matches.iter().any(|m| m.pattern == "Belt.Option"));
    }

    #[test]
    fn test_scan_modern_apis_no_match() {
        let source = r#"
let arr = Array.map(items, fn)
let str = String.trim(s)
let d = Dict.fromArray(pairs)
Console.log("hello")
"#;
        let matches = MigrationScanner::scan_source(Path::new("test.res"), source);
        assert!(
            matches.is_empty(),
            "Modern APIs should not trigger findings"
        );
    }

    #[test]
    fn test_scan_bsconfig_json() {
        let config = r#"{
  "name": "my-project",
  "bs-dependencies": ["@rescript/react"],
  "reason": {"react-jsx": 3}
}"#;
        let matches = MigrationScanner::scan_config(Path::new("bsconfig.json"), config);
        assert!(matches.iter().any(|m| m.pattern == "bsconfig.json"));
        assert!(matches.iter().any(|m| m.pattern == "bs-dependencies"));
        assert!(matches.iter().any(|m| m.pattern == "react-jsx v3"));
    }

    #[test]
    fn test_scan_rescript_json_clean() {
        let config = r#"{
  "name": "my-project",
  "dependencies": ["@rescript/react"],
  "jsx": {"version": 4},
  "uncurried": true
}"#;
        let matches = MigrationScanner::scan_config(Path::new("rescript.json"), config);
        // Should not flag bsconfig or bs-dependencies
        assert!(!matches.iter().any(|m| m.pattern == "bsconfig.json"));
        assert!(!matches.iter().any(|m| m.pattern == "bs-dependencies"));
    }

    #[test]
    fn test_scan_unsafe_coercion() {
        let source = r#"
let x = Obj.magic(someValue)
let y = %identity(otherValue)
"#;
        let matches = MigrationScanner::scan_source(Path::new("test.res"), source);
        assert!(matches
            .iter()
            .any(|m| m.category == DeprecatedCategory::UnsafeCoercion));
        assert!(matches
            .iter()
            .filter(|m| m.category == DeprecatedCategory::UnsafeCoercion)
            .all(|m| m.severity == MigrationSeverity::Recommended));
    }

    #[test]
    fn test_migration_severity_levels() {
        assert_eq!(MigrationSeverity::Required.level(), 3);
        assert_eq!(MigrationSeverity::Recommended.level(), 2);
        assert_eq!(MigrationSeverity::Info.level(), 1);
    }

    #[test]
    fn test_scan_report_summary_clean() {
        let report = MigrationScanReport {
            target: PathBuf::from("/tmp/clean-repo"),
            patterns: Vec::new(),
            required_count: 0,
            recommended_count: 0,
            has_bsconfig: false,
            has_rescript_json: true,
            migration_clean: true,
        };
        assert!(report.summary().contains("clean"));
    }

    #[test]
    fn test_scan_report_summary_with_findings() {
        let report = MigrationScanReport {
            target: PathBuf::from("/tmp/legacy-repo"),
            patterns: Vec::new(),
            required_count: 15,
            recommended_count: 3,
            has_bsconfig: true,
            has_rescript_json: false,
            migration_clean: false,
        };
        let summary = report.summary();
        assert!(summary.contains("15 required"));
        assert!(summary.contains("3 recommended"));
        assert!(summary.contains("bsconfig.json"));
    }
}
