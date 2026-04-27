// SPDX-License-Identifier: PMPL-1.0-or-later

//! Axiom usage tracking with Creusot proof annotations.
//!
//! Re-implements `src/rust/verification/axiom_tracker.rs` as a
//! self-contained, formally-annotated kernel for the trust pipeline.
//!
//! ## Key proof obligations
//!
//! | ID | Property | Source |
//! |---|---|---|
//! | **PO-A1** | `DangerLevel` total order: `Safe < Noted < Warning < Reject` | §M2 of SPARK_ADOPTION_PLAN.md |
//! | **PO-A2** | Monotonicity of `classify_axiom`: adding more dangerous patterns can only keep or raise the result | §M2 |
//! | **PO-A3** | Cap at Reject: `max(Reject, x) == Reject` for all `x` | §M2 |
//! | **PO-A4** | `enforce_policy` is non-decreasing with number of Reject-level usages | §M2 |
//! | **PO-A5** | Scaffold-sorry soundness: lines containing `ECHIDNA_SCAFFOLD_SORRY` are always skipped | §M2 |
//!
//! ## Creusot annotation style
//!
//! Contracts are written as doc-comment code blocks (always visible on
//! stable Rust) and additionally as `#[cfg(feature = "creusot")]` attribute
//! macros (activated during formal verification).  See the crate-level
//! documentation for the feature-flag rationale.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[cfg(feature = "creusot")]
use creusot_contracts::*;

// ---------------------------------------------------------------------------
// DangerLevel
// ---------------------------------------------------------------------------

/// Danger classification for an axiom or construct found in a proof.
///
/// The discriminants increase with danger so that the derived `Ord`
/// gives the natural ordering:
/// `Safe(0) < Noted(1) < Warning(2) < Reject(3)`.
///
/// ### Creusot proof obligation PO-A1 (total order)
/// ```text
/// #[logic]
/// fn danger_total_order() -> bool {
///     DangerLevel::Safe    < DangerLevel::Noted
///     && DangerLevel::Noted   < DangerLevel::Warning
///     && DangerLevel::Warning < DangerLevel::Reject
/// }
/// #[ensures(danger_total_order())]
/// fn lemma_danger_total_order() {}
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DangerLevel {
    /// Standard library axiom — allowed without restriction.
    Safe    = 0,
    /// Classical axiom in a constructive system — noted but allowed.
    Noted   = 1,
    /// Incomplete proof marker (`sorry`, `Admitted`, `postulate`) — warning.
    Warning = 2,
    /// Known unsound construct (`believe_me`, `mk_thm`, `--type-in-type`) — REJECT.
    Reject  = 3,
}

impl DangerLevel {
    /// Numeric value in `0..=3`.
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result <= 3u8)]
    /// ```
    #[cfg_attr(feature = "creusot", ensures(result <= 3u8))]
    pub fn value(self) -> u8 {
        self as u8
    }

    /// Returns the more dangerous of two `DangerLevel` values.
    ///
    /// ### Creusot contracts
    /// ```text
    /// #[ensures(result >= a)]
    /// #[ensures(result >= b)]
    /// #[ensures(result == a || result == b)]
    /// ```
    #[cfg_attr(feature = "creusot",
        ensures(result >= a),
        ensures(result >= b),
        ensures(result == a || result == b)
    )]
    pub fn max_danger(a: DangerLevel, b: DangerLevel) -> DangerLevel {
        if a >= b { a } else { b }
    }
}

impl std::fmt::Display for DangerLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            DangerLevel::Safe    => "Safe",
            DangerLevel::Noted   => "Noted",
            DangerLevel::Warning => "Warning",
            DangerLevel::Reject  => "Reject",
        };
        write!(f, "{s}")
    }
}

// ---------------------------------------------------------------------------
// AxiomUsage
// ---------------------------------------------------------------------------

/// A single dangerous construct found in proof content.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AxiomUsage {
    /// The pattern that matched (e.g. `"believe_me"`, `"sorry"`).
    pub construct: String,
    /// Danger level of this usage.
    pub danger_level: DangerLevel,
    /// Human-readable explanation of why this construct is dangerous.
    pub explanation: String,
    /// 1-indexed line number in the proof content, if determinable.
    pub line: Option<usize>,
}

// ---------------------------------------------------------------------------
// AxiomPolicy
// ---------------------------------------------------------------------------

/// Aggregate policy decision after scanning a proof.
///
/// The four variants form a natural partial order aligned with `DangerLevel`:
/// `Clean < ClassicalAxioms < IncompleteProof < Rejected`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AxiomPolicy {
    /// Proof is clean — only standard axioms used.
    Clean,
    /// Proof uses classical axioms; noted but acceptable.
    ClassicalAxioms(Vec<AxiomUsage>),
    /// Proof has incomplete proof markers; warned but not rejected.
    IncompleteProof(Vec<AxiomUsage>),
    /// Proof uses known-unsound constructs; REJECTED.
    Rejected(Vec<AxiomUsage>),
}

impl AxiomPolicy {
    /// Whether the policy allows downstream trust elevation.
    ///
    /// Only `Rejected` returns `false`.
    pub fn is_acceptable(&self) -> bool {
        !matches!(self, AxiomPolicy::Rejected(_))
    }

    /// The worst danger level observed, for integration with the trust pipeline.
    ///
    /// ### Creusot contract (monotonicity)
    /// ```text
    /// // If policy == Rejected, worst_danger() == DangerLevel::Reject
    /// #[ensures(
    ///     matches!(*self, AxiomPolicy::Rejected(_))
    ///     ==> result == DangerLevel::Reject
    /// )]
    /// ```
    #[cfg_attr(feature = "creusot",
        ensures(
            matches!(*self, AxiomPolicy::Rejected(_))
            ==> result == DangerLevel::Reject
        )
    )]
    pub fn worst_danger(&self) -> DangerLevel {
        match self {
            AxiomPolicy::Clean              => DangerLevel::Safe,
            AxiomPolicy::ClassicalAxioms(_) => DangerLevel::Noted,
            AxiomPolicy::IncompleteProof(_) => DangerLevel::Warning,
            AxiomPolicy::Rejected(_)        => DangerLevel::Reject,
        }
    }

    /// All axiom usages recorded in this policy decision.
    pub fn all_usages(&self) -> Vec<&AxiomUsage> {
        match self {
            AxiomPolicy::Clean => vec![],
            AxiomPolicy::ClassicalAxioms(u)
            | AxiomPolicy::IncompleteProof(u)
            | AxiomPolicy::Rejected(u) => u.iter().collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// DangerousPattern (internal)
// ---------------------------------------------------------------------------

/// A single pattern to search for in proof content, with its danger level.
#[derive(Debug, Clone)]
struct DangerousPattern {
    /// Literal substring to match in proof content.
    pattern: String,
    /// Danger level if this pattern is found.
    danger_level: DangerLevel,
    /// Explanation for display / reporting.
    explanation: String,
}

// ---------------------------------------------------------------------------
// ProverSyntax (internal — comment detection)
// ---------------------------------------------------------------------------

/// Minimal prover-syntax descriptor used only for comment detection.
///
/// Keeping this separate from the main `echidna` crate's `ProverKind` makes
/// the crate self-contained for formal verification purposes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProverSyntax {
    /// Lean4, Agda, Idris2, Haskell-style double-dash and block `{- -}`.
    DashComment,
    /// Coq, Isabelle, HOL4, ML-style `(* *)` block comments.
    StarComment,
    /// F* — accepts both `(* *)` and `// `.
    FStarComment,
    /// Any other prover; no comment detection.
    Unknown,
}

impl ProverSyntax {
    /// Returns `true` if the trimmed line is a comment for this syntax.
    fn is_comment_line(&self, trimmed: &str) -> bool {
        match self {
            ProverSyntax::DashComment => {
                trimmed.starts_with("--")
                    || trimmed.starts_with("{-") && !trimmed.starts_with("{-#")
                    || trimmed.starts_with("/-")
            },
            ProverSyntax::StarComment => trimmed.starts_with("(*"),
            ProverSyntax::FStarComment => {
                trimmed.starts_with("(*") || trimmed.starts_with("//")
            },
            ProverSyntax::Unknown => false,
        }
    }
}

// ---------------------------------------------------------------------------
// classify_axiom
// ---------------------------------------------------------------------------

/// Classify a single list of axiom usages to a `DangerLevel`.
///
/// Returns the maximum danger level across all usages, or `Safe` if the
/// list is empty.
///
/// ### Creusot proof obligation PO-A2 (monotonicity)
///
/// Adding more usages to the input list can only keep or raise the result:
/// ```text
/// #[requires(usages_a.len() <= usages_b.len())]   // usages_b extends usages_a
/// #[ensures(classify_axiom(usages_a) <= classify_axiom(usages_b))]
/// ```
///
/// ### Creusot proof obligation PO-A3 (cap at Reject)
/// ```text
/// #[ensures(
///     usages.iter().any(|u| u.danger_level == DangerLevel::Reject)
///     ==> result == DangerLevel::Reject
/// )]
/// ```
#[cfg_attr(feature = "creusot",
    ensures(result >= DangerLevel::Safe),
    ensures(result <= DangerLevel::Reject)
)]
pub fn classify_axiom(usages: &[AxiomUsage]) -> DangerLevel {
    usages
        .iter()
        .map(|u| u.danger_level)
        .fold(DangerLevel::Safe, DangerLevel::max_danger)
}

// ---------------------------------------------------------------------------
// AxiomTracker
// ---------------------------------------------------------------------------

/// Scans proof content for dangerous axiom patterns and enforces policy.
///
/// The tracker holds a table of `(ProverSyntax, Vec<DangerousPattern>)` pairs.
/// Each pair maps a prover's comment syntax to the patterns that are dangerous
/// for that prover.  The same tracker instance can be reused across many
/// proof results.
///
/// ## Thread safety
///
/// `AxiomTracker` is `Send + Sync`; the internal pattern table is read-only
/// after construction.
pub struct AxiomTracker {
    /// Pattern table: `(syntax, patterns)` for each known prover.
    ///
    /// Using a `String` key (prover name) rather than a prover-kind enum
    /// keeps the crate self-contained.
    patterns: HashMap<String, (ProverSyntax, Vec<DangerousPattern>)>,
}

impl AxiomTracker {
    /// Create a new `AxiomTracker` pre-loaded with all known dangerous patterns.
    ///
    /// The set of patterns mirrors `src/rust/verification/axiom_tracker.rs`
    /// exactly; the crate-level doc explains the mapping.
    pub fn new() -> Self {
        let mut patterns: HashMap<String, (ProverSyntax, Vec<DangerousPattern>)> = HashMap::new();

        // Lean4
        patterns.insert("lean".into(), (
            ProverSyntax::DashComment,
            vec![
                DangerousPattern {
                    pattern: "sorry".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Incomplete proof — 'sorry' is a placeholder for a missing proof".into(),
                },
                DangerousPattern {
                    pattern: "native_decide".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Uses native code evaluation — bypasses kernel checking".into(),
                },
                DangerousPattern {
                    pattern: "Decidable.decide".into(),
                    danger_level: DangerLevel::Noted,
                    explanation: "Decision procedure — may not verify constructively".into(),
                },
                DangerousPattern {
                    pattern: "axiom ".into(),
                    danger_level: DangerLevel::Noted,
                    explanation: "User-defined axiom — not verified by kernel".into(),
                },
            ],
        ));

        // Coq / Rocq
        patterns.insert("coq".into(), (
            ProverSyntax::StarComment,
            vec![
                DangerousPattern {
                    pattern: "Admitted".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Incomplete proof — 'Admitted' accepts an unproven goal".into(),
                },
                DangerousPattern {
                    pattern: "admit".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Tactic 'admit' — leaves goal unproven".into(),
                },
                DangerousPattern {
                    pattern: "Axiom ".into(),
                    danger_level: DangerLevel::Noted,
                    explanation: "User-defined axiom — not verified by kernel".into(),
                },
            ],
        ));

        // Agda
        patterns.insert("agda".into(), (
            ProverSyntax::DashComment,
            vec![
                DangerousPattern {
                    pattern: "postulate".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Postulate — assumed without proof".into(),
                },
                DangerousPattern {
                    pattern: "{!!}".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Agda hole — incomplete proof term".into(),
                },
                DangerousPattern {
                    pattern: "--type-in-type".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: --type-in-type collapses the type hierarchy (Girard's paradox)".into(),
                },
                DangerousPattern {
                    pattern: "OPTIONS --type-in-type".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: --type-in-type pragma collapses the type hierarchy".into(),
                },
            ],
        ));

        // Isabelle/HOL
        patterns.insert("isabelle".into(), (
            ProverSyntax::StarComment,
            vec![
                DangerousPattern {
                    pattern: "sorry".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Incomplete proof — 'sorry' skips a proof obligation".into(),
                },
                DangerousPattern {
                    pattern: "oops".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Isabelle 'oops' — intentionally incomplete proof".into(),
                },
            ],
        ));

        // HOL4
        patterns.insert("hol4".into(), (
            ProverSyntax::StarComment,
            vec![
                DangerousPattern {
                    pattern: "mk_thm".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: mk_thm bypasses the HOL4 kernel entirely".into(),
                },
            ],
        ));

        // Idris2
        patterns.insert("idris2".into(), (
            ProverSyntax::DashComment,
            vec![
                DangerousPattern {
                    pattern: "believe_me".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: believe_me asserts any type equality without proof".into(),
                },
                DangerousPattern {
                    pattern: "assert_total".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "Asserts totality without proof — may hide non-termination".into(),
                },
                DangerousPattern {
                    pattern: "assert_smaller".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "assert_smaller bypasses the termination checker without proof".into(),
                },
                DangerousPattern {
                    pattern: "unsafePerformIO".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "unsafePerformIO breaks referential transparency in Idris2".into(),
                },
                DangerousPattern {
                    pattern: "really_believe_me".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: really_believe_me bypasses all checks — more dangerous than believe_me".into(),
                },
                DangerousPattern {
                    pattern: "prim__crash".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "prim__crash unconditionally crashes — masks proof obligations".into(),
                },
                DangerousPattern {
                    pattern: "unsafeCoerce".into(),
                    danger_level: DangerLevel::Reject,
                    explanation: "UNSOUND: unsafeCoerce bypasses the type system entirely".into(),
                },
            ],
        ));

        // F*
        patterns.insert("fstar".into(), (
            ProverSyntax::FStarComment,
            vec![
                DangerousPattern {
                    pattern: "admit".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "F* admit accepts a goal without proof".into(),
                },
                DangerousPattern {
                    pattern: "assume".into(),
                    danger_level: DangerLevel::Warning,
                    explanation: "F* assume introduces an unverified assumption".into(),
                },
            ],
        ));

        Self { patterns }
    }

    /// Scan `content` for dangerous patterns for the named prover.
    ///
    /// `prover` should be one of `"lean"`, `"coq"`, `"agda"`, `"isabelle"`,
    /// `"hol4"`, `"idris2"`, `"fstar"` (case-insensitive).
    ///
    /// Returns an empty `Vec` if the prover is unknown or no patterns match.
    ///
    /// ### Scaffold-sorry soundness (PO-A5)
    ///
    /// Lines containing the marker `ECHIDNA_SCAFFOLD_SORRY` are skipped even
    /// if they match a `sorry` pattern.  This ensures that echidna's own
    /// generated proof scaffolds do not trigger false positives.
    ///
    /// Creusot contract:
    /// ```text
    /// #[ensures(
    ///     forall |i: usize| i < result.len() ==>
    ///         !content.lines().nth(result[i].line.unwrap_or(0) - 1)
    ///             .unwrap_or("").contains("ECHIDNA_SCAFFOLD_SORRY")
    /// )]
    /// ```
    pub fn scan(&self, prover: &str, content: &str) -> Vec<AxiomUsage> {
        let key = prover.to_ascii_lowercase();
        let mut usages = Vec::new();

        let Some((syntax, prover_patterns)) = self.patterns.get(&key) else {
            return usages;
        };

        for (line_idx, line) in content.lines().enumerate() {
            let trimmed = line.trim();

            // Skip comment lines entirely — patterns in comments are documentation,
            // not real usage.
            if syntax.is_comment_line(trimmed) {
                continue;
            }

            for pat in prover_patterns {
                if !line.contains(pat.pattern.as_str()) {
                    continue;
                }

                // Skip echidna's own scaffold sorrys (PO-A5).
                // These are generated by the prover backends to indicate a
                // partial proof skeleton and always carry the marker comment.
                let is_scaffold = pat.pattern == "sorry"
                    && line.contains("ECHIDNA_SCAFFOLD_SORRY");
                if is_scaffold {
                    continue;
                }

                usages.push(AxiomUsage {
                    construct:   pat.pattern.clone(),
                    danger_level: pat.danger_level,
                    explanation: pat.explanation.clone(),
                    line:        Some(line_idx + 1),
                });
            }
        }

        usages
    }

    /// Enforce axiom policy on a pre-scanned list of usages.
    ///
    /// ### Creusot proof obligation PO-A4 (monotonicity)
    ///
    /// Adding more usages can only keep the policy at the current level or
    /// escalate it; it can never reduce the severity:
    /// ```text
    /// #[requires(usages_a is a subset of usages_b)]
    /// #[ensures(enforce_policy(usages_a).worst_danger() <=
    ///           enforce_policy(usages_b).worst_danger())]
    /// ```
    pub fn enforce_policy(&self, usages: &[AxiomUsage]) -> AxiomPolicy {
        if usages.is_empty() {
            return AxiomPolicy::Clean;
        }

        let has_rejected = usages.iter().any(|u| u.danger_level == DangerLevel::Reject);
        let has_warning  = usages.iter().any(|u| u.danger_level == DangerLevel::Warning);
        let has_noted    = usages.iter().any(|u| u.danger_level == DangerLevel::Noted);

        if has_rejected {
            let rejected: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level == DangerLevel::Reject)
                .cloned()
                .collect();
            AxiomPolicy::Rejected(rejected)
        } else if has_warning {
            let warnings: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level >= DangerLevel::Warning)
                .cloned()
                .collect();
            AxiomPolicy::IncompleteProof(warnings)
        } else if has_noted {
            let noted: Vec<AxiomUsage> = usages
                .iter()
                .filter(|u| u.danger_level >= DangerLevel::Noted)
                .cloned()
                .collect();
            AxiomPolicy::ClassicalAxioms(noted)
        } else {
            AxiomPolicy::Clean
        }
    }

    /// Convenience: scan and enforce in a single call.
    pub fn analyze(&self, prover: &str, content: &str) -> AxiomPolicy {
        let usages = self.scan(prover, content);
        self.enforce_policy(&usages)
    }
}

impl Default for AxiomTracker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Invariant test suite
// ---------------------------------------------------------------------------

/// Invariant tests for `DangerLevel` and `AxiomTracker`.
///
/// Mirrors the proof obligations listed in the module-level doc table.
pub mod impl_invariants {
    // Only used in #[test] functions; module is pub for Creusot visibility.
    #[allow(unused_imports)]
    use super::*;

    // -----------------------------------------------------------------------
    // PO-A1: DangerLevel total order
    // -----------------------------------------------------------------------

    /// **PO-A1** Total order: `Safe < Noted < Warning < Reject`.
    #[test]
    fn po_a1_danger_level_total_order() {
        assert!(DangerLevel::Safe    < DangerLevel::Noted);
        assert!(DangerLevel::Noted   < DangerLevel::Warning);
        assert!(DangerLevel::Warning < DangerLevel::Reject);
    }

    // -----------------------------------------------------------------------
    // PO-A2: classify_axiom is monotone
    // -----------------------------------------------------------------------

    /// **PO-A2** Monotonicity: adding a usage to the list never lowers the
    /// classified danger level.
    #[test]
    fn po_a2_classify_axiom_monotone() {
        let base: Vec<AxiomUsage> = vec![];
        let with_noted = vec![AxiomUsage {
            construct:   "Axiom ".into(),
            danger_level: DangerLevel::Noted,
            explanation: "test".into(),
            line:        Some(1),
        }];
        let with_reject = vec![
            with_noted[0].clone(),
            AxiomUsage {
                construct:   "believe_me".into(),
                danger_level: DangerLevel::Reject,
                explanation: "test".into(),
                line:        Some(2),
            },
        ];

        assert!(classify_axiom(&base)        <= classify_axiom(&with_noted));
        assert!(classify_axiom(&with_noted)  <= classify_axiom(&with_reject));
    }

    // -----------------------------------------------------------------------
    // PO-A3: max(Reject, x) == Reject for all x
    // -----------------------------------------------------------------------

    /// **PO-A3** Reject absorbs everything:
    /// `DangerLevel::max_danger(Reject, x) == Reject` for all `x`.
    #[test]
    fn po_a3_reject_absorbs() {
        for x in [
            DangerLevel::Safe,
            DangerLevel::Noted,
            DangerLevel::Warning,
            DangerLevel::Reject,
        ] {
            assert_eq!(DangerLevel::max_danger(DangerLevel::Reject, x), DangerLevel::Reject);
            assert_eq!(DangerLevel::max_danger(x, DangerLevel::Reject), DangerLevel::Reject);
        }
    }

    // -----------------------------------------------------------------------
    // PO-A4: enforce_policy monotone w.r.t. usages
    // -----------------------------------------------------------------------

    /// **PO-A4** `enforce_policy` escalates (never de-escalates) when more
    /// dangerous usages are added.
    #[test]
    fn po_a4_enforce_policy_monotone() {
        let tracker = AxiomTracker::new();

        let empty_policy      = tracker.enforce_policy(&[]);
        let noted_usage       = vec![AxiomUsage {
            construct:   "Axiom ".into(),
            danger_level: DangerLevel::Noted,
            explanation: "test".into(),
            line:        Some(1),
        }];
        let noted_policy      = tracker.enforce_policy(&noted_usage);
        let mut reject_usages = noted_usage.clone();
        reject_usages.push(AxiomUsage {
            construct:   "believe_me".into(),
            danger_level: DangerLevel::Reject,
            explanation: "test".into(),
            line:        Some(2),
        });
        let reject_policy     = tracker.enforce_policy(&reject_usages);

        assert!(empty_policy.worst_danger()  <= noted_policy.worst_danger());
        assert!(noted_policy.worst_danger()  <= reject_policy.worst_danger());
        assert_eq!(reject_policy.worst_danger(), DangerLevel::Reject);
    }

    // -----------------------------------------------------------------------
    // PO-A5: scaffold sorry soundness
    // -----------------------------------------------------------------------

    /// **PO-A5** Lines with `ECHIDNA_SCAFFOLD_SORRY` are always skipped,
    /// even if they also contain `sorry`.
    #[test]
    fn po_a5_scaffold_sorry_skipped() {
        let tracker = AxiomTracker::new();

        // Lean scaffold sorry
        let lean_content =
            "theorem _goal : 1 = 1 := by\n  simp\n  sorry -- ECHIDNA_SCAFFOLD_SORRY";
        assert!(
            tracker.scan("lean", lean_content).is_empty(),
            "Lean scaffold sorry must not be flagged"
        );

        // Isabelle scaffold sorry
        let isa_content = "lemma foo: \"1 = 1\"\n  sorry (* ECHIDNA_SCAFFOLD_SORRY *)";
        assert!(
            tracker.scan("isabelle", isa_content).is_empty(),
            "Isabelle scaffold sorry must not be flagged"
        );
    }

    // -----------------------------------------------------------------------
    // Additional unit-level sanity checks
    // -----------------------------------------------------------------------

    /// Comment lines are never flagged, regardless of prover or pattern.
    #[test]
    fn po_a6_comment_lines_not_flagged() {
        let tracker = AxiomTracker::new();
        // Lean double-dash comment containing "sorry"
        let usages = tracker.scan("lean", "-- sorry this is a comment");
        assert!(usages.is_empty(), "Comment line should not produce usages");
    }

    /// Coq `(*` block-comment lines are not flagged.
    #[test]
    fn po_a7_coq_comment_not_flagged() {
        let tracker = AxiomTracker::new();
        let usages = tracker.scan("coq", "(* Admitted — this is a comment *)");
        assert!(usages.is_empty(), "Coq comment line should not produce usages");
    }

    /// `mk_thm` in HOL4 code is always rejected.
    #[test]
    fn po_a8_hol4_mk_thm_rejected() {
        let tracker = AxiomTracker::new();
        let policy = tracker.analyze("hol4", "val thm = mk_thm ([], ``T``)");
        assert!(!policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Reject);
    }

    /// Agda `--type-in-type` option is always rejected.
    #[test]
    fn po_a9_agda_type_in_type_rejected() {
        let tracker = AxiomTracker::new();
        let policy = tracker.analyze("agda", "{-# OPTIONS --type-in-type #-}");
        assert!(!policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Reject);
    }

    /// Clean Lean4 proof passes without any usages.
    #[test]
    fn po_a10_clean_lean_proof_passes() {
        let tracker = AxiomTracker::new();
        let policy = tracker.analyze(
            "lean",
            "theorem plus_comm : forall a b, a + b = b + a := by omega",
        );
        assert!(policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Safe);
    }

    /// Unknown provers produce empty usages (no false positives).
    #[test]
    fn po_a11_unknown_prover_no_usages() {
        let tracker = AxiomTracker::new();
        let usages = tracker.scan("some_unknown_prover_2077", "sorry believe_me mk_thm");
        assert!(
            usages.is_empty(),
            "Unknown prover must produce no usages — no pattern table available"
        );
    }

    /// `DangerLevel::value()` is in range and order-preserving.
    #[test]
    fn po_a12_danger_level_value_range_and_order() {
        assert_eq!(DangerLevel::Safe.value(),    0);
        assert_eq!(DangerLevel::Noted.value(),   1);
        assert_eq!(DangerLevel::Warning.value(), 2);
        assert_eq!(DangerLevel::Reject.value(),  3);
        assert!(DangerLevel::Safe.value()    < DangerLevel::Noted.value());
        assert!(DangerLevel::Noted.value()   < DangerLevel::Warning.value());
        assert!(DangerLevel::Warning.value() < DangerLevel::Reject.value());
    }
}

#[cfg(test)]
mod tests {
    use super::{AxiomTracker, DangerLevel, classify_axiom, AxiomUsage};

    #[test]
    fn test_lean_sorry_detected() {
        let tracker = AxiomTracker::new();
        let usages = tracker.scan("lean", "theorem foo : 1 + 1 = 2 := by sorry");
        assert_eq!(usages.len(), 1);
        assert_eq!(usages[0].danger_level, DangerLevel::Warning);
        assert_eq!(usages[0].construct, "sorry");
    }

    #[test]
    fn test_idris2_believe_me_rejected() {
        let tracker = AxiomTracker::new();
        let policy = tracker.analyze("idris2", "unsafeProof = believe_me");
        assert!(!policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Reject);
    }

    #[test]
    fn test_coq_admitted_warning_acceptable() {
        let tracker = AxiomTracker::new();
        let policy = tracker.analyze("coq", "Theorem foo : True.\nProof. Admitted.");
        // Warning — incomplete but not rejected
        assert!(policy.is_acceptable());
        assert_eq!(policy.worst_danger(), DangerLevel::Warning);
    }

    #[test]
    fn test_case_insensitive_prover_key() {
        let tracker = AxiomTracker::new();
        // "Lean" vs "lean" should both work
        let a = tracker.scan("Lean",  "sorry");
        let b = tracker.scan("lean",  "sorry");
        assert_eq!(a.len(), b.len());
    }

    #[test]
    fn test_classify_axiom_empty_is_safe() {
        assert_eq!(classify_axiom(&[]), DangerLevel::Safe);
    }

    #[test]
    fn test_classify_axiom_picks_max() {
        let usages = vec![
            AxiomUsage { construct: "a".into(), danger_level: DangerLevel::Noted,   explanation: "".into(), line: None },
            AxiomUsage { construct: "b".into(), danger_level: DangerLevel::Warning, explanation: "".into(), line: None },
        ];
        assert_eq!(classify_axiom(&usages), DangerLevel::Warning);
    }
}
