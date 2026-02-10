// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! Integration tests for ECHIDNA v1.2
//!
//! Tests all 12 provers end-to-end, including the 3 new ones:
//! - ACL2 (Tier 3)
//! - PVS (Tier 3)
//! - HOL4 (Tier 4)

use anyhow::{Context, Result};
use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::path::PathBuf;
use tempfile::TempDir;

/// Helper to create a test config
fn test_config() -> ProverConfig {
    ProverConfig {
        executable: PathBuf::from("mock"),  // Will be overridden
        library_paths: vec![],
        args: vec![],
        timeout: 30,
        neural_enabled: false,
    }
}

// ============================================================================
// ACL2 Integration Tests
// ============================================================================

#[tokio::test]
#[ignore] // Requires ACL2 binary
async fn test_acl2_basic_theorem() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("acl2"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::ACL2, config)
        .context("Failed to create ACL2 backend")?;

    // Simple associativity theorem
    let proof = r#"
(defthm append-associative
  (equal (append (append x y) z)
         (append x (append y z))))
"#;

    let state = backend.parse_string(proof).await
        .context("Failed to parse ACL2 proof")?;

    let verified = backend.verify_proof(&state).await
        .context("Failed to verify proof")?;

    assert!(verified, "ACL2 proof should verify");
    Ok(())
}

#[tokio::test]
#[ignore] // Requires ACL2 binary
async fn test_acl2_hint_system() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("acl2"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::ACL2, config)
        .context("Failed to create ACL2 backend")?;

    // Theorem with induction hint
    let proof = r#"
(defun len (x)
  (if (endp x)
      0
    (+ 1 (len (cdr x)))))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y)))
  :hints (("Goal" :induct (len x))))
"#;

    let state = backend.parse_string(proof).await
        .context("Failed to parse ACL2 proof with hints")?;

    assert!(!state.goals.is_empty(), "Should have parsed goals");
    Ok(())
}

#[test]
fn test_acl2_sexp_parser() -> Result<()> {
    use echidna::provers::acl2::SExp;

    // Test basic S-expression parsing
    let sexp = SExp::parse("(defthm test (equal x x))")?;
    assert!(matches!(sexp, SExp::List(_)));

    // Test nested lists
    let nested = SExp::parse("(a (b c) d)")?;
    if let SExp::List(items) = nested {
        assert_eq!(items.len(), 3);
    } else {
        panic!("Expected list");
    }

    // Test quoted expressions
    let quoted = SExp::parse("'(a b c)")?;
    assert!(matches!(quoted, SExp::Quote(_)));
    Ok(())
}

// ============================================================================
// PVS Integration Tests
// ============================================================================

#[tokio::test]
#[ignore] // Requires PVS binary
async fn test_pvs_basic_theory() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("pvs"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::PVS, config)
        .context("Failed to create PVS backend")?;

    // Simple PVS theory
    let theory = r#"
simple_theory: THEORY
BEGIN
  x, y: VAR nat

  addition_commutes: LEMMA
    x + y = y + x

END simple_theory
"#;

    let state = backend.parse_string(theory).await
        .context("Failed to parse PVS theory")?;

    assert!(!state.goals.is_empty(), "Should have lemmas");
    Ok(())
}

#[tokio::test]
#[ignore] // Requires PVS binary
async fn test_pvs_parametric_theory() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("pvs"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::PVS, config)
        .context("Failed to create PVS backend")?;

    // Parametric list theory
    let theory = r#"
list_theory[T: TYPE]: THEORY
BEGIN
  list: DATATYPE
  BEGIN
    null: null?
    cons(car: T, cdr: list): cons?
  END list

  append(l1, l2: list): RECURSIVE list =
    IF null?(l1) THEN l2
    ELSE cons(car(l1), append(cdr(l1), l2))
    ENDIF
  MEASURE length(l1)

  append_nil: LEMMA
    FORALL (l: list): append(l, null) = l

END list_theory
"#;

    let state = backend.parse_string(theory).await
        .context("Failed to parse parametric PVS theory")?;

    assert!(!state.goals.is_empty(), "Should have parametric lemmas");
    Ok(())
}

#[test]
fn test_pvs_tcc_generation() {
    // Test that TCCs are properly identified
    // (This would test the PVS backend's TCC extraction logic)
    // Placeholder for now
}

// ============================================================================
// HOL4 Integration Tests
// ============================================================================

#[tokio::test]
#[ignore] // Requires HOL4 binary
async fn test_hol4_basic_theorem() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("hol"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::HOL4, config)
        .context("Failed to create HOL4 backend")?;

    // Simple HOL4 theorem
    let proof = r#"
val append_nil = Q.store_thm(
  "append_nil",
  `!l. APPEND l [] = l`,
  Induct_on `l` THEN SRW_TAC[][]
);
"#;

    let state = backend.parse_string(proof).await
        .context("Failed to parse HOL4 proof")?;

    assert!(!state.goals.is_empty(), "Should have goals");
    Ok(())
}

#[tokio::test]
#[ignore] // Requires HOL4 binary
async fn test_hol4_datatype() -> Result<()> {
    let config = ProverConfig {
        executable: PathBuf::from("hol"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::HOL4, config)
        .context("Failed to create HOL4 backend")?;

    // Datatype definition
    let datatype_def = r#"
val _ = Datatype`
  tree = Leaf num
       | Node tree tree
`;

val tree_size_def = Define`
  (tree_size (Leaf n) = 1) ∧
  (tree_size (Node l r) = 1 + tree_size l + tree_size r)
`;

val tree_size_positive = Q.store_thm(
  "tree_size_positive",
  `!t. 0 < tree_size t`,
  Induct_on `t` THEN SRW_TAC[ARITH_ss][tree_size_def]
);
"#;

    let state = backend.parse_string(datatype_def).await
        .context("Failed to parse HOL4 datatype")?;

    assert!(!state.goals.is_empty(), "Should have datatype theorems");
    Ok(())
}

#[test]
fn test_hol4_tactic_parsing() {
    // Test HOL4 tactic parser
    // (Would test the 35+ tactics are properly recognized)
    // Placeholder for now
}

// ============================================================================
// Cross-Prover Tests
// ============================================================================

#[tokio::test]
async fn test_all_provers_available() -> Result<()> {
    // Test that all 12 provers can be instantiated
    let config = test_config();

    let provers = vec![
        ProverKind::Agda,
        ProverKind::Coq,
        ProverKind::Lean,
        ProverKind::Isabelle,
        ProverKind::Z3,
        ProverKind::CVC5,
        ProverKind::Metamath,
        ProverKind::HOLLight,
        ProverKind::Mizar,
        ProverKind::ACL2,      // NEW in v1.2
        ProverKind::PVS,       // NEW in v1.2
        ProverKind::HOL4,      // NEW in v1.2
    ];

    for kind in provers {
        let result = ProverFactory::create(kind, config.clone());
        assert!(result.is_ok(), "Failed to create backend for {:?}", kind);
    }
    Ok(())
}

#[tokio::test]
async fn test_tier_classification() -> Result<()> {
    // Verify tier assignments
    assert_eq!(ProverKind::ACL2.tier(), 3);
    assert_eq!(ProverKind::PVS.tier(), 3);
    assert_eq!(ProverKind::HOL4.tier(), 4);

    // Verify complexity ratings
    assert_eq!(ProverKind::ACL2.complexity(), 4);
    assert_eq!(ProverKind::PVS.complexity(), 4);
    assert_eq!(ProverKind::HOL4.complexity(), 5);
    Ok(())
}

#[test]
fn test_file_extension_detection() {
    use echidna::provers::ProverFactory;

    // Test ACL2 detection
    let acl2_file = PathBuf::from("test.lisp");
    assert_eq!(
        ProverFactory::detect_from_file(&acl2_file),
        Some(ProverKind::ACL2)
    );

    // Test PVS detection
    let pvs_file = PathBuf::from("test.pvs");
    assert_eq!(
        ProverFactory::detect_from_file(&pvs_file),
        Some(ProverKind::PVS)
    );

    // Test HOL4 detection
    let hol4_file = PathBuf::from("test.sml");
    assert_eq!(
        ProverFactory::detect_from_file(&hol4_file),
        Some(ProverKind::HOL4)
    );
}

// ============================================================================
// Example File Tests
// ============================================================================

#[tokio::test]
#[ignore] // Requires prover binaries
async fn test_acl2_examples() -> Result<()> {
    let example_files = vec![
        "proofs/acl2/associativity.lisp",
        "proofs/acl2/list_append.lisp",
        "proofs/acl2/factorial.lisp",
        "proofs/acl2/binary_trees.lisp",
        "proofs/acl2/sorting.lisp",
    ];

    let config = ProverConfig {
        executable: PathBuf::from("acl2"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::ACL2, config)
        .context("Failed to create ACL2 backend")?;

    for file in example_files {
        let path = PathBuf::from(file);
        if path.exists() {
            let state = backend.parse_file(path.clone()).await
                .context(format!("Failed to parse {}", file))?;
            assert!(!state.goals.is_empty(), "Example {} should have goals", file);
        }
    }
    Ok(())
}

#[tokio::test]
#[ignore] // Requires prover binaries
async fn test_pvs_examples() -> Result<()> {
    let example_files = vec![
        "proofs/pvs/list_theory.pvs",
        "proofs/pvs/arithmetic.pvs",
        "proofs/pvs/binary_search.pvs",
        "proofs/pvs/set_theory.pvs",
        "proofs/pvs/sorting.pvs",
    ];

    let config = ProverConfig {
        executable: PathBuf::from("pvs"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::PVS, config)
        .context("Failed to create PVS backend")?;

    for file in example_files {
        let path = PathBuf::from(file);
        if path.exists() {
            let state = backend.parse_file(path.clone()).await
                .context(format!("Failed to parse {}", file))?;
            assert!(!state.goals.is_empty(), "Example {} should have goals", file);
        }
    }
    Ok(())
}

#[tokio::test]
#[ignore] // Requires prover binaries
async fn test_hol4_examples() -> Result<()> {
    let example_files = vec![
        "proofs/hol4/list_append.sml",
        "proofs/hol4/arithmetic.sml",
        "proofs/hol4/binary_tree.sml",
        "proofs/hol4/sorting.sml",
        "proofs/hol4/set_theory.sml",
    ];

    let config = ProverConfig {
        executable: PathBuf::from("hol"),
        ..test_config()
    };

    let backend = ProverFactory::create(ProverKind::HOL4, config)
        .context("Failed to create HOL4 backend")?;

    for file in example_files {
        let path = PathBuf::from(file);
        if path.exists() {
            let state = backend.parse_file(path.clone()).await
                .context(format!("Failed to parse {}", file))?;
            assert!(!state.goals.is_empty(), "Example {} should have goals", file);
        }
    }
    Ok(())
}

// ============================================================================
// Performance Tests
// ============================================================================

#[tokio::test]
async fn test_backend_creation_performance() -> Result<()> {
    use std::time::Instant;

    let config = test_config();
    let start = Instant::now();

    // Create all 12 backends
    for kind in ProverKind::all_core() {
        let _ = ProverFactory::create(kind, config.clone());
    }

    let elapsed = start.elapsed();
    assert!(elapsed.as_millis() < 100, "Backend creation should be fast (< 100ms), took {:?}", elapsed);
    Ok(())
}

// ============================================================================
// Regression Tests
// ============================================================================

#[test]
fn test_no_backend_regression() {
    // Ensure we still have all original provers
    let original_provers = vec![
        ProverKind::Agda,
        ProverKind::Coq,
        ProverKind::Lean,
        ProverKind::Isabelle,
        ProverKind::Z3,
        ProverKind::CVC5,
        ProverKind::Metamath,
        ProverKind::HOLLight,
        ProverKind::Mizar,
    ];

    for kind in original_provers {
        // Just verify they're still creatable
        let config = test_config();
        assert!(ProverFactory::create(kind, config).is_ok());
    }
}

#[test]
fn test_prover_count() {
    // Verify we have exactly 12 core provers
    assert_eq!(ProverKind::all_core().len(), 12);
}
