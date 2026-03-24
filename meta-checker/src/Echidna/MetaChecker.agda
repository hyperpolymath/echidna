-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- MetaChecker.agda — Top-level module for ECHIDNA's formal meta-verification
--
-- This module imports and re-exports all verified properties of the ECHIDNA
-- system. When Agda type-checks this module successfully, it provides a
-- machine-verified guarantee that the following properties hold:
--
-- FROM TrustLevel:
--   ✓ Trust levels form a total order (reflexive, antisymmetric, transitive, total)
--   ✓ min-trust computes a correct lower bound
--   ✓ Dangerous axioms always cap trust at Level1
--   ✓ Safe axioms preserve trust level
--   ✓ Capping is monotonic in trust level
--
-- FROM AxiomSafety:
--   ✓ Axiom policies form a total preorder
--   ✓ worst-policy is commutative, associative, has identity (Clean)
--   ✓ Rejected is absorbing (once rejected, always rejected)
--   ✓ Comment-aware scanning is sound
--   ✓ Every danger class maps to exactly one policy
--
-- FROM Portfolio:
--   ✓ Cross-checking improves trust over single-solver
--   ✓ Inconclusive and timeout always produce Level1
--   ✓ Small-kernel provers always have higher trust
--   ✓ Agreement is reflexive and symmetric
--   ✓ Unknown verdicts never count as agreement
--
-- FROM Dispatch:
--   ✓ Failed integrity always produces Level1
--   ✓ Dangerous axioms always produce Level1
--   ✓ Maximum trust (Level5) requires all positive factors
--   ✓ Pipeline is monotonically degrading
--   ✓ Pipeline is deterministic
--
-- TOTAL: 30+ proven properties, 0 postulates (except funext in AxiomSafety),
-- 0 sorry, 0 believe_me, 0 Admitted.

module Echidna.MetaChecker where

-- Import all verified modules
open import Echidna.TrustLevel public
open import Echidna.AxiomSafety public
open import Echidna.Portfolio public
open import Echidna.Dispatch public

------------------------------------------------------------------------
-- Summary: Key safety invariants proven
------------------------------------------------------------------------

-- Re-export the critical theorems for easy reference

-- 1. Dangerous axioms ALWAYS cap trust at Level1
key-safety-1 = dangerous-axioms-cap-at-level1

-- 2. Cross-checking ALWAYS improves trust
key-safety-2 = cross-check-improves-trust

-- 3. Failed integrity ALWAYS produces Level1
key-safety-3 = failed-integrity-level1

-- 4. Maximum trust requires ALL positive factors
key-safety-4 = max-trust-requires-all

-- 5. Rejected axiom policy is absorbing
key-safety-5 = rejected-absorbing

-- 6. Pipeline is deterministic
key-safety-6 = pipeline-deterministic

-- 7. Trust levels form a total order
key-order-1 = ≤ₜ-refl
key-order-2 = ≤ₜ-antisym
key-order-3 = ≤ₜ-trans
key-order-4 = ≤ₜ-total
