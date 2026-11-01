-- SPDX-License-Identifier: MPL-2.0
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
-- FROM AxiomTrackerCompleteness:
--   ✓ Scan-entry preserves length (no silent omissions)
--   ✓ Fold distributes over append
--   ✓ Prepending a policy never lowers the folded result
--   ✓ Empty registry folds to Clean
--   ✓ A single DC-Reject pattern is always caught
--   ✓ Rejected is absorbing, and Rejected is detected on either side
--
-- FROM Receipt (epistemic-types semantic rewrite):
--   ✓ A receipt is factive; a warrant is not
--   ✓ A warrant never promotes to a receipt ("no free promotion")
--   ✓ No receipt exists while the agent cannot discriminate the worlds
--   ✓ A discriminating check yields a receipt
--
-- FROM Integrity (E11 semantic rewrite):
--   ✓ Verification requires an initialised manifest
--   ✓ Verification means the recorded digest was matched
--   ✓ An uninitialised manifest NEVER verifies (the invariant DEBT D9 breaks)
--   ✓ The collision-resistance hypothesis is load-bearing (sharpness)
--
-- FROM ClampTrust (ClampTrustBounds semantic rewrite):
--   ✓ The clamp stays within [1,5]
--   ✓ The clamp is monotone in the trust order
--   ✓ Fixed points 0/1 -> Level1, >=5 -> Level5
--   ✓ The clamp is idempotent
--
-- TOTAL: 45+ proven properties, 0 postulates, 0 assumptions,
-- 0 sorry, 0 believe_me, 0 Admitted.
--
-- Canonical invocation (PROOF-POLICY §2.1):
--   agda --safe --without-K --cubical-compatible src/Echidna/MetaChecker.agda
-- This emits -W[no]UnsupportedIndexedMatch for the indexed pattern matches
-- in TrustLevel (≤ₜ-antisym, ≤ₜ-trans) and ClampTrust (≤-difference).  Those
-- functions therefore do not compute under Cubical transports.  The build is
-- `--cubical-compatible`, NOT `--cubical`: see docs/PROOF-STATUS.adoc R4.

module Echidna.MetaChecker where

-- Import all verified modules
open import Echidna.TrustLevel public
open import Echidna.AxiomSafety public
open import Echidna.Portfolio public
open import Echidna.Dispatch public
open import Echidna.Receipt public
open import Echidna.Integrity public
open import Echidna.ClampTrust public
open import Echidna.AxiomTrackerCompleteness public

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

-- 8. Epistemic separation: a warrant is never a receipt
key-epistemic-1 = receipt-factive
key-epistemic-2 = warrant-not-factive
key-epistemic-3 = no-free-promotion

-- 9. Integrity: an uninitialised manifest never verifies (DEBT D9)
key-integrity-1 = uninitialised-never-verified
key-integrity-2 = verified-means-match

-- 10. Clamp bounds and monotonicity
key-clamp-1 = clamp-lower
key-clamp-2 = clamp-upper
key-clamp-3 = clamp-monotone
key-clamp-4 = clamp-idempotent

-- 11. Axiom-tracker completeness
key-tracker-1 = scan-entry-length
key-tracker-2 = fold-worst-++
key-tracker-3 = single-reject-detected
key-tracker-4 = worst-policy-rejected-inv
