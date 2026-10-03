-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- lakefile.lean — EchidnaTrustProofs
--
-- Builds the E-series verification proof obligations:
--   E4  ConfidenceLattice.lean   (trust-level partial order + scoring)
--   E10 ParetoMaximality.lean    (PO-1..PO-11 algebraic properties)
--       ParetoStrongMaximality.lean  (PO-12 descent / strong maximality)
--   E11 IntegrityVerification.lean  (SHAKE-256/512 + BLAKE3 verifier)
--   E13 PortfolioCompleteness.lean  (portfolio cross-checking)
--
-- Toolchain: leanprover/lean4:v4.13.0 (pinned in lean-toolchain).
-- No mathlib dependency — proofs use only core Lean 4.

import Lake
open Lake DSL

package echidna_trust_proofs where
  -- No external dependencies required.

@[default_target]
lean_lib EchidnaTrustProofs where
  roots := #[
    `ConfidenceLattice,
    `IntegrityVerification,
    `ParetoMaximality,
    `ParetoStrongMaximality,
    `PortfolioCompleteness
  ]
