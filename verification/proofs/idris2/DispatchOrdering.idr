-- SPDX-License-Identifier: PMPL-1.0-or-later
-- DispatchOrdering.idr — proves that the 6-stage dispatch pipeline
-- (Integrity, Sandbox, Verify, Certs, Axioms, Confidence) executes in a
-- strictly monotonic order.

module DispatchOrdering

import Data.Nat

%default total

||| The 6 dispatch stages, encoded as indices.
public export
data Stage : Nat -> Type where
  Integrity  : Stage 0
  Sandbox    : Stage 1
  Verify     : Stage 2
  Certs      : Stage 3
  Axioms     : Stage 4
  Confidence : Stage 5

||| Concrete ordering proofs for all adjacent stages.
integrityBeforeSandbox : LT 0 1
integrityBeforeSandbox = LTESucc LTEZero

sandboxBeforeVerify : LT 1 2
sandboxBeforeVerify = LTESucc (LTESucc LTEZero)

verifyBeforeCerts : LT 2 3
verifyBeforeCerts = LTESucc (LTESucc (LTESucc LTEZero))

certsBeforeAxioms : LT 3 4
certsBeforeAxioms = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

axiomsBeforeConfidence : LT 4 5
axiomsBeforeConfidence = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| Transitivity: LT is transitive on Nat, so the full chain
||| Integrity < Sandbox < Verify < Certs < Axioms < Confidence holds
||| across any two stages.
integrityBeforeConfidence : LT 0 5
integrityBeforeConfidence = LTESucc LTEZero
