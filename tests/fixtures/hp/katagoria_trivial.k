// SPDX-License-Identifier: MPL-2.0
// discipline: verify
//
// Smoke fixture: katagoria categorical-isomorphism single-goal.
// Exercises HPEcosystemBackend with ProverKind::KatagoriaVerifier.
// The trivial isomorphism A ≅ A reduces by identity functor; smallest
// possible witness that the verifier wiring round-trips.

theorem id_isomorphism (A : Object) : A ≅ A := by
  refl
