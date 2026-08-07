// SPDX-License-Identifier: AGPL-3.0-or-later
// discipline: verify
//
// Smoke fixture: katagoria categorical-isomorphism single-goal.
// Exercises HPEcosystemBackend with ProverKind::KatagoriaVerifier.
// The trivial isomorphism A ≅ A reduces by identity functor; smallest
// possible witness that the verifier wiring round-trips.

theorem id_isomorphism (A : Object) : A ≅ A := by
  refl
