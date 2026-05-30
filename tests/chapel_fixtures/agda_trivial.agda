-- SPDX-License-Identifier: MPL-2.0
-- Trivial Agda goal: identity on Unit. Accepted by `agda --safe`.
-- Module name MUST match the filename written by tryProver — the
-- registry entry for Agda sets filenameOverride = "Trivial.agda"
-- (src/chapel/parallel_proof_search.chpl), so this declaration must
-- read `module Trivial where`.

module Trivial where

record ⊤ : Set where
  constructor tt

trivial-true : ⊤
trivial-true = tt
