import Lake
open Lake DSL

package echidna_proofs where
  -- ECHIDNA dogfood proof corpus — pure Lean 4 core, no Mathlib / external deps.

@[default_target]
lean_lib ECHIDNA where
  -- Each proof file is its own top-level module, so every file must be listed
  -- as a root: a single umbrella root only builds the modules reachable through
  -- its import graph, silently skipping the rest. Listing them all makes
  -- `lake build` type-check the entire corpus.
  roots := #[`ECHIDNA, `Basic, `Nat, `List, `Propositional, `mvp_basic, `algebra.GroupTheory]
