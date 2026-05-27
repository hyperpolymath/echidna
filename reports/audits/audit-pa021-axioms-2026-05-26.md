<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-->

# Audit: legitimate mathematical axioms (PA021)

**Auditor**: Jonathan D.A. Jewell
**Date**: 2026-05-26
**Scope**: 2 panic-attack PA021 ProofDrift findings, both postulates with inline justification in the source.
**Cross-reference**: campaign tracker [hyperpolymath/panic-attack#32](https://github.com/hyperpolymath/panic-attack/issues/32).
**Registry**: `audits/assail-classifications.a2ml`.

## §1 — `proofs/agda/Basic.agda` — `funext` (function extensionality)

Line 172-179 of `Basic.agda`:

```agda
-- provable in Cubical Agda (--cubical). In plain Agda it must be
-- postulated. It is a standard mathematical axiom accepted by all
-- major proof assistants (Coq's Functional Extensionality, Lean's
-- funext, HoTT axiom). It does NOT compromise soundness.
-- See: HoTT Book, Section 2.9; nLab "function extensionality"
postulate
  funext : {A B : Set} {f g : A → B}
         → ((x : A) → f x ≡ g x) → f ≡ g
```

`funext` is one of the foundational axioms of dependent type theory. Coq has `FunctionalExtensionality.functional_extensionality`; Lean's mathlib has `funext`; HoTT has Axiom 2.9.3. It is provable in Cubical Agda but must be postulated in plain Agda — a well-known constraint of the underlying type theory.

**Classification**: `legitimate-mathematical-axiom`.

## §2 — `proofs/agda/SoundnessPreservation.agda` — `Conflicts` (intentional parameter)

Line 44-53 of `SoundnessPreservation.agda`:

```agda
-- Conflicts is an abstract binary predicate over two axiom lists.
-- We leave it as a postulate-free parameter: the caller supplies a
-- concrete proof of ¬ Conflicts when they know the sets are disjoint.
...
-- an axiom that the other marks Reject.
postulate
  Conflicts : List Axiom → List Axiom → Set
```

The comment explicitly tags this as "INTENTIONAL PARAMETER — 'Conflicts' is domain knowledge about which axioms conflict". This is a parameterised theorem: the theorem statement quantifies over an arbitrary `Conflicts` predicate, and the caller proves `¬ Conflicts` (or supplies a concrete relation) at use-site. This is NOT a proof debt — it is the *interface* of the theorem.

**Classification**: `intentional-parameter`.

## Anti-gameability

The registry is `audits/assail-classifications.a2ml`. Adding new postulates to either file does NOT become silently suppressed — only these two specific postulates are classified. Any new `postulate` or `sorry` in these or other proof files remains visible.

## Verification

No proof source touched; `agda --check` rebuild is moot (input unchanged from main).

Refs hyperpolymath/panic-attack#32.
