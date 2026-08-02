-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 ECHIDNA Project
-- Group Theory: self-contained abstract algebra for training corpus.
--
-- Defines abstract groups via a structure, then proves the five
-- standard group lemmas and several derived properties.
-- No Mathlib dependency.

/-! ## Abstract Group Definition -/

/-- A group structure with carrier, operation, identity, and inverse. -/
structure GroupAxioms (G : Type) (op : G → G → G) (e : G) (inv : G → G) : Prop where
  assoc     : ∀ a b c : G, op (op a b) c = op a (op b c)
  left_id   : ∀ a : G, op e a = a
  right_id  : ∀ a : G, op a e = a
  left_inv  : ∀ a : G, op (inv a) a = e
  right_inv : ∀ a : G, op a (inv a) = e

/-! ## Derived properties -/

/-- The identity element is unique. -/
theorem identity_unique {G : Type} (op : G → G → G) (e : G) (inv : G → G)
    (gax : GroupAxioms G op e inv) (e' : G) :
    (∀ a, op e' a = a) → e' = e := by
  intro h
  have : e' = op e' e := (gax.right_id e').symm
  rw [this, h]

/-- Left cancellation. -/
theorem left_cancel {G : Type} (op : G → G → G) (e : G) (inv : G → G)
    (gax : GroupAxioms G op e inv) (a b c : G) :
    op a b = op a c → b = c := by
  intro h
  have hb : b = op e b := (gax.left_id b).symm
  have hc : c = op e c := (gax.left_id c).symm
  have he : e = op (inv a) a := (gax.left_inv a).symm
  rw [hb, hc, he, gax.assoc, gax.assoc, h]

/-- Right cancellation. -/
theorem right_cancel {G : Type} (op : G → G → G) (e : G) (inv : G → G)
    (gax : GroupAxioms G op e inv) (a b c : G) :
    op b a = op c a → b = c := by
  intro h
  have hb : b = op b e := (gax.right_id b).symm
  have hc : c = op c e := (gax.right_id c).symm
  have he : e = op a (inv a) := (gax.right_inv a).symm
  rw [hb, hc, he, ← gax.assoc, ← gax.assoc, h]

/-- The inverse of the inverse is the original element. -/
theorem inv_inv {G : Type} (op : G → G → G) (e : G) (inv : G → G)
    (gax : GroupAxioms G op e inv) (a : G) :
    inv (inv a) = a := by
  apply left_cancel op e inv gax (inv a)
  rw [gax.left_inv, gax.right_inv]

/-- The inverse of a product reverses order. -/
theorem inv_mul {G : Type} (op : G → G → G) (e : G) (inv : G → G)
    (gax : GroupAxioms G op e inv) (a b : G) :
    inv (op a b) = op (inv b) (inv a) := by
  apply left_cancel op e inv gax (op a b)
  rw [gax.right_inv]
  rw [← gax.assoc (op a b)]
  rw [gax.assoc a b (inv b)]
  rw [gax.right_inv b]
  rw [gax.right_id]
  rw [gax.right_inv]

/-! ## Concrete Example: Integers mod 2 form a group under addition -/

def Z2 := Bool

def z2_op (a b : Z2) : Z2 := xor a b
def z2_e  : Z2 := false
def z2_inv (a : Z2) : Z2 := a

theorem z2_group : GroupAxioms Z2 z2_op z2_e z2_inv := {
  assoc     := by intros a b c; cases a <;> cases b <;> cases c <;> rfl
  left_id   := by intros a; cases a <;> rfl
  right_id  := by intros a; cases a <;> rfl
  left_inv  := by intros a; cases a <;> rfl
  right_inv := by intros a; cases a <;> rfl
}

/-- Verify the derived lemma for Z2. -/
example (a : Z2) : z2_inv (z2_inv a) = a :=
  inv_inv z2_op z2_e z2_inv z2_group a
