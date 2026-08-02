(* SPDX-FileCopyrightText: 2026 ECHIDNA Project Team *)
(* SPDX-License-Identifier: MPL-2.0 *)
(* Smoke fixture for the Isabelle/HOL AFP corpus adapter. *)

theory Smoke
  imports Main HOL.Nat
begin

(* A simple total definition. *)
definition double :: "nat \<Rightarrow> nat" where
  "double n = n + n"

(* A theorem closed by a single-step `by simp` (no hazards). *)
theorem double_zero: "double 0 = 0"
  by (simp add: double_def)

(* A lemma left open with `sorry` — the corpus adapter must flag this
   as a sorry hazard. *)
lemma double_mono: "n \<le> m \<Longrightarrow> double n \<le> double m"
  sorry

(* An axiomatization block — the adapter must flag the postulate hazard. *)
axiomatization choice :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  choice_spec: "\<exists>x. P x \<Longrightarrow> P (choice P)"

(* A datatype declaration. *)
datatype 'a tree =
    Leaf
  | Node "'a tree" 'a "'a tree"

(* A structured proof terminated by `qed`. *)
lemma double_succ: "double (Suc n) = Suc (Suc (double n))"
proof -
  have "double (Suc n) = Suc n + Suc n"
    by (simp add: double_def)
  also have "\<dots> = Suc (Suc (n + n))"
    by simp
  finally show ?thesis
    by (simp add: double_def)
qed

end
