(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) *)
(*
   TrustRule.v — Rocq recheck of meta-checker/src/Echidna/TrustRule.agda.

   Route: re-proved (PROOF-POLICY §2). The Agda module was not transported
   through Dedukti; each statement below is restated by hand to match the
   Agda statement of the same name (`-` becomes `_`), and proved again here.
   The definitions are transcribed from the Agda module, which is itself a
   transcription of `compute_trust_level` in
   src/rust/verification/confidence.rs.

   Correspondence, statement by statement:
     dangerous_gives_level1, integrity_failure_gives_level1   (guards)
     rule_level5, level5_sound                                (Level5)
     rule_mono, compute_mono                                  (monotonicity)
     level5_without_certificate, dispatch_model_diverges      (witnesses)
   The Agda order _≤ₜ_ is an inductive relation with the same fifteen
   cases as `le_t` below.
*)

From Coq Require Import Arith Bool Lia.

Inductive TrustLevel := Level1 | Level2 | Level3 | Level4 | Level5.

(* Same cases as Echidna.TrustLevel._≤ₜ_ *)
Inductive le_t : TrustLevel -> TrustLevel -> Prop :=
| l1_le : forall t, le_t Level1 t
| l2_le_2 : le_t Level2 Level2 | l2_le_3 : le_t Level2 Level3
| l2_le_4 : le_t Level2 Level4 | l2_le_5 : le_t Level2 Level5
| l3_le_3 : le_t Level3 Level3 | l3_le_4 : le_t Level3 Level4
| l3_le_5 : le_t Level3 Level5
| l4_le_4 : le_t Level4 Level4 | l4_le_5 : le_t Level4 Level5
| l5_le_5 : le_t Level5 Level5.

Lemma le_t_refl : forall t, le_t t t.
Proof. destruct t; constructor. Qed.

Lemma le_t_trans : forall a b c, le_t a b -> le_t b c -> le_t a c.
Proof. intros a b c H1 H2; inversion H1; subst; inversion H2; subst; constructor. Qed.

Inductive DangerLevel := Safe | Noted | Warning | Reject.

Record Factors := mkFactors {
  small_kernel : bool;
  confirming : nat;
  has_certificate : bool;
  certificate_verified : bool;
  danger : DangerLevel;
  integrity_ok : bool
}.

(* confirming_provers >= 2 *)
Definition cross (n : nat) : bool :=
  match n with 0 | 1 => false | S (S _) => true end.

Definition dangerous (d : DangerLevel) : bool :=
  match d with Safe | Noted => false | Warning | Reject => true end.

Definition rule (sk cc hc cv : bool) : TrustLevel :=
  if cc && cv && sk then Level5 else
  if sk && cv then Level4 else
  if hc && cv then Level3 else
  if cc then Level3 else Level2.

Definition bad (f : Factors) : bool :=
  dangerous (danger f) || negb (integrity_ok f).

Definition compute (f : Factors) : TrustLevel :=
  if bad f then Level1
  else rule (small_kernel f) (cross (confirming f))
            (has_certificate f) (certificate_verified f).

(* 1. Guards *)

Theorem dangerous_gives_level1 : forall f,
  dangerous (danger f) = true -> compute f = Level1.
Proof. intros f H; unfold compute, bad; rewrite H; reflexivity. Qed.

Theorem integrity_failure_gives_level1 : forall f,
  integrity_ok f = false -> compute f = Level1.
Proof.
  intros f H; unfold compute, bad; rewrite H.
  destruct (dangerous (danger f)); reflexivity.
Qed.

(* 2. What Level5 requires *)

Lemma cross_sound : forall n, cross n = true -> 2 <= n.
Proof. intros [|[|n]] H; simpl in H; try discriminate; lia. Qed.

Lemma rule_level5 : forall sk cc hc cv,
  rule sk cc hc cv = Level5 -> sk = true /\ cc = true /\ cv = true.
Proof.
  intros [] [] [] []; unfold rule; simpl; intro H;
    try discriminate; repeat split; reflexivity.
Qed.

Theorem level5_sound : forall f, compute f = Level5 ->
  small_kernel f = true /\ certificate_verified f = true /\
  2 <= confirming f /\ integrity_ok f = true /\ dangerous (danger f) = false.
Proof.
  intros f H; unfold compute, bad in H.
  destruct (dangerous (danger f)) eqn:Ed; simpl in H; try discriminate.
  destruct (integrity_ok f) eqn:Ei; simpl in H; try discriminate.
  destruct (rule_level5 _ _ _ _ H) as [Hsk [Hcc Hcv]].
  repeat split; auto. apply cross_sound; exact Hcc.
Qed.

(* 3. Monotonicity: false <= true on bool *)

Definition le_b (a b : bool) : Prop := a = true -> b = true.

Lemma cross_mono : forall m n, m <= n -> le_b (cross m) (cross n).
Proof.
  unfold le_b; intros [|[|m]] [|[|n]] Hle H; simpl in *; try discriminate;
    try reflexivity; lia.
Qed.

Theorem rule_mono : forall sk sk' cc cc' hc hc' cv cv',
  le_b sk sk' -> le_b cc cc' -> le_b hc hc' -> le_b cv cv' ->
  le_t (rule sk cc hc cv) (rule sk' cc' hc' cv').
Proof.
  unfold le_b; intros [] [] [] [] [] [] [] [] H1 H2 H3 H4;
    unfold rule; simpl;
    try (specialize (H1 eq_refl); discriminate);
    try (specialize (H2 eq_refl); discriminate);
    try (specialize (H3 eq_refl); discriminate);
    try (specialize (H4 eq_refl); discriminate);
    constructor.
Qed.

(* g is at least as good as f in every factor *)
Record better (f g : Factors) : Prop := {
  sk_le : le_b (small_kernel f) (small_kernel g);
  conf_le : confirming f <= confirming g;
  hc_le : le_b (has_certificate f) (has_certificate g);
  cv_le : le_b (certificate_verified f) (certificate_verified g);
  io_le : le_b (integrity_ok f) (integrity_ok g);
  dg_le : le_b (dangerous (danger g)) (dangerous (danger f))
}.

Lemma bad_anti : forall f g, better f g -> bad g = true -> bad f = true.
Proof.
  intros f g [_ _ _ _ Hio Hdg]; unfold bad, le_b in *.
  destruct (dangerous (danger f)), (dangerous (danger g)),
           (integrity_ok f), (integrity_ok g); simpl; intro H;
    auto; try discriminate;
    try (specialize (Hdg eq_refl); discriminate);
    try (specialize (Hio eq_refl); discriminate).
Qed.

Theorem compute_mono : forall f g, better f g -> le_t (compute f) (compute g).
Proof.
  intros f g Hb; unfold compute.
  destruct (bad f) eqn:Ef; [constructor|].
  destruct (bad g) eqn:Eg.
  - rewrite (bad_anti f g Hb Eg) in Ef; discriminate.
  - destruct Hb as [Hsk Hconf Hhc Hcv _ _].
    apply rule_mono; auto. apply cross_mono; exact Hconf.
Qed.

(* 4. Witnesses *)

Theorem level5_without_certificate :
  compute (mkFactors true 2 false true Safe true) = Level5.
Proof. reflexivity. Qed.

(* Echidna.Dispatch.compute-trust, transcribed: one certificate flag and a
   cross-checked flag; no certificate gives Level2 whatever else holds. *)
Inductive DangerClass := DC_Safe | DC_Noted | DC_Warning | DC_Reject.

Definition dispatch_compute (io : bool) (d : DangerClass) (h s c : bool)
  : TrustLevel :=
  match io, d with
  | false, _ | _, DC_Warning | _, DC_Reject => Level1
  | true, _ =>
      if h then (if s then (if c then Level5 else Level4) else Level3)
      else Level2
  end.

Theorem dispatch_model_diverges :
  compute (mkFactors false 2 false false Safe true) = Level3 /\
  dispatch_compute true DC_Safe false false true = Level2.
Proof. split; reflexivity. Qed.
