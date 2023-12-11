Require Import Reals.
Require Import Classical_Prop.
Require Import Coq.Logic.Classical_Prop.

Open Scope R_scope.

(* Q1a, proving correct negation*)

Definition in_range (a: R) := 1 < a /\ a < 5.
Lemma negation_of_in_range : forall a:R, ~ in_range a -> a <= 1 \/ a >= 5.
Proof.
  unfold in_range.
  intros a H.
  apply not_and_or in H.
  destruct H as [H1|H2].
  - left.
    apply Rnot_lt_le. assumption.
  - right.
    apply Rnot_gt_ge. assumption.
Qed.

(* Q2a, proving corrected version *)

Lemma q2a : forall a b c : Prop, a /\ ~(b /\ c) <-> a /\ (~b \/ ~c).
Proof.
  intros a b c.
  split.
  - (* left to right *)
    intros [Ha Hbc].
    split.
    + assumption.
    + apply not_and_or.
      assumption.
  - (* right to left *)
    intros [Ha Hbc].
    split.
    + assumption.
    + apply or_not_and.
      assumption.
Qed.

(* Q2b, proving corrected version *)

Lemma q2b : forall x y z : Prop, ~(x \/ y) \/ z <-> (~x /\ ~y) \/ z.
Proof.
  intros x y z.
  split.
  - (* left to right *)
    intros [Hnxy|Hz].
    + left.
      apply not_or_and.
      assumption.
    + right.
      assumption.
  - (* right to left *)
    intros [Hnxy|Hz].
    + left.
      apply and_not_or.
      assumption.
    + right.
      assumption.
Qed.

(* Q3a, proving simplification *)

Lemma q3a : forall a b : Prop, (~a /\ (~a -> (b /\ a))) <-> False.
Proof.
  split.
  - (* left to right *)
    intros [Hna Himp].
    destruct (Himp Hna) as [Hb Ha].
    contradiction Ha.
  - (* right to left *)
    intros H.
    destruct H.
Qed.

(* Q3b, proving simplification *)

Lemma statement2 : forall p q : Prop, ((p \/ ~q) -> q) <-> q.
Proof.
  split.
  - (* left to right *)
    intros H.
    apply NNPP.
    intro Hnq.
    apply Hnq.
    apply H.
    right.
    assumption.
  - (* right to left *)
    intros Hq Hp_or_nq.
    assumption.
Qed.
