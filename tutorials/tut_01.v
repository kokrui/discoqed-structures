Require Import Reals.
Require Import Classical_Prop.
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
