(* Q2, proving correct options *)

Variable S : Set.
Variable student : S -> Prop.
Variable SoC : S -> Prop.
Variable CS1231S : S -> Prop.

Axiom all_students : forall x : S, SoC x /\ CS1231S x.

Theorem q2_option_i : forall x : S, SoC x -> CS1231S x.
Proof.
  intros x Hsoc.
  pose proof (all_students x) as Hall.
  destruct Hall as [Hsoc' Hcs1231s].
  exact Hcs1231s.
Qed.
