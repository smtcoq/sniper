(* Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper. *)
From Sniper Require Import Sniper.
Require Import String.

Section inversions_lemmas.

(* An example from the Software foundations *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem SSSSev_ev : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof. Fail firstorder congruence. inv_principle_all ; firstorder congruence. Qed.

Section inversions_lemmas.

