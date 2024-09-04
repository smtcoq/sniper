Require Import ZArith.

Ltac pose_case M :=
  let pat := fresh "pat" in
  let pf_refl := fresh "pf_refl" in
  pose (pat := M);
  assert (pf_refl : M = pat) by reflexivity;
  rewrite pf_refl;
  clearbody pat.

Section Examples.

Set Default Proof Mode "Classic".

(* This did not work with fold (automatic reduction), but works with rewrite *)
Goal match O with O => 42 | S _ => 41 end = 42.
  pose_case (match O with O => 42 | S _ => 41 end).
  reflexivity.
Qed.

(* pose_case does not work here (but regular scope works) -> we have to avoid lambdas? *)
Goal forall x : nat , ((fun y => (match y with O => 42 | _ => 41 end)) x) = 41.
  intro x.
  Fail
    let m := constr:(match y with O => 42 | _ => 41 end) in
    pose_case m.
  Abort.

(* This case was not covered before *)
Goal forall (x : nat) (f g : nat -> nat) , ((match x with O => f | S _ => g end) 42 = 42).
  intros x f g.
  (* pose (m := match x with O => f | S _ => g end); assert (H : match x with O => f | S _ => g end = m) by reflexivity; rewrite H. *)
  pose_case (match x with O => f | S _ => g end).
  (* now one can do scope *)
  Abort.

(* This one was already covered *)
Goal forall y : nat , let x := match y with | O => 2 | S _ => 3 end in x = x.
  intro y.
  pose_case (match y with O => 2 | S _ => 3 end).
  Abort.

(* veriT gets stuck here but z3 and cvc5 can solve it *)
Goal forall (x : nat) , (match x with O => 3 | _ => 3 end) = 3.
  intro x.
  pose_case (match x with O => 3 | _ => 3 end).
(*   (* scope. *) *)
(*   (* verit. *) *)
  Abort.

Goal forall y : nat , let x := (match y with | O => 2 | S _ => 3 end)%Z in x = x.
  intro y.
  pose_case (match y with O => 2%Z | S _ => 3%Z end).
  Abort.

End Examples.
