Require Import ZArith.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Printf Message.
Import Unsafe.

Ltac2 l_pose_case (c : constr) : unit :=
  let fresh_id := Fresh.in_goal @pat in
  pose ($fresh_id := $c);
  let new_constr := make (Var fresh_id) in
  fold $new_constr.

Ltac pose_case c :=
  let tac := ltac2:(c |- let c' := Option.get (Ltac1.to_constr c) in l_pose_case c') in
  tac c.

Section Examples.

Set Default Proof Mode "Classic".

Goal forall x , (match x with | O => 41 | S _ => 42 end) = 42.
  intro x.
  let m := constr:(match x with | O => 41 | S _ => 42 end) in
  pose_case m.
  Abort.

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
  let m := constr:(match x with O => f | S _ => g end) in pose_case m.
  (* now one can do scope *)
  Abort.

(* This one was already covered *)
Goal forall y : nat , let x := match y with | O => 2 | S _ => 3 end in x = x.
  intro y.
  let m := constr:(match y with | O => 2 | S _ => 3 end) in pose_case m.
  Abort.

(* veriT gets stuck here but z3 and cvc5 can solve it *)
Goal forall (x : nat) , (match x with O => 3 | _ => 3 end) = 3.
  intro x.
  let m := constr:(match x with | O => 3 | S _ => 3 end) in pose_case m.
(*   (* scope. *) *)
(*   (* verit. *) *)
  Abort.

Goal forall y : nat , let x := (match y with | O => 2 | S _ => 3 end)%Z in x = x.
  intro y.
  let m := constr:(match y with O => 2%Z | S _ => 3%Z end) in pose_case m.
  Abort.

End Examples.
