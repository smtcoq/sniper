(* delete this Coq file and keep only pm_in_goal.elpi ? *)


(* \todo : put all these Ex/Import into order when done *)
Require Export SMTCoq.SMTCoq.

From elpi Require Import elpi.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import String.
Require Import utilities.
Require Import definitions.
Require Import elimination_fixpoints.
Require Import expand.
Require Import List.

Elpi Tactic pm_in_goal.
Elpi Accumulate File "pm_in_goal.elpi".
Elpi Typecheck.

Ltac kik t := match t with
| context C [ _ + _ ] => idtac "kikoo"
| _ => idtac "au revoir"
end.

Goal False.
kik 3.
kik (2 + 3).

Ltac blut t k :=
match goal with 
| |- context C[?y] => 
let T :=

  let t' := eval hnf t in 
  lazymatch t with
  | C[]
  | _ => fail
end.

