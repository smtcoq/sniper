From elpi Require Import elpi.

Elpi Command Collect_subterms.

Elpi Accumulate File "subterms.elpi".
Elpi Accumulate lp:{{
  main [trm Term] :- subterms Term L, coq.say L.
}}.
Elpi Typecheck.

Elpi Collect_subterms (Prop).
Elpi Collect_subterms (fun x : Prop => Prop).
Elpi Collect_subterms (fun x : nat => x).
Elpi Collect_subterms (nat).
Elpi Collect_subterms 
(fun x : nat => match x with 
  | 0 => unit
  | S x' => Type
end).
Elpi Collect_subterms
(fun A : Type =>
fix length (l : list A) {struct l} : nat  :=
  match l with
  | nil => 0
  | (_ :: l')%list => S (length l')
  end). 

(* TODO : struct *)

Elpi Command Collect_subterms_type.

Elpi Accumulate File "subterms.elpi".
Elpi Accumulate lp:{{
  main [trm Term] :- subterms_type Term L, coq.say L.
}}.
Elpi Typecheck.

Elpi Collect_subterms_type (Prop).
Elpi Collect_subterms_type (fun x : Prop => Prop).
Elpi Collect_subterms_type ((fun x : Type => Prop) Prop).
Elpi Collect_subterms_type (nat).
Elpi Collect_subterms_type (fun x : nat => x).
Elpi Collect_subterms_type (fun A : Type =>
fix length (l : list A) {struct l} : nat  :=
  match l with
  | nil => 0
  | (_ :: l')%list => S (length l')
  end).

Ltac pose_no_name k := pose k.
(* TODO : pourquoi ça ne marche pas avec le pose de Ltac ?*)
(* TODO : unquoter la liste des sous termes de type Type et la poser *)

Elpi Tactic pose_subterms_of_goal.
Elpi Accumulate lp:{{

  solve (goal _ _ Ty _ _ as G) GL :-
    
    coq.ltac.call "pose_no_name" [trm Ty] G GL.

}}.
Elpi Typecheck.



Goal forall A : Type, nat -> unit.
elpi pose_subterms_of_goal.
Abort.


