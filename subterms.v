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

Definition toto := fun A : Type =>
fix length (l : list A) : nat  :=
  match l with
  | nil => 0
  | (_ :: l')%list => S (length l')
  end.

Print toto.

Elpi Collect_subterms (toto).

(* TODO : struct *)

Elpi Tactic tata.
Elpi Accumulate File "subterms.elpi".

Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ _ as G) GL :- subterms Ty R, coq.say R.

}}.
Elpi Typecheck.

Goal toto = toto. 
unfold toto. elpi tata.
Abort. 


Elpi Command Collect_subterms_type.

Elpi Accumulate File "subterms.elpi".
Elpi Accumulate lp:{{
  main [trm Term] :- subterms_type Term L, coq.say L.
}}.
Elpi Typecheck.

Elpi Accumulate File "subterms.elpi".
Elpi Collect_subterms_type (Prop).
Elpi Collect_subterms_type (fun x : Prop => Prop).
Elpi Collect_subterms_type ((fun x : Type => Prop) Prop).
Elpi Collect_subterms_type (nat).
Elpi Collect_subterms_type (fun x : nat => x).
Elpi Collect_subterms_type (forall A : Type, nat -> unit).

Elpi Tactic swap.
Elpi Accumulate lp:{{
  pred last i: (list sealed-goal), o: sealed-goal.
  last [_ | GS] R :- last GS R.
  last [G] G.
  pred remove_last i: (list sealed-goal), o: (list sealed-goal).
  remove_last [G1, G2 | GS] R :- remove_last [G2 | GS] R1, 
  std.append [G1] R1 R.
  remove_last [_] [].
  remove_last [] [].
  msolve GS R :- last GS R1, remove_last GS R2, 
  std.append [R1] R2 R.
}}.
Elpi Typecheck.



Elpi Tactic instantiate_with_subterms_type_type_of_goal.
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "utilities.elpi".
Elpi Typecheck.
Elpi Accumulate File "construct_cuts.elpi".
Elpi Accumulate lp:{{

  solve (goal _ _ Ty _ [trm T] as G) GL :- !,
    subterms_type Ty L, instantiate_term_list T L R, coq.say R, construct_cuts R Trm,
    refine Trm G GL. 

}}.
Elpi Typecheck.

Elpi Tactic assert_list.
Elpi Accumulate File "construct_cuts.elpi".

Elpi Accumulate lp:{{

  solve (goal _ _ _ _ L as G) GL :- construct_cuts_args L R,
    refine R G GL.
    

}}.
Elpi Typecheck.

Goal False.
elpi assert_list (True) (nat) (unit) (true=true).
Show 2. Show 5.
all: elpi swap.
Abort.



Goal False.
elpi instantiate_with_subterms_type_type_of_goal (forall x: Type, x = x).
Abort.

Ltac instantiate_hyp_with_subterms_of_type_type H := let Ty := type of H in
elpi instantiate_with_subterms_type_type_of_goal (Ty).

Goal ((forall x: Type, x = x) -> unit -> nat -> Prop).
intro H.
instantiate_hyp_with_subterms_of_type_type H; try apply H.
Abort.



Elpi Command Tuple_to_list.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate lp:{{
  main [trm Term] :- tuple_to_list Term L, coq.say L.
}}.
Elpi Typecheck.

Elpi Tuple_to_list ((1, unit, bool)).




