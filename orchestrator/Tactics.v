From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
From Ltac2 Require Import String.
Require Import List.
Import ListNotations.
Require Import Printer.
Require Import Triggers.

Ltac myapply2 A B := split ; [apply A | apply B].
Ltac myexact t := exact t.


(** We need to use a trick here: there
is no function in Ltac2's API which returns 
a Ltac1 value given its ident. We always need the absolute path
and we cannot look at several paths because the function [Ltac1.ref] 
throws an uncatchable exception whenever the path is not the good one.
Consequently, all the Orchestrator's tactics should be in one file, or the user has to 
provide the absolute path herself, which is not convenient at all.
Using elpi avoid these difficulties, even if the user needs
to create its own copy of all the tactic which take arguments *)

From elpi Require Import elpi.

Elpi Tactic apply_ltac1.
Elpi Accumulate lp:{{

  solve ((goal _ _ _ _ [str S| H]) as G) GS :-
    coq.ltac.call S H G GS.

}}.
Elpi Typecheck.

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

(** [run] runs a Ltac1 tactic given its ident and its arguments (provided as a string) *) 

Ltac2 run (s : string) (l : constr list) :=
let id := Ident.of_string s in
let id := of_ident (get_opt id) in
let l := of_list (List.map of_constr l) in
Ltac1.apply ltac1val:(fun s l => 
  let id := s in elpi apply_ltac1 ltac_string:(id) ltac_term_list:(l)) [id; l] run.

Section tests.

Goal (True /\ True) /\ (True -> True -> True /\ True).
Proof.
run "split" [].
let str := "split" in run str [].
run "myexact" ['I].
run "myexact" ['I].
intros H1 H2.
run "myapply2" ['H1; 'H2].
Qed.

End tests. 

(** Triggers for Sniper tactics *)


Ltac2 trigger_definitions :=
  TDisj (TContains (TGoal, NotArg) (TConstant None NotArg)) (TContains (TSomeHyp, NotArg)  (TConstant None (Arg id))).

Ltac2 trigger_higher_order_equalities :=
  TIs (TSomeHyp, Arg id) (TEq (TProd tDiscard tDiscard NotArg) tDiscard tDiscard NotArg).

Ltac2 trigger_fixpoints :=
  TContains (TSomeHyp, Arg id) (TFix tDiscard tDiscard NotArg).

Ltac2 trigger_pattern_matching :=
  TContains (TSomeHyp, Arg id) (TCase tDiscard tDiscard None NotArg).

Ltac2 trigger_polymorphism :=
  TDisj (TIs (TSomeHyp, NotArg)  (TProd (TSort TSet NotArg) tDiscard NotArg)) (TIs (TSomeHyp, NotArg) (TProd (TSort TBigType NotArg) tDiscard NotArg)).

Ltac2 trigger_higher_order :=
  TContains (TSomeHyp, Arg id) (TProd (TProd tDiscard tDiscard NotArg) tDiscard NotArg).

Ltac2 trigger_algebraic_types :=
  TDisj (TContains (TGoal, NotArg) (TInd None (Arg id))) (TContains (TSomeHyp, NotArg) (TInd None (Arg id))).

Ltac2 trigger_generation_principle :=
  TDisj (TContains (TGoal, NotArg) (TInd None (Arg id))) (TContains (TSomeHyp, NotArg) (TInd None (Arg id))).

Ltac2 trigger_anonymous_funs () :=
  TDisj (TMetaLetIn (TContains (TSomeHyp, Arg id) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg)))))
  (TMetaLetIn (TContains (TGoal, NotArg) (TLambda tDiscard tDiscard (Arg id))) ["f"]
  (TNot (TMetaLetIn (TContains (TGoal, NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg))))).

(** warning A TNot is not interesting whenever all hypotheses are not considered !!! *)
Ltac2 trigger_trakt_bool () :=
  TMetaLetIn (TNot (TIs (TSomeHyp, Arg id) (TEq (TInd (Some "bool") NotArg) tDiscard tDiscard NotArg))) ["H"]
  (TIs (TNamed "H", NotArg) (TType 'Prop NotArg)).

(* Ltac2 trigger_trakt_Z_bool := *)



