From MetaCoq.Template Require Import utils All.
Unset MetaCoq Strict Unquote Universe Mode.
From SMTCoq Require Import SMTCoq.
Import MCMonadNotation.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import proof_correctness.

(* A first example :
mem n l is true whenever n belongs to l 
the plugin linearize the type of MemMatch because n is mentionned twice 
so we have an equivalent version linearized of member and then it generates an 
equivalent boolean fixpoint and the correctness lemma
*) 

(* Need to convert ltac2 tactic within ltac1 for compatibility reasons with MetaCoq *)
Tactic Notation "correctness" constr(t) constr(t') constr(n) constr(n') := 
let tac := 
ltac2:(t1 t2 n n' |- let t1' := ltac1_to_constr_unsafe t1 in
                  let t2' := ltac1_to_constr_unsafe t2 in
                  let n0 := constr_to_int (ltac1_to_constr_unsafe n) in
                  let n0' := constr_to_int (ltac1_to_constr_unsafe n') in correctness_auto t1' t2' n0 n0') in 
timeout 5 (tac t t' n n').

Ltac correctness_ltac1 t t' n n' := correctness t t' n n'.

Inductive mem : nat -> list nat -> Prop :=
    MemMatch : forall (xs : list nat) (n : nat), mem n (n :: xs)
  | MemRecur : forall (xs : list nat) (n n' : nat), mem n xs -> mem n (n' :: xs).

MetaCoq Run (decide mem []). 
Next Obligation.
(* the proof can be partially automatized thanks to tactics :
completeness_auto_npars takes the name of the fixpoint generated and the number of parameters 
as input and tries to generate the proof automatically 
soundness_auto_recarg_npars takes the name of the initial inductive, the argument 
on which to recur and the number of parameters of the inductive *)
- revert_all. ltac2:(completeness_auto_npars 'mem_linear_decidable 0).
- revert_all. ltac2:(soundness_auto_recarg_npars 'mem_linear_decidable 1 0). Defined.





 


