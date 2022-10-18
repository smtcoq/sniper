From MetaCoq.Template Require Import utils All.
Unset MetaCoq Strict Unquote Universe Mode.
From SMTCoq Require Import SMTCoq.
Require Import Sniper.
Import MCMonadNotation.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.

(* A first example :
mem n l is true whenever n belongs to l 
the plugin linearize the type of MemMatch because n is mentionned twice 
so we have an equivalent version linearized of member and then it generates an 
equivalent boolean fixpoint and the correctness lemma
*) 

Inductive mem : nat -> list nat -> Prop :=
    MemMatch : forall (xs : list nat) (n : nat), mem n (n :: xs)
  | MemRecur : forall (xs : list nat) (n n' : nat), mem n xs -> mem n (n' :: xs).

(* running the main command *)
MetaCoq Run (decide mem []). 
Next Obligation.
(* the proof can be partially automatized thanks to tactics :
completeness_auto_npars takes the name of the fixpoint generated and the number of parameters 
as input and tries to generate the proof automatically 
soundness_auto_recarg_npars takes the name of the initial inductive, the argument 
on which to recur and the number of parameters of the inductive *)
split.
- revert_all. ltac2:(completeness_auto_npars 'mem_linear_decidable 1).
- revert_all. ltac2:(soundness_auto_recarg_npars 'mem_linear_decidable 1 0). Qed.

(* Another parametric example : 
the predicate smaller_than_all holds between a
natural number and a list of integers whenever the term is
smaller than all the elements of the list
Here, we need to pass the quotations of Z.le, the boolean version of Z.le and the proof 
of equivalence as arguments to the command
*) 

Inductive smaller_than_all : Z -> list Z -> Prop :=
 | sNil  : forall n, smaller_than_all n nil
 | sCons : forall n n' l, BinInt.Z.le n n' -> smaller_than_all n l -> smaller_than_all n (n' :: l).

MetaCoq Run (decide (smaller_than_all) [(<%Z.le%>, <%Z.leb%>, <%Z.leb_le%>)]).
Next Obligation.
split.
- intros H1. induction H1; auto.
simpl. apply Z.leb_le in H. rewrite H. rewrite IHsmaller_than_all. auto.
- intros H1. induction H0. constructor. simpl in H1;
elim_and_and_or. constructor. apply Z.leb_le. assumption. apply IHlist. assumption. Qed.


(* Example of proof automation with snipe and the decided predicates *)


Trakt Add Relation 2 mem mem_linear_decidable decidable_lemma.

Lemma test1 : (forall (n : nat), mem n [n]).
Proof. trakt bool. Print mem_linear_decidable. scope. clear - H6 H4 H1 H12. verit. (*TODO *)

 


