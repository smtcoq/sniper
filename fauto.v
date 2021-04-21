Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import definitions.
Require Import eta_expand.
Require Import elimination_pattern_matching. 
Require Import elimination_polymorphism.
Require Import interpretation_algebraic_types.



Ltac def_and_pattern_matching := 
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_pattern_matching H')).

Ltac def_and_pattern_matching_mono :=
def_and_pattern_matching ; inst_no_parameter.

Goal ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)). 
def_and_pattern_matching. assumption.
Qed. 

Goal ((forall (A: Type) (l : list A), 
@List.length A l = match l with
| nil => 0
| y :: xs => S (length xs)
end)).
get_definitions_theories ltac:(fun H => let T := type of H in pose T).
assert P. unfold P. reflexivity.
unfold P in H.
expand_hyp H.
Fail eliminate_pattern_matching H0.
Abort.

Goal ((forall (A : Type) (l : list A),
#|l| = match l with
       | [] => 0
       | _ :: xs => S #|xs|
       end) -> True).
intro H.
eliminate_pattern_matching H.
exact I.
Qed.

Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)).
def_and_pattern_matching_mono.
assumption.
Qed.

Goal forall (l : list Z) x,  hd_error l = Some x -> (l <> []).
Proof.
intros l x H.       
interpretation_alg_types_tac (option Z).
interpretation_alg_types_tac (list Z).
def_and_pattern_matching.
verit (H, H2, H3,  H6, H7, H8).


(* forall l, (exists x, (hd_error l = Some x)) -> negb (l ====? nil) .
Proof.
intros. destruct H.
apply triple_eq_is_eq in H. 
verit  hd_error_def_nil  some_neq_none cons_neq_nil H   (* cons_neq_nil is necessary *).   
Qed.*)