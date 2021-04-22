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
def_and_pattern_matching ; inst_clear.

Ltac def_and_pattern_matching_mono_param t :=
def_and_pattern_matching ; instanciate_type_tuple t ; specialize_context_clear.

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

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
Proof.
interp_alg_types_context_goal. 
def_and_pattern_matching_mono.     
verit (H1, H3,  H5, H6_Z, H7_Z).
Qed.

Ltac snipe_param t :=
try interp_alg_types_context_goal ; try (def_and_pattern_matching_mono_param t).

Ltac snipe_no_param :=
try interp_alg_types_context_goal; try def_and_pattern_matching_mono.

Tactic Notation "snipe" constr(t) := snipe_param t.
Tactic Notation "snipe" := snipe_no_param.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
Proof.
snipe.
verit (H1, H3,  H5, H6_Z, H7_Z).
Qed.

Local Open Scope Z_scope.

Hypothesis length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).

Lemma length_app_auto : forall B (HB: CompDec (list B)), forall (l1 l2 l3 : list B), 
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. nat_convert.
snipe length_app.
 verit length_app_B. auto with typeclass_instances. Qed.


Inductive tree {A: Type} : Type :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.



Definition is_empty {A} (t : @tree A) :=
 match t with
 | Leaf => true
 | _ => false
 end.


Definition remove_option {A} (default : A) (o : option A) := match o with 
| Some x => x
| None => default
end.

Ltac get_tuple_of_hypothesis_aux p p' k :=
match goal with 
| H : _ |- _ => let T := type of H in
 is_not_in_tuple p T ; try (get_tuple_of_hypothesis_aux (p, T) (p', H) k) 
; k (p', H)
end.

Ltac get_tuple_of_hypothesis k := let H := fresh in
assert (H : True) by (exact I) ; get_tuple_of_hypothesis_aux I H k.

Goal False -> False -> False -> False.
intros. get_tuple_of_hypothesis ltac:(fun x => pose x).
Abort.


Lemma option_tree_Z : forall (t : tree), 
is_empty (remove_option (Node Leaf 1 Leaf) (Some t)) = true -> t = Leaf.
Proof.
snipe.
get_tuple_of_hypothesis ltac:(fun p => pose p).
verit (H, H, H_bool, H_Z, H3, H3_bool, H3_Z, H4, H4_bool, H4_Z, H5, H5_bool, H5_Z, H6, H6_bool, H6_Z,
     H7, H7_bool, H7_Z, H8, H2, H1, H0).





(* forall l, (exists x, (hd_error l = Some x)) -> negb (l ====? nil) .
Proof.
intros. destruct H.
apply triple_eq_is_eq in H. 
verit  hd_error_def_nil  some_neq_none cons_neq_nil H   (* cons_neq_nil is necessary *).   
Qed.*)