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
Require Import elimination_fixpoints.
Require Import eta_expand.
Require Import elimination_pattern_matching. 
Require Import elimination_polymorphism.
Require Import interpretation_algebraic_types.



Ltac def_and_pattern_matching := 
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_pattern_matching H')).


Ltac def_fix_and_pattern_matching :=
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun H'' =>
eliminate_pattern_matching H''))).


Ltac def_and_pattern_matching_mono :=
def_and_pattern_matching ; inst_clear.

Ltac def_and_pattern_matching_mono_param t :=
def_and_pattern_matching ; instanciate_type_tuple t ; specialize_context_clear.
Ltac def_fix_and_pattern_matching_mono_param t :=
def_fix_and_pattern_matching ; instanciate_type_tuple t ; specialize_context_clear.

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
verit.
Qed.


Ltac scope_param t :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t ; try nat_convert).
(* besoin de nat_convert parce que sinon, on risque de déplier des définitions et ajouter des 
hypothèses dans nat et ensuite verit se met à peiner *)

Ltac scope_no_param :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst_clear ; try nat_convert).

Ltac snipe_param t := 
scope_param t ; verit.

Ltac snipe_no_param := 
scope_no_param ; verit.

Tactic Notation "scope" constr(t) := scope_param t.
Tactic Notation "scope" := scope_no_param.

Tactic Notation "snipe" constr(t) := snipe_param t.
Tactic Notation "snipe" := snipe_no_param.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
Proof.
snipe.
Qed.


Goal forall (A: Type), CompDec A -> forall (l : list A) (x : A),  hd_error l = Some x -> (l <> []).
Proof.
intros A.
snipe. admit. admit. admit.
Abort.



Local Open Scope Z_scope.

Hypothesis length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).

Lemma length_app_auto : forall B (HB: CompDec B), forall (l1 l2 l3 : list B), 
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. 
snipe length_app. Qed.


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
assert (H : True) by (exact I) ; get_tuple_of_hypothesis_aux unit H k.



Goal False -> False -> False -> False.
intros.
get_tuple_of_hypothesis ltac:(fun x => pose x).
Abort.




Fixpoint search {A : Type} {H: CompDec A} (x : A) l := 
  match l with 
  | [] => false
  | x0 :: l0 => if @eqb_of_compdec _ H x x0  then true else search x l0
  end.

Lemma search_app : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A), search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
intros A H x l1 l2. induction l1 as [ | x0 l0 IH]. 
- reflexivity.
- simpl. destruct (@eqb_of_compdec _ H x x0). 
  + reflexivity.
  + rewrite IH. reflexivity. 
Qed.



Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A), search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
intros A H x l1 l2. induction l1 as [ | x0 l0 IH]. 
- snipe. admit. admit. (*  pb de compdec sinon la preuve passe *)
- simpl. destruct (@eqb_of_compdec _ H x x0). 
 + snipe. admit. admit.
 + snipe. admit. admit.

(* TODO : clears parce que scope mouline *)

Abort.




Lemma search_lemma : forall (A : Type) (H : CompDec A) (x: Z) (l1 l2 l3: list Z), search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
intros A H x l1 l2 l3.  rewrite !search_app.  rewrite Coq.Bool.Bool.orb_comm with (b1 := search x l3). rewrite Coq.Bool.Bool.orb_comm  with (b1 := search x l2) (b2 := search x l1 ). rewrite  Coq.Bool.Bool.orb_assoc. reflexivity.
Qed.


Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A), 
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. intros A H. snipe @search_app.
Abort.



Lemma option_tree_Z : forall (t : @tree Z), 
is_empty t = true -> t = Leaf.
Proof.
intro t ; case t. 
- snipe. admit. admit. admit.
- scope. 
(* verit. => trop de compdec*)
Abort.

Local Open Scope nat_scope.

Goal forall (x y z : nat), y = S x /\ z = 0 -> max y z = y.
Proof.

Abort.

(*Exemple avec une induction qui passe bien *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros A H. induction l.
- snipe.
- snipe. 
Qed. 


(* Lemma rev_app_distr : forall (A : Type) (H : CompDec A) (x y: list A), List.rev (x ++ y)%list = (List.rev y ++ List.rev x)%list.
Proof. intros A. induction x.
- snipe @app_nil_r. *)



(* forall l, (exists x, (hd_error l = Some x)) -> negb (l ====? nil) .
Proof.
intros. destruct H.
apply triple_eq_is_eq in H. 
verit  hd_error_def_nil  some_neq_none cons_neq_nil H   (* cons_neq_nil is necessary *).   
Qed.*)
