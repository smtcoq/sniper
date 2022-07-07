From MetaCoq Require Import All.
Require Import utilities.
Require Import List.
Require Import String.


(** Examples for testing inductive predicates **)

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

Inductive Add {A : Type} (a : A) : list A -> list A -> Prop :=
  | Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').

Derive Inversion Add_inv with (forall n m k, add n m k) Sort Prop.

Print Add_inv.

MetaCoq Quote Recursively Definition add_reif_rec := add.

Definition add0_reif := <% add0 %>.
Definition addS_reif := <% addS %>.

Definition nil_reif := <% @nil %>.
Definition cons_reif := <% @cons %>.


MetaCoq Quote Recursively Definition Add_reif_rec := Add.

(** Transformation: we consider add as a function 
with a codomain in Prop. 
Each constructor is an equation for add.
In order to use an hypothesis of the form add n m k, we also 
generate an inversion principle: **)

Lemma inv_add : forall n m k, (add n m k <-> 
(exists (n' : nat), n = 0 /\ m = n' /\ k = n') \/
(exists (n' m' k' : nat), n = S n' /\ m = m' /\ k = (S k') /\ add n' m' k')).
Proof. 
intros n m k; split.
- intros H. inversion H ; [ left; repeat eexists ; auto | right ; repeat eexists; auto].
- intros H. destruct H as [H1 | H2].
 + destruct H1 as [n' [H11 [H12 H13]]]; subst; auto; constructor.
 + destruct H2 as [n' [m' [k' [H21 [H22 [H23 H24]]]]]]; subst; auto; constructor; assumption. Qed.

Definition ty_inv_add_reif := <% forall n m k, add n m k <->
(exists (n' : nat), n = 0 /\ m = n' /\ k = n') \/
(exists (n' m' k' : nat), n = S n' /\ m = m' /\ k = (S k') /\ add n' m' k') %>.


(** Generation of the equations **)


(* Definition for default value *)
Definition impossible_term_indu := 
{|
    inductive_mind :=
      (MPfile
         ["utilities"%string; "theories"%string; "Sniper"%string],
      "impossible_term"%string);
    inductive_ind := 0
  |}.

Definition get_ind_and_instance (I : term) :=
match I with
| tInd indu inst => (indu, inst)
| _ => (impossible_term_indu, [])
end.

Compute get_constructors_inductive add_reif_rec.2 add_reif_rec.1. (* TODO : make this work for mutuals *)

Ltac assert_list_constructors_aux l I I_reif i n :=
lazymatch l with
| nil => idtac
| cons ?p ?ps => let t := eval cbv in (subst10 I_reif p.1.2) in
               let t' := metacoq_get_value (tmUnquote t) in
               let TyC := eval cbv in t'.(my_projT2) in 
               let c := metacoq_get_value (tmUnquoteTyped TyC (tConstruct I n i)) in
               let H := fresh c in
               pose proof (H := c) ; assert_list_constructors_aux ps I I_reif i (S n)
end.

Ltac assert_list_constructors l I I_reif i := assert_list_constructors_aux l I I_reif i 0.
 
Ltac assert_types_constructors I := 
let I_reif_rec := metacoq_get_value (tmQuoteRec I) in 
let I_reif := eval cbv in I_reif_rec.2 in 
let list_constr_opt := eval cbv in (get_constructors_inductive I_reif I_reif_rec.1) in 
lazymatch list_constr_opt with
| Some ?list_constr =>
let p := eval cbv in (get_ind_and_instance I_reif) in
let indu := eval cbv in p.1 in
let inst := eval cbv in p.2 in
assert_list_constructors list_constr indu I_reif inst
| None => fail "wrong argument"
end.

Goal False.
assert_types_constructors add.
assert_types_constructors @Add.
clear. 
Abort.
