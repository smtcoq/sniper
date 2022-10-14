Require Import SMT_classes_instances.
Require Import List.


Lemma CNat : CompDec nat.
auto with typeclass_instances.
Qed.

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

Inductive add_linear : nat -> nat -> nat -> Prop :=
| add_linear0 : forall n m, eqb_of_compdec CNat n m = true -> add_linear 0 n m
| add_linearS : forall n m k, add_linear n m k -> add_linear(S n) m (S k).

Ltac elim_eq :=
repeat match goal with
| H : eqb_of_compdec ?T ?x ?y = true |- _ => apply compdec_eq_eqb in H
end.


Ltac intros_until_last :=
lazymatch goal with
| |- forall (x : ?T) (y : ?U), _ => let _ := match goal with _ =>
let y := fresh in intro y end in intros_until_last
| |- forall (x : ?U), _ => let x := fresh in 
let _ := match goal with _ => intro x end 
in constr:(x)
end.

(* Tactic Notation "find_right_constructor" int_or_var(i) := 
let rec tac_rec i :=
match goal with
| |- ?G => first [constructor i ; idtac i ; idtac G ; repeat (try assumption) ; match goal with
      | |- eqb_of_compdec ?T ?x ?y = true => idtac 3 ; constr_eq x y ; repeat (rewrite <- compdec_eq_eqb ; 
reflexivity) ; idtac "bar"
end | tac_rec (i+1)]
end
in tac_rec i.  TODO : ça mais en Caml et avec plutôt le numéro du but *)

Ltac correction_auto := 
let H := intros_until_last in induction H; elim_eq; subst ; constructor ; repeat (try assumption).

Ltac completeness_auto := 
let H := intros_until_last in induction H;
constructor;
solve [rewrite <- compdec_eq_eqb; reflexivity | assumption].


(* TODO : checher les autres lemmes de correction quand le prédicat inductif utilise un autre prédicat inductif *)

Lemma add_linear_correct : forall n1 n2 n3, add_linear n1 n2 n3 -> add n1 n2 n3.
Proof.
correction_auto.
Qed.

Lemma add_linear_complete : forall n1 n2 n3, add n1 n2 n3 -> add_linear n1 n2 n3.
completeness_auto. 
Qed.

Section lists.
Import ListNotations.
Variable A : Type.
Variable HA : CompDec A.
Lemma CListA : CompDec (list A).
auto with typeclass_instances.
Qed.
 Inductive Add (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').

 Inductive Add_interm (a: A) : list A -> list A -> Prop :=
    | Add_interm_head : forall x, eqb_of_compdec HA a x = true -> forall l l', eqb_of_compdec CListA l l' = true -> Add_interm a l (x :: l')
    | Add_interm_cons : forall x y, eqb_of_compdec HA x y = true -> forall l l', Add_interm a l l' -> Add_interm a (x ::l) (y::l').


Lemma Add_linear_correct : forall a l l', Add_interm a l l' -> Add a l l'.
Proof.
correction_auto.
Qed.

Lemma Add_linear_complete : forall a l l', Add a l l' -> Add_interm a l l'.
Proof.
completeness_auto.
Qed.
End lists.
