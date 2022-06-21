(** Demonstration pour la présentation aux Journées Francophones des 
Langages Applicatifs **)

Add Rec LoadPath "../theories" as Sniper.theories.
Require Import Sniper.theories.Sniper.
Require Import List.
Require Import Bool.
Require Import ZArith.
Import ListNotations.


(* Section demo_definitions_trakt.

 Variable A : Type.
 Variable HA : CompDec A.

(*  Variable length2 : list A -> Z.

 Variable app_def_nil_bool: forall (l : list A), eqb_of_compdec _ ([] ++ l) l.
 Variable app_def_cons_bool: forall  (x: A) (l l': list A), eqb_of_compdec _
    ((x :: l) ++ l') (x :: (l ++ l')).
 Variable length2_def_nil_bool : eqb_of_compdec _ (length2 (@nil A)) 0%Z.
 Variable length2_def_cons_bool : forall (x: A) (l : list A),
    eqb_of_compdec _ (length2 (x :: l)) (Z.add 1%Z (length2 l)).

  Lemma app_length_bool (l l' : list A) : 
  eqb_of_compdec _ (length2 (l ++ l')) (length2 l + length2 l')%Z.
  Proof. induction l ; verit_bool. Qed. *)

(*  Variable app_def_nil: forall (l : list A), [] ++ l = l.
 Variable app_def_cons: forall  (x: A) (l l': list A), (x :: l) ++ l' = x :: (l ++ l').
 Variable length_def_nil : length (@nil A) = 0.
 Variable length_def_cons : forall (x: A) (l : list A), length (x :: l) = S (length l).

 Lemma app_length (l l' : list A) : length (l ++ l') = (length l + length l')%nat.
  Proof. induction l ; verit. Qed. *)

Lemma app_length (l l' : list A) : length (l ++ l') = (length l + length l')%nat.
  Proof. induction l ; snipe. Qed.

End demo_definitions_trakt. *)

Section demo.

 Variable A : Type.
 Variable HA : CompDec A.
 Variable HlA : CompDec (list A).
(*  Lemma HlA : CompDec (list A). auto with typeclass_instances. Qed. *)


(*  Variable app_def_nil_bool: forall (l : list A), eqb_of_compdec HlA (app [] l) l.
 Variable app_def_cons_bool: forall
 (x: A) (l l': list A), eqb_of_compdec HlA ((x :: l) ++ l') (x :: (l ++ l')).
 Variable list_inj_bool: forall (x x' : A) (l l' : list A),
  (eqb_of_compdec HlA (x :: l) (x :: l')) ---> (eqb_of_compdec HA x x') && (eqb_of_compdec HlA l l').
 Variable list_disj_bool: forall (x : A) (l : list A), negb (eqb_of_compdec HlA [] (x::l)).
 Variable proj_21 : A -> list A -> A.
 Variable proj_22 : list A -> list A -> list A. 
 Variable gen_list_bool : forall (l : list A), (eqb_of_compdec HlA l []) ||
  (eqb_of_compdec HlA l ((proj_21 inh l) :: (proj_22 [] l))). *)

(* Theorem app_eq_unit_bool:
    forall (x y: list A) (a:A),
      (eqb_of_compdec HlA (x ++ y) [a]) ---> 
      (((eqb_of_compdec HlA x []) && (eqb_of_compdec HlA y [a])) || 
      ((eqb_of_compdec HlA x [a]) && (eqb_of_compdec HlA y []))).
  Proof. verit_bool. Qed. *)

 Variable app_def_nil: forall (l : list A), [] ++ l = l.
 Variable app2_def_cons: forall
 (x: A) (l l': list A),  ((x :: l) ++ l') = (x :: (l ++ l')).
 Variable list_inj : forall (x x' : A) (l l' : list A),
  (x :: l) = (x :: l') -> x = x' /\ l=l'.
 Variable list_disj: forall (x : A) (l : list A), ~ [] = (x::l).
 Variable proj_21' : A -> list A -> A.
 Variable proj_22' : list A -> list A -> list A. 
 Variable gen_list : forall (inh : A) (l : list A), l = [] \/
  l = (proj_21' inh l) :: (proj_22' [] l).

Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. snipe. Qed.



End demo.



 