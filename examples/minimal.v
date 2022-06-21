From SMTCoq Require Import SMTCoq.
Require Import List.
Require Import Bool.
Require Import ZArith.
Import ListNotations.

Section demo.

 Variable A : Type.
 Variable HA : CompDec A.
 Lemma HlA : CompDec (list A). auto with typeclass_instances. Qed.

 Lemma inh: A. apply Inh. Qed.

 Variable app_def_nil_bool: forall (l : list A), eqb_of_compdec HlA (app [] l) l.
 Variable app2_def_cons_bool: forall
 (x: A) (l l': list A), eqb_of_compdec HlA ((x :: l) ++ l') (x :: (l ++ l')).
 Variable list_inj_bool: forall (x x' : A) (l l' : list A),
  (eqb_of_compdec HlA (x :: l) (x :: l')) ---> (eqb_of_compdec HA x x') && (eqb_of_compdec HlA l l').
 Variable list_disj_bool: forall (x : A) (l : list A), negb (eqb_of_compdec HlA [] (x::l)).
 Variable proj_21 : A -> list A -> A.
 Variable proj_22 : list A -> list A -> list A. 
 Variable gen_list_bool : forall (l : list A), (eqb_of_compdec HlA l []) ||
  (eqb_of_compdec HlA l ((proj_21 inh l) :: (proj_22 [] l))).

(*  Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. scope. Qed. *)

Theorem app_eq_unit_bool:
    forall (x y: list A) (a:A),
      (eqb_of_compdec HlA (x ++ y) [a]) ---> 
      (((eqb_of_compdec HlA x []) && (eqb_of_compdec HlA y [a])) || 
      ((eqb_of_compdec HlA x [a]) && (eqb_of_compdec HlA y []))).
  Proof. verit_bool. Qed.

End demo.