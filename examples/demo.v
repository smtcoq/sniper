(** Demonstration pour la présentation aux Journées Francophones des 
Langages Applicatifs **)

Add Rec LoadPath "../theories" as Sniper.theories.
Require Import Sniper.theories.Sniper.
Require Import List.
Require Import Bool.
Import ListNotations.

Tactic Notation "get_projs_in_variables" := get_projs_in_variables unit.

Section demo.

 Variable A : Type.

 Theorem app_eq_unit (x y:list A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
    destruct x as [|a' l]; [ destruct y as [|a' l] | destruct y as [| a0 l0] ];
      simpl.
    intros H; discriminate H.
    left; split; auto.
    intro H; right; split; auto.
    generalize H.
    generalize (app_nil_r l); intros E.
    rewrite -> E; auto.
    intros H.
    injection H as [= H H0].
    assert ([] = l ++ a0 :: l0) as H1 by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

 Variable HA : CompDec A.
 Lemma HlA : CompDec (list A). auto with typeclass_instances. Qed.
 Lemma inh : A. Proof. apply Inh. Qed.

 (* Variable app_def_nil_bool: forall (l : list A), eqb_of_compdec HlA (app [] l) l.
 Variable app_def_cons_bool: forall
 (x: A) (l l': list A), eqb_of_compdec HlA ((x :: l) ++ l') (x :: (l ++ l')).
 Variable list_inj_bool: forall (x x' : A) (l l' : list A),
  (eqb_of_compdec HlA (x :: l) (x' :: l')) ---> (eqb_of_compdec HA x x') && (eqb_of_compdec HlA l l').
 Variable list_disj_bool: forall (x : A) (l : list A), negb (eqb_of_compdec HlA [] (x::l)).
 Variable proj_21 : A -> list A -> A.
 Variable proj_22 : list A -> list A -> list A. 
 Variable gen_list_bool : forall (l : list A), (eqb_of_compdec HlA l []) ||
  (eqb_of_compdec HlA l ((proj_21 inh l) :: (proj_22 [] l))). 

Theorem app_eq_unit_bool:
    forall (x y: list A) (a:A),
      (eqb_of_compdec HlA (x ++ y) [a]) ---> 
      (((eqb_of_compdec HlA x []) && (eqb_of_compdec HlA y [a])) || 
      ((eqb_of_compdec HlA x [a]) && (eqb_of_compdec HlA y []))).
  Proof. verit_bool. Qed. *)

(*  Variable app_def_nil: forall (l : list A), [] ++ l = l.
 Variable app2_def_cons: forall
 (x: A) (l l': list A),  ((x :: l) ++ l') = (x :: (l ++ l')).
 Variable list_inj : forall (x x' : A) (l l' : list A),
  (x :: l) = (x' :: l') -> x = x' /\ l=l'.
 Variable list_disj: forall (x : A) (l : list A), ~ [] = (x::l).
 Variable proj_21' : A -> list A -> A.
 Variable proj_22' : list A -> list A -> list A. 
 Variable gen_list : forall (inh : A) (l : list A), l = [] \/
  l = (proj_21' inh l) :: (proj_22' [] l).  *)

Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
intros x y a. 
get_def app.
expand_hyp app_def; clear app_def.
eliminate_fix_hyp H; clear H.
eliminate_dependent_pattern_matching H0.
interp_alg_types (list).
elimination_polymorphism.
get_projs_in_variables. verit.
Undo. clear - HA. snipe. Qed. 

End demo.





 