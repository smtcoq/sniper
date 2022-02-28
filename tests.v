(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* If you have installed Sniper, change this line into `Require Import Sniper.Sniper`. *)
Require Import Sniper.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import instantiate.
Import ListNotations.


Section tests.

Goal ((forall (A : Type) (l : list A),
length l = match l with
       | [] => 0
       | _ :: xs => S (length xs)
       end) -> True).
intro H. 
eliminate_dependent_pattern_matching H.
exact I.
Qed.

Definition true_hidden := true.
Definition definition_no_variables := if true_hidden then 1=1 else 2=2.

Goal definition_no_variables -> True.
scope.
Abort.


Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)).
def_and_pattern_matching_mono prod_types.
assumption.
Qed.

Lemma if_var_in_context x y : (if Nat.eqb x y then x = x else y = y) -> True.
intros H.
scope.
Abort.

Goal forall (l : list Z) (x : Z) (a: bool),  hd_error l = Some x -> (l <> []).
Proof.
intros ; let p:= eval unfold prod_types in prod_types in interp_alg_types_context_goal p. 
def_and_pattern_matching_mono prod_of_symb.     
verit.
Qed.

Lemma nth_default_eq :
    forall (A : Type) (HA : CompDec A) n l (d:A), nth_default d l n = nth n l d.
  Proof. intros A HA n ; induction n. 
  - snipe.
  - intros l ; destruct l.
    * snipe.
    * scope. get_eliminators_st (option). specialize (H A a). verit.
 Qed.

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. inst. split. assumption. split. assumption. assumption.
Qed. 

(* Test eliminators, two versions *)
Variable A : Type.
Variable a : A.

Goal forall (n : nat) (l : list A)(x : A) (xs: list A), l = nil \/ l = cons x xs.
Proof. 
get_eliminators_in_goal.
Abort.

Goal
  forall s1 s2 : string, s1 = s2.
Proof.
get_eliminators_in_goal.
clear. intros s1 s2.
let p:= eval unfold prod_types in prod_types in get_eliminators_in_variables p.
Abort.


Goal forall (n : nat) (l : list A)(x : A) (xs: list A), True -> (l = nil \/ l = cons x xs \/ n = 0).
intros. let p:= eval unfold prod_types in prod_types in get_eliminators_in_variables p. 
Abort.

Variable HA : CompDec A.

Definition search := 
fix search {A : Type} {H : CompDec A} (x : A) (l : list A) {struct l} : bool :=
  match l with
  | [] => false
  | x0 :: l0 => orb (eqb_of_compdec H x x0) (search x l0)
  end.

Local Open Scope list_scope.
Import ListNotations. 

Lemma search_append_neq : 
forall l1 l2 l3 x, search x (l1 ++ l2) <> search x l3 -> l1 ++ l2 <> l3.
Proof.
  snipe. Qed.


Open Scope list_scope.

Import ListNotations.
  Variable a_0 : A.

  (** The boolean In *)
  Fixpoint Inb (a:A) (l:list A) : bool :=
    match l with
      | [] => false
      | b :: m => orb (eqb_of_compdec HA a b) (Inb a m)
    end.

  Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    snipe. 
  Qed.

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. 
  snipe. Qed.

 Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
  snipe.
  Qed.

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
  snipe. 
  Qed.

  Theorem in_eq : forall (a:A) (l:list A), Inb a (a :: l) = true.
  Proof.
  snipe. 
  Qed.

  Theorem in_cons : forall (a b:A) (l:list A), Inb b l = true -> Inb b (a :: l) = true.
  Proof.
  snipe.  
  Qed.

  Theorem not_in_cons (x b : A) (l : list A):
    ~ Inb x (a::l) = true <-> x<>a /\ ~ Inb x l = true.
  Proof.
  snipe. 
  Qed.

  Theorem in_nil : forall a:A, ~ Inb a nil.
  Proof.
  snipe. 
  Qed.

  Lemma in_inv : forall (a b:A) (l:list A), Inb b (a :: l) -> a = b \/ Inb b l.
  Proof.
  snipe. 
  Qed.

  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  snipe.
  Qed.

  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
  snipe. 
  Qed.

  Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
    induction l ; snipe. 
  Qed.

  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. snipe app_nil_r. Qed.

  Theorem app_assoc : forall l m n:list A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
    intros l ; induction l ; snipe.
  Qed. 

  Theorem app_assoc_reverse : forall l m n:list A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
     snipe app_assoc. Qed.

  Theorem app_comm_cons : forall (x y:list A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  snipe. 
  Qed.

  Theorem app_eq_nil' : forall l l':list A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof.
  snipe.  Qed.

   Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
  snipe. Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    induction x ; snipe.
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> or (Inb a l) (Inb a m).
  Proof.
    intros l m b. induction l; snipe.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    induction l ; snipe. Qed.

(* Test no_check version *)
Goal forall (l : list A), l = [] -> hd_error l = None.
snipe_no_check. Qed.

End tests.
