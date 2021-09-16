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
Require Import tree.
Require Import Bool.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.


(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> []).
Proof. snipe. Qed.


(* The same, on any type who enjoys a decidable equality *)
Section Generic.

  Variable A : Type.
  Variable HA : CompDec A.

  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> []).
  Proof. snipe. Qed.

End Generic.


(* An example with polymorphism *)
Lemma length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).
Proof.
intros A l1 l2.
apply Z.eqb_eq.
induction l1.
- reflexivity.
- simpl length.
  rewrite !Nat2Z.inj_succ.
  rewrite IHl1.
  rewrite Z.add_succ_l.
  reflexivity.
Qed.


Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s.
- snipe app_nil_r.
- snipe (app_ass, app_nil_r).
Qed.



Lemma rev_elements_node c (H: CompDec c) l x r :
 rev_elements c (Node l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. snipe (rev_elements_app, app_nil_r). Qed.


Lemma length_app_auto : forall B (HB: CompDec B), forall (l1 l2 l3 : list B),
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. snipe length_app. Qed.


(* Example of search an element in a list *)
Fixpoint search {A : Type} {H: CompDec A} (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => eqb_of_compdec H x x0 || search x l0
  end.

Lemma search_app : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
  intros A H x l1 l2. induction l1 as [ | x0 l0 IH].
  - reflexivity.
  - simpl. destruct (eqb_of_compdec H x x0).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* The proof of this lemma, except induction, can be automatized *)
Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof. intros A H x l1 l2. induction l1 as [ | x0 l0 IH]; simpl. interp_alg_types_context_goal. def_fix_and_pattern_matching  
+ prop2bool_hyp H3_bool  .
Qed.


(* Manually using this lemma *)
Lemma search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
    search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
  intros A H x l1 l2 l3. rewrite !search_app.
  rewrite orb_comm with (b1 := search x l3).
  rewrite orb_comm  with (b1 := search x l2) (b2 := search x l1 ).
  rewrite orb_assoc.
  reflexivity.
Qed.


(* It can be fully automatized *)
Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. intros A H. snipe @search_app. Qed.


(* Another example with search *)
Lemma in_inv : forall (A: Type) (HA : CompDec A) (a b:A) (l:list A),
    search b (a :: l) -> eqb_of_compdec HA a b \/ search b l.
Proof. intros A HA. snipe. Qed.


(* Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros A H; induction l; snipe. Qed.


(** Examples on trees *)

Lemma empty_tree_Z2 : forall (t : @tree Z) a t' b,
is_empty t = true -> t <> Node a t' b.
Proof. intros t a t' b; snipe. Qed.
