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
Require Import tree.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Section Paper_examples.

  Variable A : Type.
  Variable HA : CompDec A.

  Lemma app_length (l l' : list A) : length (l ++ l') = (length l + length l')%nat.
  Proof. induction l ; snipe. Qed.

  Lemma app_eq_nil (l l' : list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. snipe. Qed.
  
  Lemma arith_and_uninterpreted_symbol (T : Type) (HT : CompDec T)
  (x y : nat) (b : bool) (f : nat -> T) :
    True /\ b = true \/ f (x + y ) = f (y + x ).
    Proof. snipe. Qed.

  (*** Examples from CompCert ***)


  Local Open Scope Z_scope.

  Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)



  Instance CD_memory_chunk : CompDec memory_chunk. Admitted. 

  Definition size_chunk (chunk: memory_chunk) : Z :=
    match chunk with
    | Mint8signed => 1
    | Mint8unsigned => 1
    | Mint16signed => 2
    | Mint16unsigned => 2
    | Mint32 => 4
    | Mint64 => 8
    | Mfloat32 => 4
    | Mfloat64 => 8
    | Many32 => 4
    | Many64 => 8
    end.

  Lemma size_chunk_pos: forall chunk, size_chunk chunk > 0.
  Proof. snipe. Qed. 

  Inductive permission: Type :=
    | Freeable: permission
    | Writable: permission
    | Readable: permission
    | Nonempty: permission.

  Instance CD_permission : CompDec permission. Admitted.

  Definition perm_order p p'  :=
    match (p,p') with
    | (Writable, Writable) => true 
    | (Readable, Readable) => true
    | (Freeable, _) => true
    | (Writable, Readable) => true
    | (_, Nonempty) => true
    | _ => false
    end.

  (* transitivity is now automatically proved *)
  Lemma perm_order_trans:
    forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
  Proof. snipe. Qed.

End Paper_examples.


Local Open Scope Z_scope.


(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
Proof. snipe. Qed.


(* The same, on any type who enjoys a decidable equality *)
Section Generic.

  Variable A : Type.
  Variable HA : CompDec A.

  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. snipe. Qed.
  
End Generic.

Section destruct_auto.

  Variable A : Type.
  Variable HA : CompDec A.


(* This theorem needs a case analysis on x and y *)
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

Theorem app_eq_unit_auto :
    forall (x y: list A) (a:A),
      x ++ y = a :: nil -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof. snipe. Qed.


End destruct_auto.


(* An example with polymorphism *)
Lemma length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat (length (l1 ++ l2)) =? Z.of_nat (length l1) + Z.of_nat (length l2)).
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
Proof. intros A H x l1 l2. induction l1 as [ | x0 l0 IH]; simpl; snipe. Qed.


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



