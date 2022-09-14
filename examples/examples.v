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


(* If you have Sniper installed, change these two lines into:
   From Sniper Require Import Sniper.
   From Sniper Require Import tree.
*)
Require Import Sniper.
Require Import tree.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Require Import OrderedType Psatz.
Import ListNotations.

Section Paper_examples.

  Section Simple_examples.

  Variable A: Type.
  Variable HA: CompDec A.
  
  Lemma app_length (l l' : list A) : length (l ++ l') = (length l + length l')%nat.
  Proof. induction l ; snipe. Qed.

  Lemma app_eq_nil (l l' : list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. snipe. Qed.

  Lemma arith_and_uninterpreted_symbol (T : Type) (HT : CompDec T)
  (x y : nat) (b : bool) (f : nat -> T) :
    True /\ b = true \/ f (x + y ) = f (y + x ).
    Proof. snipe. Qed.

  End Simple_examples.

  Section Polymorphism.
  
  (* In this section, we illustrate the two ways of instantiating 
  lemmas: 
  - one version uses as ground terms all the terms of type Type in the goal
  - the other version uses the parameters of polymorphic terms as instances *)

Tactic Notation "inst_with_subterms_of_type_type" := inst.
Tactic Notation "inst_with_chosen_parameters" := elimination_polymorphism.

(*  Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : list B), 
 (x1 = x2 /\ y1 = y2) -> x1 =x2) -> ((forall (x1 x2 : bool) (y1 y2 : list Z), 
(x1 = x2 /\ y1 = y2) -> x1 =x2) /\ (forall (x1 x2 : Z) (y1 y2 : list unit), 
(x1 = x2 /\ y1 = y2) -> x1 =x2) /\ (forall (x1 x2 : bool) (y1 y2 : list bool), 
(x1 = x2 /\ y1 = y2) -> x1 =x2)).
Proof. intros. inst. split ; [|split]. Undo. verit. *)

  Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
      (x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> 
((forall (x1 x2 : unit*Z) (y1 y2 : list Z), (x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ 
(forall (x1 x2 : int) (y1 y2 : option Z), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
Proof. intro H. inst_with_subterms_of_type_type. (* 64 instances *)
Undo. inst_with_chosen_parameters. (* 7 instances *) 
split; [ |split]; verit. 
Qed. 

End Polymorphism.

  (*** Examples from CompCert ***)

  Section CompCert.

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


  Section CD_memory_chunk.

    Scheme Equality for memory_chunk.

    Lemma memory_chunk_beq_spec x y : memory_chunk_beq x y = true <-> x = y.
    Proof.
      split.
      - apply internal_memory_chunk_dec_bl.
      - apply internal_memory_chunk_dec_lb.
    Qed.

    Definition memory_chunk_to_Z mc :=
      match mc with
      | Mint8signed => 0%Z
      | Mint8unsigned => 1
      | Mint16signed => 2
      | Mint16unsigned => 3
      | Mint32 => 4
      | Mint64 => 5
      | Mfloat32 => 6
      | Mfloat64 => 7
      | Many32 => 8
      | Many64 => 9
      end.

    Lemma memory_chunk_to_Z_eq x y : x = y <-> memory_chunk_to_Z x = memory_chunk_to_Z y.
    Proof.
      case x; case y; unfold memory_chunk_to_Z; simpl; split;
        try discriminate; reflexivity.
    Qed.

    Definition memory_chunk_lt x y := memory_chunk_to_Z x < memory_chunk_to_Z y.

    Lemma memory_chunk_lt_trans x y z :
      memory_chunk_lt x y -> memory_chunk_lt y z -> memory_chunk_lt x z.
    Proof. now apply Z.lt_trans. Qed.

    Lemma memory_chunk_lt_neq x y : memory_chunk_lt x y -> x <> y.
    Proof.
      case x; case y; unfold memory_chunk_lt; simpl; intros H1 H2;
        try discriminate H2; discriminate H1.
    Qed.

    Definition memory_chunk_compare x y : Compare memory_chunk_lt eq x y.
    Proof.
      case_eq (memory_chunk_beq x y); intro Heq.
      - apply EQ. now apply internal_memory_chunk_dec_bl.
      - case_eq (Z.ltb (memory_chunk_to_Z x) (memory_chunk_to_Z y)); intro Hlt.
        + apply LT. unfold memory_chunk_lt. now rewrite <- Z.ltb_lt.
        + apply GT. unfold memory_chunk_lt. rewrite Z.ltb_ge in Hlt.
          assert (H:memory_chunk_to_Z x <> memory_chunk_to_Z y).
          { intro H. rewrite <- memory_chunk_to_Z_eq in H.
            apply internal_memory_chunk_dec_lb in H.
            rewrite H in Heq. discriminate.
          }
          lia.
    Defined.

    Definition memory_chunk_inh := Mint8signed.

  End CD_memory_chunk.

  Instance CD_memory_chunk : CompDec memory_chunk :=
    CompDec_from _ _ memory_chunk_beq_spec _ memory_chunk_lt_trans memory_chunk_lt_neq
                 memory_chunk_compare memory_chunk_inh.


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


  Section CD_permission.

    Scheme Equality for permission.

    Lemma permission_beq_spec x y : permission_beq x y = true <-> x = y.
    Proof.
      split.
      - apply internal_permission_dec_bl.
      - apply internal_permission_dec_lb.
    Qed.

    Definition permission_to_Z mc :=
      match mc with
      | Freeable => 0%Z
      | Writable => 1
      | Readable => 2
      | Nonempty => 3
      end.

    Lemma permission_to_Z_eq x y : x = y <-> permission_to_Z x = permission_to_Z y.
    Proof.
      case x; case y; unfold permission_to_Z; simpl; split;
        try discriminate; reflexivity.
    Qed.

    Definition permission_lt x y := permission_to_Z x < permission_to_Z y.

    Lemma permission_lt_trans x y z :
      permission_lt x y -> permission_lt y z -> permission_lt x z.
    Proof. now apply Z.lt_trans. Qed.

    Lemma permission_lt_neq x y : permission_lt x y -> x <> y.
    Proof.
      case x; case y; unfold permission_lt; simpl; intros H1 H2;
        try discriminate H2; discriminate H1.
    Qed.

    Definition permission_compare x y : Compare permission_lt eq x y.
    Proof.
      case_eq (permission_beq x y); intro Heq.
      - apply EQ. now apply internal_permission_dec_bl.
      - case_eq (Z.ltb (permission_to_Z x) (permission_to_Z y)); intro Hlt.
        + apply LT. unfold permission_lt. now rewrite <- Z.ltb_lt.
        + apply GT. unfold permission_lt. rewrite Z.ltb_ge in Hlt.
          assert (H:permission_to_Z x <> permission_to_Z y).
          { intro H. rewrite <- permission_to_Z_eq in H.
            apply internal_permission_dec_lb in H.
            rewrite H in Heq. discriminate.
          }
          lia.
    Defined.

    Definition permission_inh := Freeable.

  End CD_permission.

  Instance CD_permission : CompDec permission :=
    CompDec_from _ _ permission_beq_spec _ permission_lt_trans permission_lt_neq
                 permission_compare permission_inh.


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

  End CompCert.

End Paper_examples.


Local Open Scope Z_scope.


(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
Proof. snipe. Qed.


(* The `snipe` tactics requires instances of equality to be decidable.
   It is in particular visible with type variables. *)
Section Generic.

  Variable A : Type.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
    snipe.
    (* New goals are open that require instances of equality to be
       decidable. On usual types such as `Z` in the previous example,
       these goals are automatically discharged. On other concrete
       types, it is up to the user to prove it or admit it. *)
  Abort.

  (* On abstract type, it has to be assumed. *)
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. snipe. Qed.

End Generic.


(* When the goal is automatically provable by the `snipe` tactic, it is
   often done in a few seconds. To avoid too long runs when the goal is
   not provable, the tactic can be called with a timeout, in seconds. *)
Section Timeout.

  Variable A : Type.
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. (* snipe_timeout 10. *) snipe. Qed.

End Timeout.


(* A more involved example *)
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

Lemma length_app_auto : forall B (HB: CompDec B), forall (l1 l2 l3 : list B),
(length (l1 ++ l2 ++ l3)) = (length l1 + length l2 + length l3)%nat.
Proof. snipe app_length. Qed.

(* Example of searching an element in a list *)
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

Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s.
- snipe app_nil_r.
- snipe (app_ass, app_nil_r).
Qed.

Lemma rev_elements_node c (H: CompDec c) l x r :
 rev_elements c (Node l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. snipe (rev_elements_app, app_nil_r). Qed.
