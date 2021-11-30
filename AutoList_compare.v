Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
Require Import Sniper.Sniper.
Require Setoid.
Require Import BinInt.
Require Import PeanoNat Le Gt Minus Bool Lt.
Require Import List.


Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [Init/Datatypes],
    as well as the definitions of [length] and [app] *)

Open Scope list_scope.

Import ListNotations.

Section Lists.

  Variable A : Type.
  Variable a_0 : A.
  Variable HA : CompDec A.

  (** Head and tail *)

  Definition hd (default:A) (l:list A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list A) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list A) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

  (** The boolean In *)
  Fixpoint Inb (a:A) (l:list A) : bool :=
    match l with
      | [] => false
      | b :: m => orb (eqb_of_compdec HA a b) (Inb a m)
    end.



  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    Time snipe1. Undo. Time snipe2. 
  Qed.


  (** Destruction *)

 (* Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof.
 Time snipe1. Undo.
 Time snipe2. Qed. *)

  Variable a : A.

 Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
 Time snipe1. Undo. Time snipe2.
  Qed.

  Fixpoint length (l : list A) :=  match l with
      | [] => 0
      | x :: xs => 1 + length xs
    end.

 (* Theorem length_zero_iff_nil : forall (l : list A),
   length l <> 0 <-> l <> nil.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed. *)


  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.


  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  (* Theorem in_eq : forall (a:A) (l:list A), Lists.Inb a (a :: l) = true.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed. *)

  Theorem in_cons : forall (a b:A) (l:list A), Lists.Inb b l = true -> Lists.Inb b (a :: l) = true.
  Proof.
  Time snipe1. Undo. Time snipe2. 
  Qed.

  Theorem not_in_cons (x b : A) (l : list A):
    ~ Lists.Inb x (a::l) = true <-> x<>a /\ ~ Lists.Inb x l = true.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.

  Theorem in_nil : forall a:A, ~ Lists.Inb a nil.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list A), Lists.Inb b (a :: l) -> a = b \/ Lists.Inb b l.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.



  (**************************)
  (** *** Facts about [app] *)
  (**************************)



  (** Discrimination *)
  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.

  (* Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
    Time induction l ; snipe1. Undo. Time induction l ; snipe2.
  Qed. *)

  (* begin hide *)
  (* Deprecated *)
  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. Time snipe1 app_nil_r. Undo. Time snipe2 app_nil_r. Qed. 



  (** [app] is associative *)
  Theorem app_assoc : forall l m n:list A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
    Time intros l ; induction l ; snipe1. Undo.
    Time intros l ; induction l ; snipe2.
  Qed. 

  Theorem app_assoc_reverse : forall l m n:list A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
     Time snipe1 app_assoc. Undo.
     Time snipe2 app_assoc.
    Qed.

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons : forall (x y:list A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  Time snipe1. Undo. Time snipe2.
  Qed.

  (** Facts deduced from the result of a concatenation *)

(*   Theorem app_eq_nil' : forall l l':list A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof.
  Time snipe1. Undo. Time snipe2. Qed. *)
    

  (*  Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
  Time snipe1. Undo. Time snipe2. Qed. *)

  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
  Proof.
    Time induction l; snipe1 app_comm_cons. Undo. 
    Time induction l ; snipe2 app_comm_cons. Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> or (Inb a l) (Inb a m).
  Proof.
Admitted.

  Lemma in_or_app : forall (l m:list A) (a:A), or (Inb a l) (Inb a m) -> Inb a (l ++ m).
  Proof.
Admitted.

  Lemma in_app_iff : forall l l' (a:A), Inb a (l++l') <-> or (Inb a l) (Inb a l').
  Proof.
   Time snipe1 (in_app_or, in_or_app). Undo. Time snipe2 (in_app_or, in_or_app). Qed.

 (*  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    Time induction l ; snipe1. Undo.
    Time induction l ; snipe2. Qed. *)

Section Elts.


  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end.
(*  Lemma nth_S_cons :
    forall (n:nat) (l:list A) (d a:A),
      Inb (nth n l d) l -> Inb (nth (S n) (a :: l) d) (a :: l).
  Proof.
   Time snipe1. Undo. Time snipe2. Qed. *)