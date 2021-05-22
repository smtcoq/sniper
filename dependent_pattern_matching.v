Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Import ListNotations.
Require Import String.


Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons _ x ls1' => Cons _ x (app _ ls1' _ ls2)
    end.


Variable x : A.


Compute app 0 Nil 2 (Cons 1 x (Cons 0 x Nil)).



  Fixpoint inject (ls : list A) : ilist (Datatypes.length ls) :=
    match ls in (list _) return (ilist (Datatypes.length ls)) with
      | nil => Nil
      | h :: t => Cons _ h (inject t)
    end.


  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject _ t
    end.


MetaCoq Quote Recursively Definition app_reif := app.


Print app_reif.















