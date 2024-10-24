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

From Sniper Require Import Sniper.
From Sniper Require Import Transfos.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

Section poly.


Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C),
let f0 := fun x : A => (f x, g x) in
let f1 := @map A (B * C) f0 in
let f2 := @map A B f in
let f3 := @map A C g in
(forall (H5 H7 : Type) (l' : list H7), @zip H5 H7 [] l' = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7), @zip H7 H9 (H10 :: H11) [] = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7) (h : H9) (l : list H9),
 @zip H7 H9 (H10 :: H11) (h :: l) = (H10, h) :: @zip H7 H9 H11 l) ->
f1 [] = [] ->
(forall (a : A) (l : list A), f1 (a :: l) = f0 a :: f1 l) ->
f2 [] = [] ->
(forall (a : A) (l : list A), f2 (a :: l) = f a :: f2 l) ->
f3 [] = [] ->
(forall (a : A) (l : list A), f3 (a :: l) = g a :: f3 l) ->
(forall (x : Type) (x0 x1 : x) (x2 x3 : list x), x0 :: x2 = x1 :: x3 -> x0 = x1 /\ x2 = x3) ->
(forall (x : Type) (x0 : x) (x1 : list x), [] = x0 :: x1 -> False) ->
(forall (x x0 : Type) (x1 x2 : x) (x3 x4 : x0), (x1, x3) = (x2, x4) -> x1 = x2 /\ x3 = x4) ->
f1 [] = @zip B C (f2 []) (f3 [])).
Proof. intros. elimination_polymorphism. Abort.

End poly.

Section tests_for_decidable_relations.

Variable (A : Type).
Variable (HA : CompDec A).

Fixpoint smaller_dec_bis (l l' : list A) :=
match l with
| nil => true
| cons x xs => false 
end
|| 
match l with
| nil => false
| cons x xs => match l' with
          | nil => false
          | cons x' xs' => smaller_dec_bis xs xs'
end
end.

Goal forall (l l' l'' : list A) (x : A), 
smaller_dec_bis l l' -> l' = [] -> l <> cons x l''.
Proof. snipe. Qed.

End tests_for_decidable_relations.

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
intros.
unfold definition_no_variables in H.
eliminate_dependent_pattern_matching H.
Abort.

Lemma if_var_in_context x y : (if Nat.eqb x y then x = x else y = y) -> True.
intros H.
scope.
Abort. 

Lemma nth_default_eq :
    forall (A : Type) (HA : CompDec A) n l (d:A), nth_default d l n = nth n l d.
Proof. intros A HA n ; induction n.
  - snipe.
  - intros l ; destruct l.
    * snipe.
    * scope. get_projs_st option. (* specialize (gen_option A d). *)
      (* verit does not succed because p and p0 are not Zified by trakt (see "Preprocessing" channel *)
Abort.

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. elimination_polymorphism. split. assumption. split. assumption. assumption.
Qed. 

(* Test projs  *)
Variable A : Type.
Variable a : A.

Goal forall (n : nat) (l : list A)(x : A) (xs: list A), l = nil \/ l = cons x xs.
Proof. 
get_projs_in_goal.
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
Time snipe. Qed.


Open Scope list_scope.

Import ListNotations.
  Variable a_0 : A.

  (** The boolean In *)
  Fixpoint Inb (a:A) (l:list A) : bool :=
    match l with
      | [] => false
      | b :: m => orb (eqb_of_compdec HA a b) (Inb a m)
    end.


(* 
  Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
  Time snipe.
  Abort. *)

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. Time snipe. 
 Qed.

 Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
  Time snipe_no_check.
  Qed.

Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
  Time snipe_no_check.
  Qed. 


 (* Theorem in_eq  : forall (a:A) (l:list A), Inb a (a :: l) = true.
  Proof.
  Time snipe. 
  Qed. *)

  Theorem in_cons : forall (a b:A) (l:list A), Inb b l = true -> Inb b (a :: l) = true.
  Proof.
  Time snipe_no_check. 
  Qed.

  Theorem not_in_cons (x b : A) (l : list A):
    ~ Inb x (a::l) = true <-> x<>a /\ ~ Inb x l = true.
  Proof.
  Time snipe_no_check. 
  Qed.

  Theorem in_nil : forall a:A, ~ Inb a nil.
  Proof.
  Time snipe_no_check. 
  Qed.

  Lemma in_inv : forall (a b:A) (l:list A), Inb b (a :: l) -> a = b \/ Inb b l.
  Proof.
  Time snipe. 
  Qed. 

  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  Time snipe_no_check.
  Qed.

  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
  Time snipe_no_check. 
  Qed.

  Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
   Time induction l ; snipe_no_check.
  Qed.

  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. pose proof app_nil_r. snipe_no_check. Qed.

  Theorem app_assoc : forall l m n:list A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
    Time intros l ; induction l ; snipe_no_check. 
  Qed. 

  Theorem app_assoc_reverse : forall l m n:list A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
  pose proof app_assoc. Time snipe_no_check.
  Qed.

  Theorem app_comm_cons : forall (x y:list A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  Time snipe_no_check.
  Qed.

  Theorem app_eq_nil' : forall l l':list A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof. 
  Time snipe_no_check. Qed.

   Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
  Time snipe_no_check. Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
  Time induction x ; snipe_no_check. 
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> or (Inb a l) (Inb a m).
  Proof.
    intros l m b. Time induction l; snipe_no_check.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    Time induction l ; snipe_no_check. Qed.

Goal forall (l : list A), l = [] -> hd_error l = None.
snipe_no_check. Qed.

End tests.

Section Pairs.
 Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

  Definition fst (p:A * B) := match p with (x, y) => x end.
  Definition snd (p:A * B) := match p with (x, y) => y end.

Lemma surjective_pairing :
  forall (p:A * B), p = (fst p, snd p).
Proof. Time snipe_no_check. Qed.

End Pairs.

Check N.

(* `expand_hyp` shouldn't rely on the body of the symbol, but on the proof of equality *)
Section expand_hyp_without_body.

Variable  x : nat.
Variable  f g : nat -> nat.
Variable  h1 : f 42 = 42.
Variable  h2 : g 42 = 42.
Variable  M : nat -> nat.
Variable  pf_refl : M = match x with | 0 => f | S _ => g end.

Goal M 42 = 42.
  scope.
  Abort.

End expand_hyp_without_body.

(* Testing interaction of `pose_case` with other transformations - verit won't conclude the goal due to silent simplification  *)
Goal forall (x : nat) (f g : nat -> nat) , (f 2 = 2) -> (g 2 = 2) -> ((match x with O => f | S _ => g end) 2 = 2).
Proof.
  scope.
  verit.
  Abort.

Set Default Proof Mode "Classic".

Definition p := fun x : nat => x > 3.

Program Definition k : nat -> sig p -> nat -> sig p -> nat -> sig p := fun _ _ _ _ _ => exist _ 4 _.
Next Obligation.
  unfold p.
  auto.
Qed.

Goal 4 > 3.
  elim_refinement_types k.
  assert (five: 5 > 3) by auto.
  exact (H 5 5 five 5 5 five 5).
Qed.

Fixpoint rep_sig (i : nat) : Set :=
  match i with
    | 0 => nat
    | S i' => @sig (rep_sig i') (fun x => x = x)
  end.

Goal True.
  convert_sigless h (rep_sig 100).
  trivial.
Qed.

Section CompCertExample.

  Local Open Scope Z_scope.

  (* The trigger does not work up to delta conversion, but the tactic does *)
  Inductive data : Type := Nil | Cons (lo hi: Z) (tl: data).

  Fixpoint ok (x : data) : bool :=
    match x with
      | Nil => true
      | Cons l1 h1 s =>
          match s with
          | Nil => l1 <? h1
          | Cons l2 _ _ => (l1 <? h1) && (h1 <? l2) && (ok s)
          end
    end.

  (* TODO: Currently we use Variable, but this is provable. *)
  Variable intervalOk : forall l h , ok (if l <? h then Cons l h Nil else Nil).

  (* TODO: Currently we use Variable, but this is provable. *)
  Variable compDecData : CompDec data.

  Definition refData := { r : data | ok r }.

  Program Definition interval (l h: Z) : refData :=
    exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.

  Goal forall l h , (proj1_sig (interval l h) = Nil) \/ (l <? h = true).
    intros l h.
    elim_refinement_types interval.
    snipe.
  Qed.

End CompCertExample.
