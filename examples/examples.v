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
From Sniper Require Import tree.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.


Local Open Scope Z_scope.

(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
Proof. snipe. Qed.

(* The `snipe` and `snipe_no_check` tactics requires instances of equality to be decidable.
   It is in particular visible with type variables. *)
Section Generic.

  Variable A : Type.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof.
   scope. 3: verit. 
    (* New goals are open that require instances of equality to be
       decidable. On usual types such as `Z` in the previous example,
       these goals are automatically discharged. On other concrete
       types, it is up to the user to prove it or admit it. *)
  Abort.

  (* On abstract type, it has to be assumed. *)
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. snipe_no_check. Qed.

End Generic.


(* When the goal is automatically provable by the `snipe` tactic, it is
   often done in a few seconds. To avoid too long runs when the goal is
   not provable, the tactic can be called with a timeout, in seconds. *)
Section Timeout.

  Variable A : Type.
  Hypothesis HA : CompDec A.
  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> nil).
  Proof. (* snipe_timeout 10. *) snipe_no_check. Qed.

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
  Proof. snipe_no_check. Qed.


End destruct_auto.

Section search.

Variable (A: Type).
Variable (H : CompDec A).


(* Example of searching an element in a list *)
Fixpoint search (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => eqb_of_compdec H x x0 || search x l0
  end.

Lemma search_app : forall (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
  intros x l1 l2. induction l1 as [ | x0 l0 IH].
  - reflexivity.
  - simpl. destruct (eqb_of_compdec H x x0).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* The proof of this lemma, except induction, can be automatized *)
Lemma search_app_snipe : forall (x: A) (l1 l2: list A),
    @search x (l1 ++ l2) = ((@search x l1) || (@search x l2))%bool.
Proof. induction l1 ; snipe_no_check. Qed. 


(* Manually using this lemma *)
Lemma search_lemma : forall (x: A) (l1 l2 l3: list A),
    search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
  intros x l1 l2 l3. rewrite !search_app.
  rewrite orb_comm with (b1 := search x l3).
  rewrite orb_comm  with (b1 := search x l2) (b2 := search x l1 ).
  rewrite orb_assoc.
  reflexivity.
Qed.

(* It can be fully automatized *)
Lemma snipe_search_lemma : forall (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. pose proof search_app. snipe_no_check. Qed.

Lemma in_inv : forall (a b:A) (l:list A),
    search b (a :: l) -> orb (eqb_of_compdec H a b) (search b l).
Proof. snipe. Qed.


(*  Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros ; induction l; snipe_no_check. Qed. 

End search.

Section higher_order.


Variable A B C: Type.
Variable HA : CompDec A.
Variable HB : CompDec B.
Variable HC : CompDec C.


Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; time snipe. Qed.

End higher_order.

(** Examples on trees *)

Section Tree. 


Lemma empty_tree_Z2 : forall (t : @tree Z) a t' b,
is_empty t = true -> t <> Node a t' b.
Proof. snipe. Qed.

Lemma rev_elements_app :
 forall A (H:CompDec A) s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A H s ; induction s. 
- pose proof List.app_nil_r; snipe.
- pose proof app_ass ; pose proof List.app_nil_r; snipe. 
Qed.

Lemma rev_elements_node c (H: CompDec c) l x r :
 rev_elements c (Node l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. pose proof app_ass ; pose proof rev_elements_app ; snipe. Qed.

End Tree.

Section RefinementTypes.

  (* Source: CompCert (https://github.com/AbsInt/CompCert/blob/bf8a3e19dcdd8fec1f8b49e137262c7280d6d8a8/lib/IntvSets.v#L326)  *)
  (* Note: we did modify the example *)
  Inductive data : Type := Nil | Cons (lo hi: Z) (tl: data).

  (* The original version of this was an equivalent function returning `Prop` *)
  Fixpoint InBool (x: Z) (s: data) : bool :=
    match s with
    | Nil => false
    | Cons l h s' => ((Z.leb l x) && (Z.ltb x h)) || InBool x s'
    end.

  (* The original version of this was an equivalent function returning `Prop` *)
  Fixpoint ok (x : data) : bool :=
    match x with
      | Nil => true
      | Cons l1 h1 s =>
          match s with
          | Nil => l1 <? h1
          | Cons l2 _ _ => (l1 <? h1) && (h1 <? l2) && (ok s)
          end
    end.


  (* Fixpoint eqb (d1 : data) (d2 : data) := *)
  (*   match d1, d2 with *)
  (*     | Cons l1 h1 tl1, Cons l2 h2 tl2 => Z.eqb l1 l2 && Z.eqb h1 h2 && eqb tl1 tl2 *)
  (*     | Nil, Nil => true *)
  (*     | _, _ => false *)
  (*   end. *)

  (* Theorem eqb_spec : forall d1 d2 : data , eqb d1 d2 = true <-> d1 = d2. *)
  (*   intros d1 d2. *)
  (*   split. *)
  (*   intro H. *)
  (*   destruct d1. *)
  (*   - destruct d2. *)
  (*     + reflexivity. *)
  (*     + discriminate H. *)
  (*   - destruct d2. *)
  (*     + discriminate H. *)
  (*     + simpl in H. *)
  (*       case H. *)

  (* Instance eqbData : EqbType data := { *)
  (*   eqb := *)
  (*     fun (d1 d2 : data) => *)
  (*       match d1, d2 with *)
  (*         | _, _ => false *)
  (*       end *)
  (*   eqb_spec *)
  (* }. *)

  (* Program Definition ordData : OrdType data. admit. Admitted. *)

  (* Program Definition compData : @Comparable data ordData. admit. Admitted. *)

  (* Program Definition inhData : Inhabited data. admit. Admitted. *)

  (* Instance compDecData : CompDec data := *)
  (*   { Eqb := eqbData ; Ordered := ordData ; Comp := compData ; Inh := inhData }. *)

  (* Three modifications: *)
  (*   1 - Use boolean version of lt (`Z.ltb` instead of `Z_lt_dec`) *)
  (*   2 - Put the `exist` on the top of the term (`exist if ...` instead of `if (..) then exist (..) else exist (..)) *)
  (*   3 - Don't use an alias for the refinement type, inline it in the return type of `interval` *)
  Axiom foo : forall l h , ok (if l <? h then Cons l h Nil else Nil).
  Program Definition interval (l h: Z) : { r : data | ok r } :=
    exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.
  Next Obligation.
    exact (foo l h).
  Defined.

  Program Definition InBoolRef (x : Z) (s : {r : data | ok r }) : bool := InBool x s.

  Goal forall l h , (proj1_sig (interval l h) = Nil) \/ (l <? h = true).
    intros l h.
    scope.
    - admit.
    - verit.
  Abort.

  Goal forall x l h, (InBoolRef x (interval l h) = true) <-> l <= x < h.
    intros x l h.
    split.
    - intro h2.
      scope.
      + admit.
      + verit.
    - intro h2.
      scope.
      + admit.
      + verit.
       admit.
  Abort.

End RefinementTypes.
