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
From Stdlib Require Import String ZArith Bool List.
Import ListNotations.


(* Test computing the maximum of a list.

   We go from simpler (everything is axiomatized in a simple way) to
   harder (we need to unfold functions, we do not use a standard
   comparison, etc).
 *)
Section Max_list.

  (* Simplest test *)
  Section ML0.
    Variable max_opt : option Z -> option Z -> option Z.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_None_Some : forall b,
        max_opt None (Some b) = Some b.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (a <? b)%Z then b else a).

    Variable max_list : list Z -> option Z -> option Z.
    Hypothesis max_list_nil : forall acc,
        max_list [] acc = acc.
    Hypothesis max_list_cons : forall x xs acc,
        max_list (x::xs) acc = max_list xs (max_opt acc (Some x)).
    Hypothesis max_list_app : forall l1 l2 acc,
        max_list (l1++l2) acc = max_list l2 (max_list l1 acc).

    Goal forall a b l,
        Some b = max_list l None ->
        Some (if (a <? b)%Z then b else a) = max_list (l ++ [a]) None.
    Proof.
      snipe.
    Qed.
  End ML0.

  (* Same as 0, but we use a let ... in ... in the definition of a function *)
  (* TODO: loops forever *)
  (* Section ML1. *)
  (*   Variable max_opt : option Z -> option Z -> option Z. *)
  (*   Hypothesis max_opt_None_None : *)
  (*     max_opt None None = None. *)
  (*   Hypothesis max_opt_Some_None : forall a, *)
  (*       max_opt (Some a) None = Some a. *)
  (*   Hypothesis max_opt_None_Some : forall b, *)
  (*       max_opt None (Some b) = Some b. *)
  (*   Hypothesis max_opt_Some_Some : forall a b, *)
  (*       max_opt (Some a) (Some b) = Some (if (a <? b)%Z then b else a). *)

  (*   Variable max_list : list Z -> option Z -> option Z. *)
  (*   Hypothesis max_list_nil : forall acc, *)
  (*       max_list [] acc = acc. *)
  (*   Hypothesis max_list_cons : forall x xs acc, *)
  (*     max_list (x::xs) acc = *)
  (*       let a := max_opt acc (Some x) in *)
  (*       max_list xs a. *)

  (*   Goal forall a b l, *)
  (*       Some b = max_list l None -> *)
  (*       Some (if (a <? b)%Z then b else a) = max_list (l ++ [a]) None. *)
  (*   Proof. *)
  (*     snipe. *)
  (*   Qed. *)
  (* End ML1. *)

  (* Same as 0, but the max_list function is defined and not axiomatized anymore *)
  Section ML2.
    Variable max_opt : option Z -> option Z -> option Z.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_None_Some : forall b,
        max_opt None (Some b) = Some b.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (a <? b)%Z then b else a).

    Fixpoint max_list2 (l:list Z) (acc:option Z) : option Z :=
      match l with
      | [] => acc
      | x::xs => max_list2 xs (max_opt acc (Some x))
      end.
    Lemma max_list2_app : forall l1 l2 acc,
        max_list2 (l1++l2) acc = max_list2 l2 (max_list2 l1 acc).
    Proof. induction l1 as [ |x xs IHxs]; simpl; auto. Qed.

    Goal forall a b l,
        Some b = max_list2 l None ->
        Some (if (a <? b)%Z then b else a) = max_list2 (l ++ [a]) None.
    Proof.
      generalize max_list2_app.
      snipe.
    Qed.
  End ML2.

  (* Same as 0, but we replace Z with an abstract type
     Commutativity of max_opt is now required
   *)
  Section ML3.
    Variable A : Type.
    Hypothesis CA : CompDec A.
    Variable lt : A -> A -> bool.

    Variable max_opt : option A -> option A -> option A.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (lt a b) then b else a).
    Hypothesis max_opt_comm : forall a b,
        max_opt a b = max_opt b a.

    Variable max_list : list A -> option A -> option A.
    Hypothesis max_list_nil : forall acc,
        max_list [] acc = acc.
    Hypothesis max_list_cons : forall x xs acc,
        max_list (x::xs) acc = max_list xs (max_opt acc (Some x)).
    Hypothesis max_list_app : forall l1 l2 acc,
        max_list (l1++l2) acc = max_list l2 (max_list l1 acc).

    Goal forall a b l,
        Some b = max_list l None ->
        Some (if (lt a b) then b else a) = max_list (l ++ [a]) None.
    Proof.
      snipe.
    Qed.
  End ML3.

  (* Combination of 2 and 3 *)
  Section ML23.
    Variable A : Type.
    Hypothesis CA : CompDec A.
    Variable lt : A -> A -> bool.

    Variable max_opt : option A -> option A -> option A.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (lt a b) then b else a).
    Hypothesis max_opt_comm : forall a b,
        max_opt a b = max_opt b a.

    Fixpoint max_list23 (l:list A) (acc:option A) : option A :=
      match l with
      | [] => acc
      | x::xs => max_list23 xs (max_opt acc (Some x))
      end.
    Lemma max_list23_app : forall l1 l2 acc,
        max_list23 (l1++l2) acc = max_list23 l2 (max_list23 l1 acc).
    Proof. induction l1 as [ |x xs IHxs]; simpl; auto. Qed.

    Goal forall a b l,
        Some b = max_list23 l None ->
        Some (if (lt a b) then b else a) = max_list23 (l ++ [a]) None.
    Proof.
      generalize max_list23_app.
      snipe.
    Qed.
  End ML23.

  (* Same as 2, but the max_list function is defined using an internal anonymous fixpoint *)
  Section ML4.
    Variable max_opt : option Z -> option Z -> option Z.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_None_Some : forall b,
        max_opt None (Some b) = Some b.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (a <? b)%Z then b else a).

    Definition max_list4 : list Z -> option Z -> option Z :=
      fix ml (l : list Z) (acc : option Z) {struct l} : option Z :=
        match l with
        | [] => acc
        | x::xs => ml xs (max_opt acc (Some x))
        end.
    Lemma max_list4_app : forall l1 l2 acc,
        max_list4 (l1++l2) acc = max_list4 l2 (max_list4 l1 acc).
    Proof. induction l1 as [ |x xs IHxs]; simpl; auto. Qed.

    Goal forall a b l,
        Some b = max_list4 l None ->
        Some (if (a <? b)%Z then b else a) = max_list4 (l ++ [a]) None.
    Proof.
      generalize max_list4_app.
      snipe.
    Qed.
  End ML4.

  (* Combination of 3 and 4 *)
  Section ML34.
    Variable A : Type.
    Hypothesis CA : CompDec A.
    Variable lt : A -> A -> bool.

    Variable max_opt : option A -> option A -> option A.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (lt a b) then b else a).
    Hypothesis max_opt_comm : forall a b,
        max_opt a b = max_opt b a.

    Definition max_list34 : list A -> option A -> option A :=
      fix ml (l : list A) (acc : option A) {struct l} : option A :=
        match l with
        | [] => acc
        | x::xs => ml xs (max_opt acc (Some x))
        end.
    Lemma max_list34_app : forall l1 l2 acc,
        max_list34 (l1++l2) acc = max_list34 l2 (max_list34 l1 acc).
    Proof. induction l1 as [ |x xs IHxs]; simpl; auto. Qed.

    Goal forall a b l,
        Some b = max_list34 l None ->
        Some (if (lt a b) then b else a) = max_list34 (l ++ [a]) None.
    Proof.
      generalize max_list34_app.
      snipe.
    Qed.
  End ML34.

  (* Same as 3, but uses a comparison function *)
  Section ML5.
    Variable A : Type.
    Hypothesis CA : CompDec A.
    Variable cmp : A -> A -> comparison.

    Variable max_opt : option A -> option A -> option A.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (comparison_eqb (cmp a b) Lt) then b else a).
    Hypothesis max_opt_comm : forall a b,
        max_opt a b = max_opt b a.

    Variable max_list : list A -> option A -> option A.
    Hypothesis max_list_nil : forall acc,
        max_list [] acc = acc.
    Hypothesis max_list_cons : forall x xs acc,
        max_list (x::xs) acc = max_list xs (max_opt acc (Some x)).
    Hypothesis max_list_app : forall l1 l2 acc,
        max_list (l1++l2) acc = max_list l2 (max_list l1 acc).

    Goal forall a b l,
        Some b = max_list l None ->
        Some (if (comparison_eqb (cmp a b) Lt) then b else a) = max_list (l ++ [a]) None.
    Proof.
      snipe.
    Qed.
  End ML5.

  (* Same as 5, but comparison is stated differently *)
  Section ML6.
    Variable A : Type.
    Hypothesis CA : CompDec A.
    Variable cmp : A -> A -> comparison.

    Variable max_opt : option A -> option A -> option A.
    Hypothesis max_opt_None_None :
      max_opt None None = None.
    Hypothesis max_opt_Some_None : forall a,
        max_opt (Some a) None = Some a.
    Hypothesis max_opt_Some_Some : forall a b,
        max_opt (Some a) (Some b) = Some (if (comparison_eqb (cmp a b) Lt) then b else a).
    Hypothesis max_opt_comm : forall a b,
        max_opt a b = max_opt b a.

    Variable max_list : list A -> option A -> option A.
    Hypothesis max_list_nil : forall acc,
        max_list [] acc = acc.
    Hypothesis max_list_cons : forall x xs acc,
        max_list (x::xs) acc = max_list xs (max_opt acc (Some x)).
    Hypothesis max_list_app : forall l1 l2 acc,
        max_list (l1++l2) acc = max_list l2 (max_list l1 acc).

    Goal forall a b l comp,
        comp = true <-> cmp a b = Lt ->
        Some b = max_list l None ->
        Some (if comp then b else a) = max_list (l ++ [a]) None.
    Proof.
      snipe_no_check.
    Qed.
  End ML6.

  (* Same as 6, but max is generic over comparison *)
  Section ML7.
    Variable max : forall {A}, (A -> A -> comparison) -> A -> A -> A.
    Variable option_cmp :
      forall {A}, (A -> A -> comparison) ->
                  option A -> option A -> comparison.

    Variable A : Type.
    Hypothesis CA : CompDec A.

    Variable cmp : A -> A -> comparison.

    Hypothesis max_Lt : forall x y, cmp x y = Lt -> max cmp x y = y.
    Hypothesis max_Ge : forall x y, cmp x y <> Lt -> max cmp x y = x.
    Hypothesis max_comm : forall a b, max cmp a b = max cmp b a.

    Hypothesis max_None_None :
        max (option_cmp cmp) None None = None.
    Hypothesis max_Some_None : forall a,
        max (option_cmp cmp) (Some a) None = Some a.
    Hypothesis max_Some_Some : forall a b,
        max (option_cmp cmp) (Some a) (Some b) = Some (max cmp a b).

    Variable max_list : list A -> option A -> option A.
    Hypothesis max_list_nil : forall acc,
        max_list [] acc = acc.
    Hypothesis max_list_cons : forall x xs acc,
        max_list (x::xs) acc = max_list xs (max (option_cmp cmp) acc (Some x)).
    Hypothesis max_list_app : forall l1 l2 acc,
        max_list (l1++l2) acc = max_list l2 (max_list l1 acc).

    Goal forall a b l comp,
        comp = true <-> cmp a b = Lt ->
        Some b = max_list l None ->
        Some (if comp then b else a) = max_list (l ++ [a]) None.
    Proof.
      snipe.
    Qed.
  End ML7.

End Max_list.


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

(* Looping forever? *)
(* Lemma nth_default_eq : *)
(*     forall (A : Type) (HA : CompDec A) n l (d:A), nth_default d l n = nth n l d. *)
(* Proof. intros A HA n ; induction n. *)
(*   - snipe. *)
(*   - intros l ; destruct l. *)
(*     * snipe. *)
(*     * scope. get_projs_st option. (* specialize (gen_option A d). *) *)
(*       (* verit does not succed because p and p0 are not Zified by trakt (see "Preprocessing" channel *) *)
(* Abort. *)

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


(* Loops forever? *)
(* (* Testing interaction of `pose_case` with other transformations - verit won't conclude the goal due to silent simplification  *) *)
(* Goal forall (x : nat) (f g : nat -> nat) , (f 2 = 2) -> (g 2 = 2) -> ((match x with O => f | S _ => g end) 2 = 2). *)
(* Proof. *)
(*   scope. *)
(*   verit. *)
(*   Abort. *)
