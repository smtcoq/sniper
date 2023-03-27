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


(* If you have Sniper installed, change this line into:
   From Sniper Require Import Sniper.
*)
Require Import Sniper.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

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

(* Test for inversion principle *)

Lemma Add_in (A : Type) (a : A) l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
Proof.
scope_no_param_intuitionistic.
clear -H.
scope_param_intuitionistic @app_nil_r. Abort.

Definition true_hidden := true.
Definition definition_no_variables := if true_hidden then 1=1 else 2=2.

Goal definition_no_variables -> True.
scope.
Abort.


Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)). anonymous_funs. prenex_higher_order.
def_and_pattern_matching_mono prod_types get_definitions_theories_no_generalize.
assumption.
Qed.

Lemma if_var_in_context x y : (if Nat.eqb x y then x = x else y = y) -> True.
intros H.
scope.
Abort.

Goal forall (l : list Z) (x : Z) (a: bool),  hd_error l = Some x -> (l <> []).
Proof.
intros ; let p:= eval unfold prod_types in prod_types in interp_alg_types_context_goal p. 
def_and_pattern_matching_mono prod_of_symb get_definitions_theories_no_generalize.     
verit.
Qed.

Lemma nth_default_eq :
    forall (A : Type) (HA : CompDec A) n l (d:A), nth_default d l n = nth n l d.
Proof. intros A HA n ; induction n.  
  - snipe2.
  - intros l ; destruct l.
    * snipe2.
    * scope. get_projs_st option. specialize (gen_option A d). verit.
Qed.

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. elimination_polymorphism. split. assumption. split. assumption. assumption.
Qed. 

(* Test projs, two versions *)
Variable A : Type.
Variable a : A.

Goal forall (n : nat) (l : list A)(x : A) (xs: list A), l = nil \/ l = cons x xs.
Proof. 
get_projs_in_goal.
Abort.

Goal
  forall s1 s2 : string, s1 = s2.
Proof.
get_projs_in_goal.
clear. intros s1 s2.
let p:= eval unfold prod_types in prod_types in get_projs_in_variables p.
Abort.


Goal forall (n : nat) (l : list A)(x : A) (xs: list A), True -> (l = nil \/ l = cons x xs \/ n = 0).
intros. let p:= eval unfold prod_types in prod_types in get_projs_in_variables p. 
Abort.

Variable HA : CompDec A.

Definition search := 
fix search {A : Type} {H : CompDec A} (x : A) (l : list A) {struct l} : bool :=
  match l with
  | [] => false
  | x0 :: l0 => orb (eqb_of_compdec H x x0) (search x l0)
  end.

Section ho.

Variable A' B' : Type.
Variable HA' : CompDec A'.
Variable HB' : CompDec B'.

Definition app := fun (f : A'-> B') (x: A') => f x.

Lemma bar0 (f : A' -> B') (x : A') : 
app f x = f x -> app f x = f x. snipe2. Qed.

End ho.

Local Open Scope list_scope.
Import ListNotations. 

Lemma search_append_neq : 
forall l1 l2 l3 x, search x (l1 ++ l2) <> search x l3 -> l1 ++ l2 <> l3.
Proof. 
Time snipe2.
Undo. Time snipe. Qed.


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
    Time snipe2.
Undo. Time snipe.
  Qed.

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. Time snipe2.
Undo. Time snipe. 
 Qed.

 Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
  Time snipe2.
Undo. Time snipe.
  Qed.

End tests.

From elpi Require Import elpi.

Elpi Tactic elimination_polymorphism2.

Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/instantiate.elpi".
Elpi Accumulate File "elpi/find_instances.elpi".
Elpi Accumulate File "elpi/construct_cuts.elpi".

Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list term)), i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] Inst (goal Ctx _ _ _TyG _ as G) GS :- std.rev Ctx Ctx',
      pos_ctx_to_var_in_term Ctx' Inst Inst', coq.say "Inst'" Inst',
      snd P HPoly,
      instances_param_indu_strategy_aux HPoly Inst' [{{unit}}] LInst, !, coq.say LInst, 
      std.map LInst (add_pos_ctx Ctx') LInst', coq.say LInst', 
      % unit is a dumb default case to eliminate useless polymorphic premise
      construct_cuts LInst' G GL1, !,
      refine_by_instantiation GL1 P [G1|_GL], !, 
      coq.ltac.open (instances_param_indu_strategy_list XS Inst) G1 GS.
    instances_param_indu_strategy_list [] _ _G _.
    
  solve (goal Ctx _ TyG _ L as G) GL :- std.rev Ctx Ctx',
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2, argument_to_term L LTerm, 
    append_nodup HL2 LTerm HPoly, !, find_instantiated_params_in_list Ctx' [TyG |HL] Inst,
    instances_param_indu_strategy_list HPoly Inst G GL.
 

}}.
Elpi Typecheck.

Ltac clear_prenex_poly_hyps_in_context := repeat match goal with 
| H : forall (A : ?T), _ |- _ => first [ constr_eq T Set | constr_eq T Type] ; 
let T := type of H in let U := type of T in tryif (constr_eq U Prop) then try (clear H)
else fail
end.

Tactic Notation "elimination_polymorphism2" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism2 ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.


Tactic Notation "snipe2" uconstr_list_sep(l, ",") :=
let p2' := eval unfold prod_types in prod_types in
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching prod_of_symb ltac:(get_definitions_theories_no_generalize); 

intros ; idtac 1;
elpi elimination_polymorphism2 ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context) ;
get_projs_in_variables p2' ; verit.

  Theorem hd_error_nil A : hd_error (@nil A) = None.
  Proof.
  Time snipe2.
  Undo. Time snipe.
  Qed.

  Theorem in_eq : forall (a:A) (l:list A), Inb a (a :: l) = true.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Theorem in_cons : forall (a b:A) (l:list A), Inb b l = true -> Inb b (a :: l) = true.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Theorem not_in_cons (x b : A) (l : list A):
    ~ Inb x (a::l) = true <-> x<>a /\ ~ Inb x l = true.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Theorem in_nil : forall a:A, ~ Inb a nil.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Lemma in_inv : forall (a b:A) (l:list A), Inb b (a :: l) -> a = b \/ Inb b l.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  Time snipe2.
  Undo. Time snipe.
  Qed.

  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
  Time snipe2.
  Undo. Time snipe. 
  Qed.

  Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
   Time induction l ; snipe. Undo.
   Time induction l ; snipe2.
  Qed.

  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. Time snipe app_nil_r. Undo. Time snipe2 app_nil_r. Qed.

  Theorem app_assoc : forall l m n:list A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
    Time intros l ; induction l ; snipe. Undo. Time intros l ; induction l ; snipe2.
  Qed. 

  Theorem app_assoc_reverse : forall l m n:list A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
     Time snipe app_assoc. Undo. Time snipe2 app_assoc. Qed.

  Theorem app_comm_cons : forall (x y:list A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  Time snipe2.
  Undo. Time snipe.
  Qed.

  Theorem app_eq_nil' : forall l l':list A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof. 
  Time snipe2.
  Undo. Time snipe. Qed.

   Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
    Time snipe2.
  Undo. Time snipe. Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    Time induction x ; snipe. Undo. Time induction x ; snipe2.
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> or (Inb a l) (Inb a m).
  Proof.
    intros l m b. Time induction l; snipe. Undo. Time induction l ; snipe2.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    Time induction l ; snipe. Undo. Time induction l ; snipe2. Qed.



(* Test no_check version *)
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
Proof. Time snipe. Undo. Time snipe2. Qed.

End Pairs.


