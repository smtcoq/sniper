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
Import ListNotations.


Local Open Scope Z_scope.


(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> nil).
Proof. snipe. Qed.

Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.


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

(* An example with higher order and anonymous functions 
Note that as map should be instantiated by f and g, 
it does not work by using an induction principle which generalizes 
on f and g, so f and g have to be introduced before l 
It also work only with snipe2 because the arrow type instances will 
make SMTCoq complain *) 
Lemma map_compound : forall (A B C : Type) (HA : CompDec A)
(HB : CompDec B) (HC : CompDec C) (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; snipe2. Qed.

(* Section higher_order.

Variable A : Type.
Variable HA : CompDec A.
Variable B : Type.
Variable HB : CompDec B.*)
From elpi Require Import elpi.

Elpi Tactic elimination_polymorphism'.
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/instantiate.elpi".
Elpi Accumulate File "elpi/find_instances.elpi".
Elpi Accumulate File "elpi/construct_cuts.elpi".

Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list instance)), i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] Inst (goal Ctx _ _ _ _ as G) GS :-
      std.rev Ctx Ctx',
      subst_in_instances Ctx' Inst Inst',
      snd P HPoly,
      instances_param_indu_strategy_aux HPoly Inst' [{{unit}}] LInst, !, coq.say "LINST" LInst,
      % unit is a dumb default case to eliminate useless polymorphic premise
      construct_cuts LInst ProofTerm,
      refine ProofTerm G GL1, !,
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

Tactic Notation "elimination_polymorphism" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.

Tactic Notation "scope2_aux" constr(p1) constr(p2) uconstr_list_sep(l, ",") := 
let p2' := eval unfold p2 in p2 in
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching p1 ltac:(get_definitions_theories_no_generalize)) ; 
elpi elimination_polymorphism' ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context ;
get_projs_in_variables p2'.

Lemma zip_map A B (f : A -> B) (g : A -> B) (l : list A) :
map (fun (x : A) => (f x, g x)) l = zip (map f l) (map g l).
Proof. (* The pb is that f and g are also context variables so should be substituted in hypothesis *)
induction l ; scope2_aux prod_of_symb prod_types. Qed.

End higher_order.

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
