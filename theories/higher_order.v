Require Import utilities.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.
Require Import anonymous_functions.
Require Import instantiate.

From elpi Require Import elpi.

(* TODO : use orchestrator instead of coding a small snipe in Ltac2 *)

Ltac mypose_and_reify_def_unfold t := 
tryif (is_local_def t) then idtac else
let Na := fresh "f" in pose t as Na; fold Na ;
let tupl := hyps in fold_tuple Na tupl ;
let H := fresh "H" in assert (H : Na = t) by reflexivity ; let hd := get_head t in 
unfold hd in H.

Elpi Tactic prenex_higher_order.
Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/subterms.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list (pair term (list term)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- 
    std.rev Ctx Ctx',
    std.map L (elim_pos_ctx Ctx') L',
    coq.ltac.call "mypose_and_reify_def_unfold" [trm (app [X | L'])] G [G'], 
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.


  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_hyps Ctx Trms, names Na,
    subterms_list_and_args [TyG|Trms] Na Subs, coq.say Subs,
    std.filter Subs (x\ fst x X, contains_prenex_ho_ty X, prenex_ho1_ty X) L, trm_and_args_type_funs L L', 
    std.rev Ctx Ctx', 
    add_pos_ctx_pr Ctx' L' L'', mypose_list L'' G GL.

}}.
Elpi Typecheck.

Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
List.map g (List.map f l) = map (fun x => g (f x)) l.
intros.
elpi anonymous_funs.
elpi prenex_higher_order. Abort.

Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)). elpi anonymous_funs. Abort. 
(* Bug fix : each branch of a match is a function so the function looking 
for anonymous functions were returning the branches and we do not want that.
So we stopped the recursive search when meeting a match.
But this should be improved by creating a special predicate for matches.  *)

Tactic Notation "prenex_higher_order" :=
  elpi prenex_higher_order.

From Ltac2 Require Import Ltac2.

Ltac2 prenex_higher_order_with_equations (u : unit) :=
let h := Control.hyps () in 
let () := ltac1:(prenex_higher_order) in
let h' := Control.hyps () in 
let h0 := new_hypothesis h h' in 
let rec aux h :=
  match h with
  | [] => ()
  | x :: xs => match x with
            | (id, opt, cstr) => let hltac2 := Control.hyp id in
              let hltac1 := Ltac1.of_constr hltac2 in ltac1:(H |- let T := type of H in let U := type of T 
              in tryif (constr_eq U Prop) then try (expand_hyp_cont H ltac:(fun H' => 
              eliminate_fix_cont H' ltac:(fun H'' => try (eliminate_dependent_pattern_matching H''))); clear H)
else idtac) hltac1 ; aux xs
            end
end 
in aux h0.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
induction l; Control.enter anonymous_funs_with_equations ; Control.enter prenex_higher_order_with_equations. Abort.

Tactic Notation "prenex_higher_order_with_equations" :=
ltac2:(Control.enter prenex_higher_order_with_equations).
