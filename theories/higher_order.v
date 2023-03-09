Require Import utilities.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.

From elpi Require Import elpi.

Ltac mypose t := let Na := fresh "f" in pose t as Na; fold Na. (*TODO fold in all hyps except
the self refering one *)

Ltac mypose_and_reify_def t := let Na := fresh "f" in pose t as Na; fold Na ;
let H := fresh "H" in assert (H : Na = t) by reflexivity ; let hd := get_head t in 
unfold hd in H ; expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun H'' =>
try (eliminate_dependent_pattern_matching H''))).

Elpi Tactic anonymous_funs.

Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list term, i: goal, o: list sealed-goal.
  mypose_list [X|XS] G GL :- coq.ltac.call "mypose" [trm X] G [G'],
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.

  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_tys Ctx Trms,
    get_anonymous_funs_list [TyG|Trms] Lfun, mypose_list Lfun G GL.

}}.
Elpi Typecheck.

Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
pose (h := (fun x => x + 1) 42 = 43). 
elpi anonymous_funs. Abort.

Elpi Tactic prenex_higher_order.
Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/subterms.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list (pair term (list instance)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- std.rev Ctx Ctx',
    std.map L (instance_to_term Ctx') L', 
    coq.ltac.call "mypose_and_reify_def" [trm (app [X | L'])] G [G'],
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.


  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_hyps Ctx Trms, names Na,
    subterms_list_and_args [TyG|Trms] Na Subs,
    std.filter Subs (x\ fst x X, contains_prenex_ho_ty X, prenex_ho1_ty X) L, trm_and_args_type_funs L L', std.rev Ctx Ctx', 
term_to_instance_pr Ctx' L' L'', mypose_list L'' G GL.

}}.
Elpi Typecheck.
Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
elpi anonymous_funs.
elpi prenex_higher_order. Abort.

Goal ((forall (x : nat) (a : nat) (l : list nat), 
@hd nat x (@cons nat a l) = match (@cons nat a l) with
| nil => x
| y :: xs => y
end)). elpi anonymous_funs. Abort. (* Bug  fix : each branch of a match is a function *)

Tactic Notation "anonymous_funs" :=
  elpi anonymous_funs.

Tactic Notation "prenex_higher_order" :=
  elpi prenex_higher_order.


