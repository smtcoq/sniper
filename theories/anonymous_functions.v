Require Import utilities.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.
Require Import instantiate.

From elpi Require Import elpi.

Ltac mypose t := 
tryif (is_local_def t) then idtac else
let Na := fresh "f" in pose t as Na; try fold Na. (* ; 
fold Na ;
let tupl := hyps in fold_tuple Na tupl ;
let H := fresh "H" in assert (H : Na = t) by reflexivity *)


Elpi Tactic anonymous_funs.

From Sniper.elpi Extra Dependency "higher_order.elpi" as HigherOrder.
Elpi Accumulate File HigherOrder.
From Sniper.elpi Extra Dependency "utilities.elpi" as Utils.
Elpi Accumulate File Utils.

Elpi Accumulate lp:{{
  
  pred anonyms_funs_hyps i: int, i: goal, o: list sealed-goal.
    anonyms_funs_hyps 0 _ _.
    anonyms_funs_hyps N (goal Ctx _ _ _ _ as G) GL :- ctx_to_tys Ctx Trms,
      get_anonymous_funs_list Trms [F|_L], coq.ltac.call "mypose" [trm F] G [G'],
      N1 is N - 1, coq.ltac.open (anonyms_funs_hyps N1) G' GL.

  pred anonyms_funs_goal i: int, i: goal, o: list sealed-goal.
    anonyms_funs_goal 0 (goal Ctx _ _ _ _ as G) GL :- ctx_to_tys Ctx Trms,
      get_anonymous_funs_list Trms LfunsCtx, std.length LfunsCtx N, anonyms_funs_hyps N G GL. 
    anonyms_funs_goal N (goal _ _ TyG _ _ as G) GL :- get_anonymous_funs_list [TyG] [F|_],
      coq.ltac.call "mypose" [trm F] G [G'],
      N1 is N - 1, coq.ltac.open (anonyms_funs_goal N1) G' GL.

  solve (goal _ _ TyG _ _ as G) GL :-
    get_anonymous_funs_list [TyG] LfunsGoal, std.length LfunsGoal N, 
    anonyms_funs_goal N G GL.

}}.
Elpi Typecheck.

Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
assert (H : (fun x => x + 1) 42 = 43) by reflexivity.
elpi anonymous_funs. Abort.

Goal (forall (A: Type) (n : nat) (l : list A) (x : A), 
(fun (n : nat) (l : list A) (default : A) => nth n l default) n l x = x ->
(n >= (fun (l : list A) => length l) l)).
Proof. intros. elpi anonymous_funs. Abort.

Lemma bar2 A B C (l : list A) (f : A -> B) (g: B -> C) : map (fun x => g (f x)) l = (fun l' => map g (map f l')) l.
Proof. elpi anonymous_funs. Abort. 

Tactic Notation "anonymous_funs" :=
  elpi anonymous_funs.

