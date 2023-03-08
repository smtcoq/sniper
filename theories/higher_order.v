Require Import utilities.
From elpi Require Import elpi.

Ltac mypose t := let Na := fresh "f" in pose t as Na; fold Na. (*TODO fold in all hyps except
the self refering one *)

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

  shorten coq.ltac.{ open, set-goal-arguments }.


  pred select_args_type_funs i: list term, o: list term.
    select_args_type_funs [X | XS] [X |RS] :- (coq.typecheck X {{ Type }} ok ; coq.typecheck X {{ lp:_A -> lp:_B}} ok), select_args_type_funs XS RS. 
    select_args_type_funs _ []. 

  pred trm_and_args_type_funs i: list (pair term (list term)), o: list (pair term (list term)).
    trm_and_args_type_funs [pr X Y | XS] [pr X L| RS] :- select_args_type_funs Y L, trm_and_args_type_funs XS RS.
    trm_and_args_type_funs [] [].

  pred term_to_instance i: goal-ctx, i: int, i: term, o: instance.
    term_to_instance [decl X _ _|_] I X (var_context I).
    term_to_instance [def X _ _ _|_] I X (var_context I).
    term_to_instance [_|XS] I T R :- I' is I + 1, term_to_instance XS I' T R.
    term_to_instance [] I T (concrete_type T). 

  pred term_to_instance_pr i: goal-ctx, i: (list (pair term (list term))), o: (list (pair term (list instance))).
    term_to_instance_pr Ctx [pr X Y |L] [pr X Y' | R] :- term_to_instance_pr Ctx L R, std.map Y (term_to_instance Ctx 0) Y'.
    term_to_instance_pr _ [] [].

  pred mypose_list i: list (pair term (list instance)), i: goal, o: list sealed-goal.
  mypose_list [pr X L |XS] (goal Ctx _ _ _ _ as G) GL :- std.rev Ctx Ctx',
    std.map L (instance_to_term Ctx') L', 
    coq.ltac.call "mypose" [trm (app [X | L'])] G [G'],
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
pose (h := fun (x: A) => g (f x)).
 fold h. elpi prenex_higher_order. (* TODO Pb : elpi change silently the name of the variables when we change the goal 
use coq.ltac.set-goal-arguments Args G G1 G1wArgs and see 
https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html#setting-arguments-for-a-tactic*)


(* TODO filtrer les arguments de type produit dans la liste des arguments 
du terme d'ordre sup *) 


