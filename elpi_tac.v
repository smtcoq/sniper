From elpi Require Import elpi.
Require Import List.

Ltac assert2 H := assert H.

Ltac assert_list l H := match constr:(l) with
| nil => idtac 
| ?x :: ?xs => idtac "bar"; assert x by apply H ; assert_list xs H
end ; try (clear H).

Goal False.
Print app_length.
assert (forall (A : Type) (l l' : list A),
       length (l ++ l') = length l + length l') by apply app_length.
assert_list (cons (forall (l l' : list nat),
       length (l ++ l') = length l + length l') (cons
(forall (l l' : list unit),
       length (l ++ l') = length l + length l') nil)) H.
Abort.

Ltac apply2 H := apply H.

Ltac clear2 H := clear H.

Elpi Tactic test.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate lp:{{

pred type_global i: term, o: term.
  type_global (global (indt I)) Ty :- coq.env.indt I _ _ _ Ty _ _.

pred codomain i:term, o:term.
  codomain (prod Na Ty F) R :- !, pi x\ decl x Na Ty => codomain (F x) R. 
  codomain T T.

pred is_not_prop i: term, o: diagnostic.
  is_not_prop T ok :- coq.unify-leq T {{Prop}} (error S).
  is_not_prop T (error "the term is Prop").

pred codomain_not_prop i: term, o: diagnostic.
codomain_not_prop T ok :- codomain T U, is_not_prop U ok.

pred find_instantiated_params i: term, o: (list (pair term (list term))).
    find_instantiated_params (fun N Ty F) L :- !, find_instantiated_params Ty R1,
        pi x\ decl x N Ty => find_instantiated_params (F x) R2, append_nodup  R1 R2 L.
    find_instantiated_params (prod N Ty F) L :- !, find_instantiated_params Ty R1,
        pi x\ decl x N Ty => find_instantiated_params (F x) R2, append_nodup  R1 R2 L.
    find_instantiated_params (let N Ty V F) R :- !, find_instantiated_params Ty R1,
        pi x\ def x N Ty V => find_instantiated_params (F x) R2, append_nodup R1 R2 R.
    find_instantiated_params (match T U L) R :- find_instantiated_params T R1, 
        std.map L find_instantiated_params R2,
        std.flatten R2 R3,
        append_nodup  R1 R3 R.
    find_instantiated_params (fix Na _ Ty F) R :- !, find_instantiated_params Ty R1,
        pi x\ decl x Na Ty => find_instantiated_params (F x) R2,
        append_nodup R1 R2 R.
    find_instantiated_params (app [(global G)|X]) [(pr (global G) R)] :- 
    type_global (global G) Ty, codomain_not_prop Ty ok, %TODO one single call to coq.env.indt
    get_number_of_parameters (global G) NB,
        std.take NB X R.
    find_instantiated_params (app L) R :- std.map L find_instantiated_params R1, std.flatten R1 R.
    find_instantiated_params _ [].

pred find_instantiated_params_in_list i: (list term), o: (list (pair term (list term))).
    find_instantiated_params_in_list [X | XS] L :- find_instantiated_params X R1, 
    find_instantiated_params_in_list XS R2, append_nodup R1 R2 L.
    find_instantiated_params_in_list [] [].


  solve (goal Ctx _ TyG _ L as G) GL :- 
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2,
    find_instantiated_params_in_list [TyG|HL] Inst, coq.say Inst.
  


}}.
Elpi Typecheck.

Goal (forall (A : Type) (l : list A), A = A) -> (1 + 1 = 2) -> (forall (A : Type)
(l: list A), l= l).
intros. elpi test.

Elpi Tactic elimination_polymorphism.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate lp:{{

 pred elpi_list_to_coq_list i: list term, o: term.
    elpi_list_to_coq_list [X | XS] (app [{{@cons}}, {{Prop}}, X, R]) :- elpi_list_to_coq_list XS R.
    elpi_list_to_coq_list [] {{@nil Prop}}.

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list term)), i: goal, 
    o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] L G GL :- fst P Nah, snd P HPoly,
      instances_param_indu_strategy_aux HPoly L LInst, coq.say LInst,
 elpi_list_to_coq_list
      LInst LCoq, coq.say LCoq, coq.ltac.call "assert_list" [trm LCoq, trm NaH] G [GL1, GL2], 
      coq.ltac.open (instances_param_indu_strategy_list XS L) GL2 GL. 
    instances_param_indu_strategy_list [] L G _.
    


  solve (goal Ctx _ TyG _ L as G) GL :- 
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2,
    find_instantiated_params_in_list [TyG |HL] Inst, argument_to_term L LTerm,
    append_nodup HL2 LTerm Hpoly, 
    instances_param_indu_strategy_list Hpoly Inst G GL.
  


}}.
Elpi Typecheck.

Goal (forall (A : Type) (l : list A), A = A) -> (1 + 1 = 2) -> (forall (A : Type)
(l: list A), l= l).
intros. elpi elimination_polymorphism. (* Pour l'instant, pb entre l'hyp et son type mais ça va être réglé *)





Elpi Tactic toto.
Elpi Accumulate lp:{{

  pred tutu i:list argument, i:goal, o:list sealed-goal.

  tutu [H|L] G [GL1|GL] :- !,
    coq.ltac.call "assert2" [H] G [GL1,GL2],
    coq.ltac.open (tutu L) GL2 GL.

  tutu [] G _.


  solve (goal _ _ _ _ L as G) GL :-
    tutu L G GL, !.

  solve _ _ :- coq.ltac.fail _ "erreur".

}}.
Elpi Typecheck.


Goal True.
elpi toto (true = true) (False). Show 1. Show 2. Show 3.
Abort.

(* TODO : utiliser les instances sur une liste d'hypothèses passées en paramètre 
+ les hypothèses polymorphes du but *)

Elpi Tactic tata.
Elpi Accumulate lp:{{
  pred titi i: list argument.
  titi [X | XS] :- coq.say X, titi XS.
  titi [].
  tutu L Ty G GL :- titi [trm Ty| L].
  solve (goal _ _ Ty _ L as G) GL :-
    tutu L Ty G GL, !.

  solve _ _ :- coq.ltac.fail _ "erreur".

}}.
Elpi Typecheck.

Goal False -> False.
elpi tata (true = true) (forall (A: Type), A=A). 