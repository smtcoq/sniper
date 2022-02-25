From elpi Require Import elpi.
Require Import List.

Ltac assert2 H := assert H.

Ltac assert_list l H := match constr:(l) with
| nil => idtac 
| ?x :: ?xs => idtac "bar"; try (assert x by apply H) ; assert_list xs H
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
Elpi Accumulate File "find_instances.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate File "construct_cuts.elpi".
Elpi Accumulate lp:{{
  pred elpi_singl_to_coq_term  i: list term, o: list argument.
    elpi_singl_to_coq_term [X] [trm X].

  solve (goal Ctx _ TyG _ [trm H] as G) GL :- 
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2,
    find_instantiated_params_in_list [TyG|HL] Inst, subterms_type TyG Subs, 

instances_param_indu_strategy_aux H Inst Subs Res, coq.say Res, elpi_singl_to_coq_term Res H', coq.say H',
coq.ltac.call "assert" H' G GL.
%construct_cuts Res Trm,
    %refine Trm G GL. 

  


}}.
Elpi Typecheck.

Goal (forall (A : Type) (l : list A), A = A) -> (1 + 1 = 2) -> (forall (A B : Type)
(l: list A) (p: B*B), l= l -> p = p).
intros. elpi test (forall (A : Type) (l: list A), l = l). Abort.