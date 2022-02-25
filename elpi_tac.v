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

Lemma foo : (forall (A : Type) (l: list A), l = l).
Proof. intros; reflexivity. Qed.

Elpi Tactic test.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "find_instances.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate File "construct_cuts.elpi".
Elpi Accumulate lp:{{
  pred elpi_singl_to_coq_term  i: list term, o: list argument.
    elpi_singl_to_coq_term [X] [trm X].

  solve (goal Ctx _ TyG _ [trm H] as G) [GL1| GL] :- 
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2,
    find_instantiated_params_in_list [TyG|HL] Inst, subterms_type TyG Subs, 

instances_param_indu_strategy_aux H Inst Subs Res, elpi_singl_to_coq_term Res H',
construct_cuts Res Trm, 
  refine Trm G [GL1, GL2], coq.say {{foo}}, coq.ltac.open (refine (app [{{foo}}, _])) GL2 GL. 

  


}}.
Elpi Typecheck.



Goal (forall (A : Type) (l : list A), A = A) -> (1 + 1 = 2) -> (forall (A B : Type)
(l: list A) (p: B*B), l= l -> p = p).
intros. elpi test (forall (A : Type) (l: list A), l = l). Abort.

Elpi Tactic elimination_polymorphism.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "find_instances.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate File "construct_cuts.elpi".
Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list term)),
  i: list term, i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] L Subs G GL :- fst P Nah, snd P HPoly,
      instances_param_indu_strategy_aux HPoly L Subs LInst, !,
      construct_cuts LInst ProofTerm, refine ProofTerm G GL1, !, coq.say Nah,
      refine_by_instanciation GL1 Nah [G1 | GL], coq.say "proved".
      %coq.ltac.open (instances_param_indu_strategy_list XS L Subs) G1 GL. 
    instances_param_indu_strategy_list [] L _ G _.
    
  solve (goal Ctx _ TyG _ L as G) GL :- 
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2,
    find_instantiated_params_in_list [TyG |HL] Inst, subterms_type TyG Subs, argument_to_term L LTerm, 
    coq.say LTerm,
    append_nodup HL2 LTerm HPoly, !, instances_param_indu_strategy_list HPoly Inst Subs G GL.
  


}}.
Elpi Typecheck.

Goal forall l : list nat, l = l.
Proof.  elpi elimination_polymorphism (app_length).


Goal (forall (A : Type) (l : list A), A = A) -> (1 + 1 = 2) -> (forall (A : Type)
(l: list A), l= l).
intros. elpi elimination_polymorphism. 






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