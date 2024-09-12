From elpi Require Import elpi.

Elpi Tactic step_one_tac.

Elpi Accumulate lp:{{

  %copy ({{ exist _ lp:P _ }}) P.

  pred step_one i:term, o:term.
  step_one I O :- (copy ( {{ exist _ lp:P _ }} ) P :- !) => copy I O.

  solve (goal _ _ _ _ [str S, trm P] as G) GL :-
      !,
      coq.string->name S N,
      step_one P P',
      coq.term->string P PS,
      %coq.say "P:" PS,
      coq.term->string P' PS2,
      %coq.say "P':" PS2,

      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".
}}.
Elpi Typecheck.
