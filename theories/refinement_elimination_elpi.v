From elpi Require Import elpi.

From Sniper.elpi Extra Dependency "ref_elim_utils.elpi" as ref_elim_utils.

Elpi Tactic convert_sigless_tac.

Elpi Accumulate File ref_elim_utils.

Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [str S, trm P] as G) GL :-
      !,
      coq.string->name S N,
      replace P P',
      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".

}}.
Elpi Typecheck.

Elpi Tactic sig_expand_tac.

Elpi Accumulate File ref_elim_utils.

Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [str S, trm P] as G) GL :-
      !,
      coq.string->name S N,
      smart_sig_expand P P',
      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".

}}.
Elpi Typecheck.

Elpi Tactic sigfull_tac.

Elpi Accumulate File ref_elim_utils.

Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [trm P]) _ :-
    sigfull P.

  solve (goal _ _ _ _ [trm _]) _ :-
    coq.ltac.fail 0 "The argument is not sigfull".

  solve (goal _ _ _ _ [_]) _ :-
    coq.ltac.fail 0 "The argument should be a term".

  solve (goal _ _ _ _ _) _ :-
    coq.ltac.fail 0 "There should be exactly 1 argument".

}}.
Elpi Typecheck.
