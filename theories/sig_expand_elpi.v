From elpi Require Import elpi.

From Sniper.elpi Extra Dependency "sigfull.elpi" as Sigfull.

Elpi Tactic sig_expand_tac.

Elpi Accumulate File Sigfull.

Elpi Accumulate lp:{{

  pred smart_sig_expand i:term o:term.
  pred sig_expand i:term o:term.
  pred sig_expand_rec i:term o:term.

  smart_sig_expand I O :-
    sigfull I, !,
    coq.term->string I Is,
    coq.say "smart_sig_expand sigfull: Is = " Is,
    sig_expand I O,
    coq.term->string O Os,
    coq.say "smart_sig_expand sigfull: Os = " Os.
  smart_sig_expand I I :-
    coq.term->string I Is,
    coq.say "smart_sig_expand sigless: Is = " Is.

  sig_expand I O :-
    coq.reduction.lazy.whd I Ir,
    sig_expand_rec Ir O.

% There probably is a more direct algorithm that simultaneously checks whether there is a `sig` inside the term and
% expands. Chantal's idea: as we traverse the tree, remember which constructors we went through and rebuild then when
% we find a `sig`.
% Another approach would be to understand how to use memoization
  %sig_expand_rec X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
  sig_expand_rec (global _ as C) C :- coq.say "global", !.
  sig_expand_rec (pglobal _ _ as C) C :- coq.say "pglobal", !.
  sig_expand_rec (sort _ as C) C :- coq.say "sort", !.
  sig_expand_rec (fun N T F) (fun N T1 F1) :- coq.say "fun", !,
    smart_sig_expand T T1, pi x\ decl x _ T => smart_sig_expand (F x) (F1 x).
  sig_expand_rec (let N T B F) (let N T1 B1 F1) :- coq.say "let", !,
    smart_sig_expand T T1, smart_sig_expand B B1, pi x\ decl x _ T => smart_sig_expand (F x) (F1 x).
  sig_expand_rec (prod N T F) (prod N T1 F1) :- coq.say "prod", !,
    smart_sig_expand T T1, (pi x\ decl x _ T => smart_sig_expand (F x) (F1 x)).
  sig_expand_rec (app L as T) (app L1) :-
    coq.term->string T Ts,
    coq.say "app: " Ts, !,
    %(F X1 X2 :- smart_sig_expand B X1 X2) =>
    std.map L smart_sig_expand L1.
  sig_expand_rec (fix N Rno Ty F) (fix N Rno Ty1 F1) :- coq.say "fix", !,
    smart_sig_expand Ty Ty1, pi x\ decl x _ Ty => smart_sig_expand (F x) (F1 x).
  sig_expand_rec (match T Rty B) (match T1 Rty1 B1) :- coq.say "match", !,
    smart_sig_expand T T1, smart_sig_expand Rty Rty1,
    %(F X1 X2 :- smart_sig_expand BB X1 X2) =>
    std.map B smart_sig_expand B1.
  sig_expand_rec (primitive _ as C) C :- coq.say "primitive", !.
  sig_expand_rec (uvar M L as X) W :- coq.say "uvar", var X, !,
    %(F X1 X2 :- smart_sig_expand B X1 X2) =>
   std.map L smart_sig_expand L1, coq.mk-app-uvar M L1 W.
  % when used in CHR rules
  sig_expand_rec (uvar X L) (uvar X L1) :- coq.say "uvar2",
    %(F X1 X2 :- smart_sig_expand B X1 X2) =>
      std.map L smart_sig_expand L1.

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

Elpi Accumulate File Sigfull.

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
