From elpi Require Import elpi.

Elpi Tactic step_one_tac.

Elpi Accumulate lp:{{
  shorten std.{map}.

  pred replace i:term o:term.
  replace I O :-
    (copy ({{ exist _ lp:P _ }}) P' :- !, replace P P') =>
    (copy ({{ @sig lp:A _ }}) A' :- !, replace A A') =>
    (copy ({{ @proj1_sig _ _ lp:X }}) X' :- !, replace X X') =>
      copy I O.


%  pred replace i:term, o:term.
%  replace I O :-
%            (copy ({{ exist _ lp:P _ }}) P' :- !, replace P P') =>
%            (copy ({{ @sig lp:A _ }}) A' :- !, replace A A') =>
%            (copy ({{ @proj1_sig _ _ lp:X }}) X' :- !, replace X X') =>
%              copy I O.

%  replace T T' :-
%            coq.unify-leq T ({{ exist _ lp:P _ }}) ok, !, replace P T'.
%  replace T T' :-
%            coq.unify-leq T ({{ @sig lp:A _ }}) ok, !, replace A T'.
%  replace T T' :-
%            coq.unify-leq T ({{ @proj1_sig _ _ lp:X }}) ok, !, replace X T'.
%  replace X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
%  replace (global _ as C) C :- !.
%  replace (pglobal _ _ as C) C :- !.
%  replace (sort _ as C) C :- !.
%  replace (fun N T F) (fun N T1 F1) :- !,
%    replace T T1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1).
%  replace (let N T B F) (let N T1 B1 F1) :- !,
%    replace T T1, replace B B1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1).
%  replace (prod N T F) (prod N T1 F1) :- !,
%    replace T T1, (pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1)).
%  replace (app L) (app L1) :- !, map L replace L1.
%  replace (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
%    replace Ty Ty1, pi x\ decl x _ Ty => pi x1\ decl x1 _ Ty1 => replace x x1 => replace (F x) (F1 x1).
%  replace (match T Rty B) (match T1 Rty1 B1) :- !,
%    replace T T1, replace Rty Rty1, map B replace B1.
%  replace (primitive _ as C) C :- !.
%  replace (uvar M L as X) W :- var X, !, map L replace L1, coq.mk-app-uvar M L1 W.
%  % when used in CHR rules
%  replace (uvar X L) (uvar X L1) :- map L replace L1.


%  pred step_one'' i:term, o:term.
%  step_one'' I O :-
%      coq.say "step_one'' before: I = " I " | O = " O,
%      (copy ( {{ exist _ lp:P _ }} ) P :- !) => copy I O,
%      coq.say "step_one'' after: I = " I " | O = " O.
%
%  pred step_one' i:term o:term.
%  step_one' I O :-
%      coq.say "step_one' before: I = " I " | O = " O,
%      (step_one'' ( {{ @sig lp:A _  }} ) A :- !) => step_one'' I O,
%      coq.say "step_one' after: I = " I " | O = " O.
%
%  pred step_one i:term o:term.
%  step_one I O :-
%      coq.say "step_one before: I = " I " | O = " O,
%      (step_one' ( {{ proj1_sig lp:X }} ) X :- !) => step_one' I O,
%      coq.say "step_one after: I = " I " | O = " O.

  solve (goal _ _ _ _ [str S, trm P] as G) GL :-
      !,
      coq.string->name S N,
      replace P P',
      coq.say "input of replace: " P,
      coq.say "replace computed: " P',

      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".
}}.
Elpi Typecheck.
