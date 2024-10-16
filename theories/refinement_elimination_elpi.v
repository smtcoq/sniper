From elpi Require Import elpi.

Elpi Tactic step_one_tac.

Elpi Accumulate lp:{{
  shorten std.{map}.

  pred isSig i:term.
  isSig ({{ @sig _ _ }}).

  pred refinefull i:term.
  pred refinefull_rec i:term.

  refinefull_rec ({{ exist _ _ _ }}).
  refinefull_rec ({{ @sig _ _ }}).
  refinefull_rec ({{ @proj1_sig _ _ _ }}).

  refinefull_rec (fun _ T _) :- refinefull_rec T, !.
  refinefull_rec (fun _ T F) :-
    pi x\ decl x _ T =>
    refinefull_rec (F x), !.

  refinefull_rec (let _ T _ _) :-
    refinefull T, !.
  refinefull_rec (let _ _ B _) :-
    refinefull B, !.
  refinefull_rec (let _ T _ F) :-
    pi x\ decl x _ T => refinefull (F x), !.

  refinefull_rec (prod _ T _) :-
    refinefull T, !.
  refinefull_rec (prod _ T F) :-
    pi x\ decl x _ T => refinefull (F x), !.

  refinefull_rec (app L) :- !, std.exists L refinefull.

  refinefull_rec (fix _ _ Ty _) :-
    refinefull Ty, !.
  refinefull_rec (fix _ _ Ty F) :-
    pi x\ decl x _ Ty => refinefull (F x), !.

  refinefull_rec (match T _ _) :- refinefull T, !.
  refinefull_rec (match _ Rty _) :- refinefull Rty, !.
  refinefull_rec (match _ _ B) :- !,
    std.exists B refinefull.

  refinefull_rec (uvar _ L) :- std.exists L refinefull, !.

  refinefull I :-
    coq.reduction.lazy.whd I Ir,
    refinefull_rec Ir.

  pred smart_replace i:term o:term.
  pred red_replace i:term o:term.
  pred replace i:term o:term.

  smart_replace I O :-
    refinefull I, !,
    red_replace I O.

  smart_replace I I.

  red_replace I O :-
    coq.term->string I Is,
    coq.say "red_replace: " Is,
    coq.reduction.lazy.whd I Ir,
    coq.term->string Ir Irs,
    coq.say "red_replace: " Irs,
    replace Ir O.

  pred replace i:term, o:term.
  replace ({{ exist _ lp:P _ }}) P' :- !, replace P P'.
  replace ({{ @sig lp:A _ }}) A' :- !, replace A A'.
  replace ({{ @proj1_sig _ _ lp:X }}) X' :- !, replace X X'.
  replace (fun N T F) (fun N T1 F1) :- !,
      % We should add another variable and figure out which rule to add between the two introduced variables
    replace T T1, pi x\ decl x _ T => replace (F x) (F1 x).
  replace X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
  replace (global _ as C) C1 :- refinefull C, !, coq.reduction.lazy.whd C C2, replace C2 C1.
  replace (global _ as C) C.
  replace (pglobal _ _ as C) C1 :- refinefull C, !, coq.reduction.lazy.whd C C2, replace C2 C1.
  replace (pglobal _ _ as C) C :- !.
  replace (sort _ as C) C :- !.
  replace (let N T B F) (let N T1 B1 F1) :- !,
    replace T T1, replace B B1, pi x\ decl x _ T => replace (F x) (F1 x).
  replace (prod N T F) (prod N T1 F1) :- !,
    replace T T1, (pi x\ decl x _ T => replace (F x) (F1 x)).
  replace (app L) (app L1) :- !, map L replace L1.
  replace (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
    replace Ty Ty1, pi x\ decl x _ Ty => replace (F x) (F1 x).
  replace (match T Rty B) (match T1 Rty1 B1) :- !,
    replace T T1, replace Rty Rty1, map B replace B1.
  replace (primitive _ as C) C :- !.
  replace (uvar M L as X) W :- var X, !, map L replace L1, coq.mk-app-uvar M L1 W.
  % when used in CHR rules
  replace (uvar X L) (uvar X L1) :- map L replace L1.

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
