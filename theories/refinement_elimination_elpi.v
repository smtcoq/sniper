From elpi Require Import elpi.

Elpi Tactic step_one_tac.

Elpi Accumulate lp:{{
  shorten std.{map}.

  pred isSig i:term.
  isSig ({{ @sig _ _ }}).

  pred refinefull i:term.
  pred refinefull_rec i:term.

  refinefull_rec ({{ exist _ _ _ }}) :- !.
  refinefull_rec ({{ @sig _ _ }}) :- !.
  refinefull_rec ({{ let (A, _) := lp:X in A }}) :-
    coq.typecheck X XT ok,
    coq.reduction.lazy.whd XT XTR,
    isSig XTR,
  !.

  refinefull_rec (fun _ T _) :-
    refinefull T, !.
  refinefull_rec (fun _ T F) :-
    pi x\ decl x _ T => refinefull (F x), !.

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

  refinefull_rec (match T _ _) :-
    refinefull T, !.
  refinefull_rec (match _ Rty _) :-
    refinefull Rty, !.
  refinefull_rec (match _ _ B) :-
    std.exists B refinefull, !.

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
    coq.reduction.lazy.whd I Ir,
    replace Ir O.

  pred replace i:term, o:term.
  replace ({{ exist _ lp:P _ }}) P' :- !, smart_replace P P'.
  replace ({{ @sig lp:A _ }}) A' :- !, smart_replace A A'.
  replace ({{ let (A, _) := lp:X in A }}) X' :-
    coq.typecheck X XT ok,
    coq.reduction.lazy.whd XT XTR,
    isSig XTR,
    !, smart_replace X X'.
  replace X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
  replace (global _ as C) C :- !.
  replace (pglobal _ _ as C) C :- !.
  replace (sort _ as C) C :- !.
  replace (fun N T F) (fun N T1 F1) :- !,
    smart_replace T T1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
  replace (let N T B F) (let N T1 B1 F1) :- !,
    smart_replace T T1, smart_replace B B1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
  replace (prod N T F) (prod N T1 F1) :- !,
    smart_replace T T1, (pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1)).
  replace (app L) (app L1) :- !, map L smart_replace L1.
  replace (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
    smart_replace Ty Ty1, pi x\ decl x _ Ty => pi x1\ decl x1 _ Ty1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
  replace (match T Rty B) (match T1 Rty1 B1) :- !,
    smart_replace T T1, smart_replace Rty Rty1, map B smart_replace B1.
  replace (primitive _ as C) C :- !.
  replace (uvar M L as X) W :- var X, !, map L smart_replace L1, coq.mk-app-uvar M L1 W.
  % when used in CHR rules
  replace (uvar X L) (uvar X L1) :- map L smart_replace L1.

  solve (goal _ _ _ _ [str S, trm P] as G) GL :-
      !,
      coq.string->name S N,
      smart_replace P P',
      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".

}}.
Elpi Typecheck.
