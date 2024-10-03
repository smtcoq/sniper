From elpi Require Import elpi.


(* Elpi Tactic eval_tac. *)

(* Elpi Accumulate lp:{{ *)
(*   solve (goal _ _ _ _ [trm P] as _G) _GL :- *)
(*       !, *)
(*       coq.reduction.lazy.whd P Pr, *)
(*       coq.say "P: " P, *)
(*       coq.say "Pr: " Pr. *)
(* }}. *)
(* Elpi Typecheck. *)

Elpi Tactic step_one_tac.

Elpi Accumulate lp:{{
  shorten std.{map}.


  % Maybe this thing is working, but the evaluation did not expand the symbol inside the lambda
%  replace I O :-
%    (copy {{ 2%nat }} {{ 3%nat }}) => copy I O.
%    (copy ({{ exist _ lp:P _ }}) P) =>
%    (copy ({{ @sig lp:A _ }}) A) =>
%    (copy ({{ @proj1_sig _ _ lp:X }}) X) =>
%          copy I O.


  pred refinefull i:term.
  pred refinefull_rec i:term.

  refinefull_rec ({{ exist _ _ _ }}) :- !.
  refinefull_rec ({{ @sig _ _ }}) :- !.
  refinefull_rec ({{ @proj1_sig _ _ _ }}) :- !.

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
    refinefull T, !. %, coq.say "match 1".
  refinefull_rec (match _ Rty _) :-
    refinefull Rty, !. %, coq.say "match 2".
  refinefull_rec (match _ _ B) :-
    std.exists B refinefull, !. %, coq.say "match 3".

  refinefull_rec (uvar _ L) :- std.exists L refinefull, !.

  refinefull I :-
    coq.reduction.lazy.whd I Ir,
    %coq.say "refinefull exist 2",
    refinefull_rec Ir.





  pred smart_refineexp i:term o:term.
  pred refineexp i:term o:term.
  pred refineexp_rec i:term o:term.

  smart_refineexp I O :-
    refinefull I, !, refineexp I O.
  smart_refineexp I I.

  refineexp I O :-
    coq.reduction.lazy.whd I Ir,
    smart_refineexp Ir O.

  refineexp_rec (fun X T F) (fun X T' F') :- !,
    smart_refineexp T T',
    pi x\ decl x _ T => pi x'\ decl x' _ T' => smart_refineexp (F x) (F' x').

  refineexp_rec I I.



  pred smart_replace i:term o:term.
  pred red_replace i:term o:term.
  pred replace i:term o:term.

  smart_replace I O :-
    %coq.say "smart_replace 0",
    refinefull I, !,
    %coq.say "smart_replace 1",
    %coq.term->string I Is,
    %coq.say "I = " Is,
    red_replace I O.
    %coq.term->string O Os.
    %coq.say "O = " Os.


  smart_replace I I.% :-
    %coq.say "smart_replace 2",
    %coq.term->string I Is,
    %coq.say "I = " Is.

  red_replace I O :-
    coq.say "red_replace",
    coq.reduction.lazy.whd I Ir,
    %coq.term->string I Is,
    %coq.say "I = " Is,
    %coq.term->string Ir Irs,
    %coq.say "Ir = " Irs,
    replace Ir O.
    %coq.term->string I Is,
    %coq.term->string Ir Irs,
    %coq.term->string O Os,
    %coq.say "I = " Is,
    %coq.say "Irs = " Irs,
    %coq.say "O = " Os.


%  replace ({{ exist _ lp:P _ }}) T' :- !, coq.say "replace exist", smart_replace P T'.
%  replace ({{ @proj1_sig _ _ lp:X }}) T' :- !, smart_replace X T'.
%  replace ({{ @sig lp:A _ }}) T' :- ! , smart_replace A T'.
%  replace X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
%  replace (global _ as C) C :- !.
%  replace (pglobal _ _ as C) C :- !.
%  replace (sort _ as C) C :- !.
%  replace (fun N T F) (fun N T1 F1) :- !,
%    smart_replace T T1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
%  replace (let N T B F) (let N T1 B1 F1) :- !,
%    smart_replace T T1, smart_replace B B1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
%  replace (prod N T F) (prod N T1 F1) :- !,
%    smart_replace T T1, (pi x\ decl x _ T => pi x1\ decl x1 _ T1 => smart_replace x x1 => smart_replace (F x) (F1 x1)).
%  replace (app L) (app L1) :- !,
%    map L smart_replace L1.
%  replace (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
%    smart_replace Ty Ty1, pi x\ decl x _ Ty => pi x1\ decl x1 _ Ty1 => smart_replace x x1 => smart_replace (F x) (F1 x1).
%  replace (match T Rty B) (match T1 Rty1 B1) :- !,
%    smart_replace T T1, smart_replace Rty Rty1, map B smart_replace B1.
%  replace (primitive _ as C) C :- !.
%  replace (uvar M L as X) W :- var X, !, map L smart_replace L1, coq.mk-app-uvar M L1 W.
%  % when used in CHR rules
%  replace (uvar X L) (uvar X L1) :- map L smart_replace L1.

  pred replace i:term, o:term.
  replace ({{ exist _ lp:P _ }}) P' :- !, replace P P'.
  replace ({{ @sig lp:A _ }}) A' :- !, replace A A'.
  replace ({{ @proj1_sig _ _ lp:X }}) X' :- !, replace X X'.
  replace X Y :- name X, !, X = Y, !. % avoid loading "replace x x" at binders
  replace (global _ as C) C :- !.
  replace (pglobal _ _ as C) C :- !.
  replace (sort _ as C) C :- !.
  replace (fun N T F) (fun N T1 F1) :- !,
    replace T T1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1).
  replace (let N T B F) (let N T1 B1 F1) :- !,
    replace T T1, replace B B1, pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1).
  replace (prod N T F) (prod N T1 F1) :- !,
    replace T T1, (pi x\ decl x _ T => pi x1\ decl x1 _ T1 => replace x x1 => replace (F x) (F1 x1)).
  replace (app L) (app L1) :- !, map L replace L1.
  replace (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
    replace Ty Ty1, pi x\ decl x _ Ty => pi x1\ decl x1 _ Ty1 => replace x x1 => replace (F x) (F1 x1).
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
      coq.term->string P Ps,
      coq.term->string P' P's,
      coq.say "P: " Ps,
      coq.say "Pr': " P's,

      refine (let N _ P' Tgt_) G GL.

  solve (goal _ _ _ _ [_, trm _]) _ :- coq.ltac.fail 0 "The first argument should be an identifier".

  solve (goal _ _ _ _ [_, _]) _ :- coq.ltac.fail 0 "The second argument should be a term".

  solve (goal _ _ _ _ _) _ :- coq.ltac.fail 0 "There should be exactly two arguments".
}}.
Elpi Typecheck.
