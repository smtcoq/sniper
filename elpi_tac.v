From elpi Require Import elpi.
Require Import List.

Ltac assert2 H := assert H.


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