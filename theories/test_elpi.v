From elpi Require Import elpi.
Require Import List.

Ltac assert2 H := assert H.


Elpi Tactic toto'.
Elpi Accumulate File "elpi/pattern_matching.elpi".
Elpi Accumulate lp:{{

  solve (goal _ _ Ty _ _ as G) GL :- toto Ty Ty', coq.say Ty'.

}}.
Elpi Typecheck.

Goal (forall (x y : Type), x=x).
elpi toto'. Abort.

Elpi Tactic toto3.
Elpi Accumulate File "elpi/pattern_matching.elpi".
Elpi Accumulate lp:{{
    

     solve (goal [decl H _ _] _ Ty _ _ as G) [G2] :- !, toto Ty Foo,
    toto2 Ty H Bar, coq.say Bar, coq.ltac.call "assert2" [trm Foo] G [G1, G2],
    coq.say G1,
    coq.ltac.open (refine Bar) G1 _.
  
    
    

}}.
Elpi Typecheck.

Inductive foo :=
bar1 | bar2.

Print foo_rect.


Elpi Tactic hop.
Elpi Accumulate File "elpi/pattern_matching.elpi".
Elpi Accumulate lp:{{
  solve (goal [decl H _ TyH] Trigger _ Proof _ as G) GL :- coq.say TyH,
    toto2 TyH H Bar, coq.say Bar,  Trigger = Bar,
    coq.ltac.collect-goals Proof GL _X.
}}.
Elpi Typecheck.

Goal (forall (x y : Type), x=x) -> (forall (x y : Type), x=x /\ True).
intro H. elpi hop (H).



Goal (forall (x y : Type), x=x).
assert (H: (forall (x y : Type), x=x)) by (intros; auto).
elpi toto3.  Abort.
