From elpi Require Import elpi.

From elpi Require Import elpi.

Elpi Tactic create_new_goal.
Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [trm H] as G) GL :-
    std.assert-ok! (coq.elaborate-ty-skeleton H _ H1) "cut formula illtyped",
    refine (app[(fun `new_hyp` H1 x\ G1_ x), G2_]) G GL,
    coq.say GL.

}}.
Elpi Typecheck.

(* [(nabla c0 \
   seal
    (goal [decl c0 `new_hyp` (global (indt «False»))] (X0 c0) 
      (global (indt «True»)) (X1 c0) [])), 
 seal (goal [] (X2) (global (indt «False»)) (X3) [])] *)

Goal True.
refine ((fun (new_hyp : False) => I) _).
elpi create_new_goal (False).
Show 2. Abort.

Elpi Tactic argpass.
Elpi Accumulate lp:{{

% this directive lets you use short names
shorten coq.ltac.{ open, thenl, all }.

type intro open-tactic. % goal -> list sealed-goal
intro G GL :- refine {{ fun H => _ }} G GL.

type set-arg-n-hyp int -> open-tactic.
set-arg-n-hyp N (goal Ctx _ _ _ _ as G) [SG1] :-
  std.nth N Ctx (decl X _ Ty), coq.say G,
  coq.ltac.set-goal-arguments [trm Ty] G (seal G) SG1.

type myassert open-tactic.
  myassert (goal _ _ _ _ [trm H] as G) GL :-
    std.assert-ok! (coq.elaborate-ty-skeleton H _ H1) "cut formula illtyped",
    refine (app[(fun `new_hyp` H1 x\ G1_ x), G2_]) G GL.

msolve SG GL :-
  all (thenl [ open intro,
               open (set-arg-n-hyp 0),
               open myassert ]) SG GL.

}}.
Elpi Typecheck.

Lemma test_argpass (Q: Prop) (P : Prop) : P -> P.
Proof.
elpi argpass.
Abort.

Definition foo := unit.
Definition bar := nat.

Elpi Tactic toto.
Elpi Accumulate lp:{{

pred tutu i:term, o:prop.
tutu X (copy {{ foo }} {{ bar}}).

solve (goal _ _ _ _ [trm H] as G) GL :- tutu H R, (R :- !) => copy H B,
  coq.say B.

}}.
Elpi Typecheck.

Goal False.
elpi toto (foo).
