Require Import utilities.
From elpi Require Import elpi.

Ltac mypose t := pose t.

Elpi Tactic name.

Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  solve (goal _ _ _ _ [trm T1]) _ :- get_anonymous_funs_trm T1 L, coq.say L.

}}.
Elpi Typecheck.

Goal False.
pose (x := 1).
elpi name (forall (x : nat), (fun (y : nat) => y) = 1).


