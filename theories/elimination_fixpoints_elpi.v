From elpi Require Import elpi.
Require Import List.
Import ListNotations.
Print length.

Elpi Command toto.
Elpi Accumulate File "elpi/eliminate_fix.elpi".
Elpi Accumulate lp:{{
  main [trm T1, trm T2] :- mkEq T1 T2 R, coq.say R.
}}.
Elpi Typecheck.

Elpi toto (length) (length).



Lemma test : forall (A : Type) (l : list A), 
(fix length_anon (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length_anon l')
  end) l  =
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.
Proof.
intros; destruct l ; reflexivity. Qed.

Variable toto : nat -> nat.

Lemma test2 n m : (fix add (n0 m0 : nat) :=
  match n0 with
  | 0 => m0
  | S p => S (add p m0)
  end) n m = 
  match n with
  | 0 => m
  | S p => S (Nat.add p m)
  end
.
Proof. 
intros; destruct n; reflexivity. Qed.

Goal False.

assert (H4 : forall n m, toto (Nat.add n m) =
(toto ((fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m))). reflexivity. setoid_rewrite test2 in H4. Abort.




Elpi Tactic elimination_fixpoints.

Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate File "elpi/subterms.elpi".

Elpi Typecheck.