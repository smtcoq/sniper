From elpi Require Import elpi.
Require Import List.
Import ListNotations.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac intros_destructn n := 
lazymatch n with
| 0 => let x := fresh in intro x; destruct x
| S ?n' => let H := fresh in intro H; intros_destructn n'
end.

Ltac myrewrite H1 H2 := setoid_rewrite H1 in H2.

Ltac mypose x := pose x.

Goal (forall (A : Type) (B : Type) (l : list A) (l' : list B), l = l).
intros_destructn 3. Abort.

Ltac myassert x n := assert x by (intros_destructn n ; reflexivity).

Elpi Tactic eliminate_fix_hyp.
Elpi Accumulate File "elpi/eliminate_fix.elpi".
Elpi Accumulate File "elpi/subterms.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  solve ((goal _ _ _ _ [trm H1, trm H2]) as G) GL :- 

    subst_anon_fix H1 H2 H3, coq.ltac.call "mypose" [trm H3] G GL.
}}.

Elpi Typecheck. (*     %coq.typecheck H TyH ok, 
    %subterms_fix TyH L,*)


Print length.
Goal False. 
elpi eliminate_fix_hyp (fun A : Type =>
fix length (l : list A) {struct l} : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) (length). elpi eliminate_fix_hyp (fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) (Nat.add).



% ==> pour chaque F (fix dans la liste des fix)

% globals_in_goal Ctx L, std.filter L (x\ const_reduces_to x F) L'

Print length.

Goal forall (A : Type) (l : list A), False.
intros. elpi toto (fun A : Type =>
fix length (l : list A) {struct l} : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end).


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