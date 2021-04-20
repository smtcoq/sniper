Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.

Require Import List.
Require Import definitions.



Theorem example1 : forall (A : Type) (x : A) (l: list A), hd_error l = Some x -> l <> nil.
Proof.
intros A x l H.
unfold not.
intro H0.
unfold hd_error in H. rewrite H0 in H. inversion H.
Qed.



Theorem example2 : forall (A : Type) (x : A) (l: list A), hd_error l = Some x -> l <> nil.
Proof.
assert (forall A (x : A), Some x <> None) by discriminate.
intros A x l H1.
assert (forall B, @hd_error B nil = None) by reflexivity.
assert (forall B (x : B) (l : list B), @hd_error B (x :: l)  = Some x) by reflexivity.
specialize (H0 A). specialize (H2 A).
verit.
  Qed.