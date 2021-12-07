Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
Require Import Sniper.Sniper.
Require Setoid.



Section projections.
  Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

  Definition fst (p:A * B) := match p with (x, y) => x end.
  Definition snd (p:A * B) := match p with (x, y) => y end.

  Register fst as core.prod.proj1.
  Register snd as core.prod.proj2.

End projections.

Section lemmas.

  Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

Lemma surjective_pairing :
  forall (p:A × B), p = (fst A B p, snd A B p).
Proof.
  scope2. (*  verit. *) (* TODO Chantal *)
Admitted.

Lemma injective_projections :
  forall (p1 p2:A * B),
    fst A B p1 = fst A B p2 -> snd A B p1 = snd A B p2 -> p1 = p2.
Proof.
  scope1. (* verit. *)
Abort.

Lemma pair_equal_spec :
  forall (a1 a2 : A) (b1 b2 : B),
    (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.
  snipe1. Undo. snipe2.
Qed.
