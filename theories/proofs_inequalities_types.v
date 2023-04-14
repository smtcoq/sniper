Lemma bool_not_unit : bool = unit -> False.
Proof.
  intros H.
  pose (f :=
  match H in _ = b return bool -> b with
  | eq_refl => fun x => x 
  end). 
  pose (g := 
  match H in _ = b return b -> bool with
  | eq_refl => fun x => x
  end).
  assert (H1 : forall (x : bool), g (f x) = x).
  intro x. destruct x; destruct H ; unfold f; unfold g; reflexivity.
  pose proof H1 as H2. specialize (H1 false). specialize (H2 true).
  destruct (f _) in H1. destruct (f _) in H2. rewrite H2 in H1. 
  inversion H1. Qed.

Lemma nat_is_not_bool : nat = bool -> False.
Proof.
  intros H.
  pose (f :=
  match H in _ = b return nat -> b with
  | eq_refl => fun (x : nat) => x 
  end). 
  pose (g := 
  match H in _ = b return b -> nat with
  | eq_refl => fun x => x
  end).
  assert (H1 : forall (x : nat), g (f x) = x).
  intro x. destruct x; destruct H ; unfold f; unfold g; reflexivity.
  pose proof H1 as H2. pose proof H1 as H3. specialize (H1 0). specialize (H2 1).
  specialize (H3 2).
  destruct (f _) in H1; destruct (f _) in H2; destruct (f _) in H3; subst.
  - rewrite H2 in H1; inversion H1.
  - rewrite H2 in H1; inversion H1.
  - rewrite H3 in H1; inversion H1.
  - rewrite H3 in H2; inversion H2.
  - rewrite H3 in H2; inversion H2.
  - rewrite H3 in H1; inversion H1.
  - rewrite H1 in H2; inversion H2.
  - rewrite H1 in H2; inversion H2. Qed.

Lemma nat_is_not_unit : nat = unit -> False.
Proof.
  intros H.
  pose (f :=
  match H in _ = b return nat -> b with
  | eq_refl => fun (x : nat) => x 
  end). 
  pose (g := 
  match H in _ = b return b -> nat with
  | eq_refl => fun x => x
  end).
  assert (H1 : forall (x : nat), g (f x) = x).
  intro x. destruct x; destruct H ; unfold f; unfold g; reflexivity.
  pose proof (H2 := H1). specialize (H1 0). specialize (H2 1).
  destruct (f _) in H1; destruct (f _) in H2.
  rewrite H1 in H2. inversion H2. Qed.
  
Lemma nat_is_not_natto_nat :

Lemma bool_is_not_boolto_bool :

Ltac2 different_cardinals_leads_to_different_types :=