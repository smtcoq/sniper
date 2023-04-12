Axiom bu : nat = bool.

Definition g : bool -> nat :=
  match bu in _ = b return b -> nat with
  | eq_refl => fun x => x
  end. 

Definition f : nat -> bool :=
  match bu in _ = b return nat -> b with
  | eq_refl => fun x => x
  end.

Definition fg (x : nat) : g (f x) = x :=
  match bu as bu return (match bu in _ = b return b -> nat with
                   | eq_refl => fun x => x
                   end) ((match bu in _ = b return nat -> b with
                       | eq_refl => fun x => x
                       end) x) = x with
  | eq_refl => eq_refl
  end.

Goal False.
pose proof (fg 0) as H1.
pose proof (fg 1) as H2.
pose proof (fg 2) as H3.
destruct (f _);
destruct (f _); destruct (f _).
- rewrite H2 in H1.
discriminate.
- rewrite H2 in H1.
discriminate.
- rewrite H3 in H1.
discriminate.
- rewrite H2 in H3.
discriminate.
- rewrite H2 in H3.
discriminate.
- rewrite H3 in H1.
discriminate.
- rewrite H2 in H1.
discriminate.
- rewrite H2 in H1.
discriminate.
Qed.