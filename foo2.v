Axiom bu : (nat -> nat) = bool.

Definition g : bool -> (nat -> nat) :=
  match bu in _ = b return b -> (nat -> nat) with
  | eq_refl => fun x => x
  end. 

Definition f : (nat -> nat) -> bool :=
  match bu in _ = b return (nat -> nat) -> b with
  | eq_refl => fun x => x
  end.

Definition fg (x : (nat -> nat)) : g (f x) = x :=
  match bu as bu return (match bu in _ = b return b -> (nat -> nat) with
                   | eq_refl => fun x => x
                   end) ((match bu in _ = b return (nat -> nat) -> b with
                       | eq_refl => fun x => x
                       end) x) = x with
  | eq_refl => eq_refl
  end.

Goal False.
pose proof (fg (fun _ => 0)) as H1.
pose proof (fg (fun _ => 1)) as H2.
pose proof (fg (fun _ => 2)) as H3.
destruct (f _);
destruct (f _); destruct (f _).
- rewrite H2 in H1.
assert (H:(fun _ : nat => 1) 0 = (fun _ : nat => 0) 0).
change ((fun _ : nat => 1) 0 = (fun _ : nat => 0) 0).
rewrite H1. reflexivity.
simpl in H. discriminate.
discrimi(nat -> nat)e.
- rewrite H2 in H1.
discrimi(nat -> nat)e.
- rewrite H3 in H1.
discrimi(nat -> nat)e.
- rewrite H2 in H3.
discrimi(nat -> nat)e.
- rewrite H2 in H3.
discrimi(nat -> nat)e.
- rewrite H3 in H1.
discrimi(nat -> nat)e.
- rewrite H2 in H1.
discrimi(nat -> nat)e.
- rewrite H2 in H1.
discrimi(nat -> nat)e.
Qed.