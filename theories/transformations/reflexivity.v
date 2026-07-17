
Ltac assert_refl c :=
  let H := fresh in assert (H : c = c) by reflexivity.

Goal False.
assert_refl nat.
assert_refl Nat.add.
Abort.