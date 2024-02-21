Require List.

Ltac unfold_in H t :=
  unfold t in H.

Section Tests.
Variable (A B : Type).
Variable (f : A -> B).

Goal False.
pose (mapf := List.map f).
assert (H : mapf = List.map f) by reflexivity.
unfold_in H List.map.
Abort.

End Tests.