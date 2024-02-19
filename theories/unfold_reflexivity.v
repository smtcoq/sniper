
Ltac unfold_refl H :=
  let T := type of H in 
    match T with
      | ?x = ?x => try unfold x at 2 in H
      | _ => idtac
    end.

Goal False.
assert (H : length = length) by reflexivity.
unfold_refl H.
Abort.