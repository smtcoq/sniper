From Ltac2 Require Import Ltac2.

Ltac2 fold_local_def (c : constr) :=
  let hs := Control.hyps () in
  try (fold $c) ;
  let rec aux hs :=
    match hs with
      | (id, _, _) :: hs' => 
          try (fold $c in $id) ; aux hs'
      | [] => ()
    end
  in aux hs.


Section tests.

Goal (let x := True in True -> True -> False -> True).
intros.
fold_local_def 'x.
Abort.

End tests.