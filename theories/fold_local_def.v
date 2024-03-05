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

Tactic Notation "fold_local_def" constr(t) :=
let tac :=
ltac2:(t |- let t := Ltac1.to_constr t in let t := Option.get t in fold_local_def t) 
in tac t.

Ltac fold_local_def_in_hyp_goal H t :=
 try (fold t in H); fold t.

Set Default Proof Mode "Classic".
Section tests.

Goal (let x := True in True -> True -> False -> True).
intros.
fold_local_def x. (* Undo. fold_local_def_in_hyp H x. *)
Abort.

End tests.