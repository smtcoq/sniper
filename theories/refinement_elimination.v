From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".


(* param p: symbol whose type contain a refinement type *)
(* 1. Define new equivalent symbol free of refinement types *)
(* 2. Prove that the first projection of p is equal to the new symbol *)
(* 3. Prove that the new symbol satisfies the predicate of p *)
(* 4. Replace p by the new symbol everywhere *)


Ltac2 fail msg :=
  Control.zero (Tactic_failure (Some msg)).

Ltac2 step_one (p: constr) := constr:(proj1_sig $p).

Ltac2 get_pred (tp:constr) : constr :=
  lazy_match! tp with
    | @sig _ ?pa => pa
    | _ => fail (Message.concat (Message.of_string "Expected refinement type but got: ") (Message.of_constr tp))
  end.

(*Definition get_pred {A : Type} {P : A -> Prop} : @sig A P -> (A -> Prop) := fun _ => P.*)

Ltac elim_refinement_types p :=

  (* Step 1 *)
  let new_p_id := fresh "new_p" in
  let tac :=
    ltac2:(new_p_id' p' |-
             let new_p := Ltac1.of_constr (step_one (Option.get (Ltac1.to_constr p'))) in
             ltac1:(new_p_id'' new_p' |- pose (new_p_id'' := new_p')) new_p_id' new_p)
  in
  tac new_p_id p;

  (* Step 2 *)
  let pf_refl := fresh "pf_refl" in
  assert (pf_refl : proj1_sig p = new_p_id) by reflexivity;

  (* Step 3 *)
  let tp := type of p in
  let tp := eval hnf in tp in
  let tac :=
    ltac2:(new_p_id' tp' |-
      let pred := Ltac1.of_constr (get_pred (Option.get (Ltac1.to_constr tp'))) in
      (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong *)
      ltac1:(pred' new_p_id'' |- let foo := constr:(pred' new_p_id'') in let foo := (eval hnf in foo) in assert (foo) by apply proj2_sig) pred new_p_id'
    )
  in tac new_p_id tp;

  (* Step 4 *)
  rewrite pf_refl in *;

  clear pf_refl.

Definition t := { x : nat | x >= 3 }.

Goal forall (x : t) , (proj1_sig x) >= 3.
  intro x.
  elim_refinement_types x.
  Focus 2.
