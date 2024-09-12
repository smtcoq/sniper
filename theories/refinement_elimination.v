From Ltac2 Require Import Ltac2.
From elpi Require Import elpi.

Set Default Proof Mode "Classic".

Require Import refinement_elimination_elpi.

Definition p (n : nat) : Prop := n >= 3.

Definition t := { x : nat | p x }.

Definition x : t := exist _ 3 (le_n 3).

Tactic Notation "step_one" uconstr(x) :=
  elpi step_one_tac ltac_term:(x).

Goal (proj1_sig x) >= 3.
  elpi step_one_tac "foo" (exist p 3 (le_n 3)).
  elpi step_one_tac "blah" ((fun (_ : nat) => (exist p 3 (le_n 3))) 42).
  step_one (fun _ => (exist _ 3 (le_n 3)) 42).
  Abort.
  (* let foo := fresh in *)
  (* elpi step_one_tac ltac_string:(ident:foo) (x). *)


(* param p: symbol whose type contain a refinement type *)
(* 1. Define new equivalent symbol free of refinement types *)
(* 2. Prove that the first projection of p is equal to the new symbol *)
(* 3. Prove that the new symbol satisfies the predicate of p *)
(* 4. Replace p by the new symbol everywhere *)


Ltac2 fail msg :=
  Control.zero (Tactic_failure (Some msg)).



(*Ltac2 step_one (p : constr) :=
  lazy_match! p with
    | exist _ ?body _ => body
    | f x =>*)

(* Ltac2 step_one (p: constr) := constr:(proj1_sig $p). *)

Ltac2 get_pred (tp:constr) : constr :=
  lazy_match! tp with
    | @sig _ ?pa => pa
    | _ => fail (Message.concat (Message.of_string "Expected refinement type but got: ") (Message.of_constr tp))
  end.

(*Definition get_pred {A : Type} {P : A -> Prop} : @sig A P -> (A -> Prop) := fun _ => P.*)

Ltac elim_refinement_types foo p :=

  (* Step 1 *)
  (* let new_p_id := fresh "new_p" in *)
  let p2 := eval hnf in p in
  step_one p2;

  (* let tac := *)
  (*   ltac2:(new_p_id' p' |- *)
  (*            let new_p := Ltac1.of_constr (step_one (Option.get (Ltac1.to_constr p'))) in *)
  (*            ltac1:(new_p_id'' new_p' |- pose (new_p_id'' := new_p')) new_p_id' new_p) *)
  (* in *)
  (* tac new_p_id p; *)

  (* Step 2 *)
  let pf_refl := fresh "pf_refl" in
  assert (pf_refl : proj1_sig p = foo) by reflexivity;

  (* Step 3 *)
  let tp := type of p in
  let tp := eval hnf in tp in
  let tac :=
    ltac2:(new_p_id' tp' pf_refl' |-
      let pred := Ltac1.of_constr (get_pred (Option.get (Ltac1.to_constr tp'))) in
      (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong *)
      ltac1:(pred' new_p_id'' pf_refl'' |- let pred_applied := constr:(pred' new_p_id'') in let pred_applied := (eval hnf in pred_applied) in assert (pred_applied) by (rewrite <- pf_refl''; apply proj2_sig)) pred new_p_id' pf_refl'
    )
  in tac foo tp pf_refl;

  (* Step 4 *)
  rewrite pf_refl in *;

  clear pf_refl.

Goal (proj1_sig x) >= 3.
  (* assert (H:x = exist _ 3 (le_n 3)) by reflexivity. *)
  elim_refinement_types foo x.

  Goal forall (x : t) , (proj1_sig x) >= 3.
  intro x.
  elim_refinement_types x.
  Focus 2.
