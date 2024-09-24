Require Import expand.
Require Import unfold_reflexivity.
Require Import unfold_in.
Require Import reflexivity.
From elpi Require Import elpi.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
Import Constr.Unsafe.


Set Default Proof Mode "Classic".



(* Definition p (n : nat) : Prop := n >= 3. *)

(* Definition t := { x : nat | p x }. *)

(* Definition x : t := exist _ 3 (le_n 3). *)


(* Definition identity {A : Type} : A -> A := fun x => x. *)

(* Goal (proj1_sig x) >= 3. *)
(*   step_one foo (exist p 3 (le_n 3)). *)
(*   pose (y := exist p 3 (le_n 3)). *)
(*   step_one foo2 y. *)
(*   step_one bar (fun x : @sig nat p => exist p (proj1_sig x) (proj2_sig x)). *)
(*   step_one baz (let z : @sig nat p := exist p 3 (le_n 3) in z). *)

(*   step_one baz2 ((fun k : @sig nat p -> @sig nat p => k y) id). *)
(*   (* This one does not work *) *)


(*   step_one baz3 (fun k : @sig nat p -> @sig nat p => k y). *)
(*   Abort. *)

(* The trigger should be activated for any symbol that contains a refinement type in its type *)
(* param p: symbol whose type contain a refinement type *)
(* 1. Define new equivalent symbol free of refinement types *)
(* 2. Prove that the first projection of p is equal to the new symbol *)
(* 3. Prove that the new symbol satisfies the predicate of p *)
(* 4. Replace p by the new symbol everywhere *)

Ltac2 fail msg :=
  Control.zero (Tactic_failure (Some msg)).

Ltac2 rec make_eq' (f : constr) (g : constr) (gA : constr) (gP : constr) (t : constr) (i : int) (args : constr list) :=
  match kind t with
  | Prod b c =>
      make (Prod b (make_eq' f g gA gP c (Int.add i 1) (make (Rel i) :: args)))
  | _ =>
      let lhs := make (App f (Array.of_list args)) in
      let rhs := make (App g (Array.of_list args)) in
      let rhs' := make (App constr:(proj1_sig) (Array.of_list [gA; gP; rhs])) in
      make (App constr:(@eq) (Array.of_list [t; lhs; rhs']))
  end.

Ltac2 rec get_ret_sig (t : constr) : constr * constr :=
  match kind t with
    | Prod _ c => get_ret_sig c
    | _ =>
       lazy_match! t with
         | @sig ?d ?p => (d, p)
         | _ => fail (Message.concat (Message.of_string "Expected refinement type but got: ") (Message.of_constr t))
       end
  end.

Ltac2 make_eq (f : constr) (g : constr) (reducedTypeG : constr) :=
  let (gA, gP) := get_ret_sig reducedTypeG in
  make_eq' f g gA gP (Constr.type f) 1 [].

Ltac2 rec make_pred' (f : constr) (tF : constr) (pred : constr) (i : int) (args : constr list) :=
  match kind tF with
  | Prod b c =>
      make (Prod b (make_pred' f c pred (Int.add i 1) (make (Rel i) :: args)))
  | _ =>
      let fApplied := make (App f (Array.of_list args)) in
      make (App pred (Array.of_list [fApplied]))
  end.

Ltac2 make_pred (f : constr) (pred : constr) :=
  make_pred' f (Constr.type f) pred 1 [].


Require Import refinement_elimination_elpi.

Tactic Notation "step_one" ident(i) constr(x) :=
  elpi step_one_tac ltac_string:(i) ltac_term:(x).

Ltac elim_refinement_types p :=
  (* Step 1 *)
  let f1 := fresh "step_one" in
  let p2 := eval hnf in p in
  step_one f1 p2;

  (* Step 2 *)
  let f1 := eval cbn in f1 in
  let pf_refl := fresh "step_two" in
  let tp := type of p in
  let tp := eval red in tp in
  let tac := ltac2:(f1' p' redPType pf_refl |-
    let f1'' := Option.get (Ltac1.to_constr f1') in
    let p'' := Option.get (Ltac1.to_constr p') in
    let redPType' := Option.get (Ltac1.to_constr redPType) in
    let eq := make_eq f1'' p'' redPType' in
    ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl
  ) in tac f1 p tp pf_refl.

  (* (* Step 3 *) *)
  (* let tac := ltac2:(f1' tp' pf_refl' |- *)
  (*     let tp'2 := Option.get (Ltac1.to_constr tp') in *)
  (*     let (_, pred) := get_ret_sig tp'2 in *)
  (*     (* let pred := Ltac1.of_constr pred' in *) *)
  (*     let pred_applied := make_pred (Option.get (Ltac1.to_constr f1')) pred in *)
  (* (*     (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *) *) *)
  (*     ltac1:(pred' f1'' pf_refl'' |- *)
  (*       (* let pred' := eval cbn in pred' in *) *)
  (*       assert (pred') by (intros; rewrite pf_refl''; apply proj2_sig) *)
  (*     ) (Ltac1.of_constr pred_applied) f1' pf_refl' *)
  (*   ) *)
  (* in tac f1 tp pf_refl. *)


  (* (* (* Step 4 *) *) *)
  (* rewrite pf_refl in *; *)

  (* clear pf_refl. *)


Definition P : nat -> Prop := fun x => x >= 3.

Definition tt := {x : nat | P x}.

Definition v : tt := exist P 3 (le_n 3).

Goal proj1_sig v - 1 >= 2.
  let f1 := fresh "step_one" in
  let p2 := eval hnf in v in
  step_one f1 p2.
  elim_refinement_types v.

Require Import ZArith.

Open Scope Z.

Inductive data : Type := Nil | Cons (lo hi: Z) (tl: data).

Fixpoint In (x: Z) (s: data) :=
  match s with
  | Nil => False
  | Cons l h s' => l <= x < h \/ In x s'
  end.

Fixpoint InBool (x: Z) (s: data) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => ((Z.leb l x) && (Z.ltb x h)) || InBool x s'
  end.


Inductive ok: data -> Prop :=
  | ok_nil: ok Nil
  | ok_cons: forall l h s
      (BOUNDS: l < h)
      (BELOW: forall x, In x s -> h < x)
      (OK: ok s),
      ok (Cons l h s).

Fixpoint ok' (x : data) : bool :=
  match x with
    | Nil => true
    | Cons l1 h1 s =>
        match s with
        | Nil => l1 <? h1
        | Cons l2 _ _ => (l1 <? h1) && (h1 <? l2) && (ok' s)
        end
  end.

Check @sig.

Definition refData := @sig data (fun r => ok r).

(* Definition refData := { r : data | ok r }. *)

Axiom foo : forall l h , ok (if l <? h then Cons l h Nil else Nil).

Program Definition interval (l h: Z) : refData :=
  exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.
Next Obligation.
  exact (foo l h).
Defined.

Program Definition InBoolRef (x : Z) (s : refData) : bool := InBool x s.

Theorem In_interval: forall x l h, (InBoolRef x (interval l h) = true) <-> l <= x < h.
  Proof.
  split.
  intro H.


  let f1 := fresh "step_one" in
  let p2 := eval hnf in InBoolRef in
  step_one f1 p2.

  let f1 := eval cbn in step_one in
  let tp := type of InBoolRef in idtac tp.
  let tp := type of InBoolRef in
  let tp := eval hnf in tp in idtac tp.

  (* Step 2 *)
  let f1 := eval cbn in f1 in
  let pf_refl := fresh "step_two" in
  let tp := type of p in
  let tp := eval red in tp in
  let tac := ltac2:(f1' p' redPType pf_refl |-
    let f1'' := Option.get (Ltac1.to_constr f1') in
    let p'' := Option.get (Ltac1.to_constr p') in
    let redPType' := Option.get (Ltac1.to_constr redPType) in
    let eq := make_eq f1'' p'' redPType' in
    ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl
  ) in tac f1 p tp pf_refl.







  (* let f1 := fresh "step_one" in *)
  (* let p2 := eval hnf in interval in *)
  (* step_one f1 p2. *)

  (* let tp := type of interval in *)
  (* let tp := eval red in tp in *)
  (* let pf_refl := fresh "step_two" in *)
  (* let tac := ltac2:(f1' p' redPType pf_refl |- *)
  (*   let f1'' := Option.get (Ltac1.to_constr f1') in *)
  (*   let p'' := Option.get (Ltac1.to_constr p') in *)
  (*   let redPType' := Option.get (Ltac1.to_constr redPType) in *)
  (*   let eq := make_eq f1'' p'' redPType' in *)
  (*   ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *)
  (* ) in tac step_one interval tp pf_refl. *)



  (* let tac := ltac2:(f1' tp' pf_refl' |- *)
  (*     let tp'2 := Option.get (Ltac1.to_constr tp') in *)
  (*     let (_, pred) := get_ret_sig tp'2 in *)
  (*     let pred_applied := make_pred (Option.get (Ltac1.to_constr f1')) pred in *)
  (* (* (*     (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *) *) *) *)
  (*     ltac1:(pred' f1'' pf_refl'' |- *)
  (*       idtac pred') *)
  (*       (* let pred' := eval cbn in pred' in *) *)
  (*       (* assert (pred') (*by (rewrite <- pf_refl''; apply proj2_sig)*)) *) (Ltac1.of_constr pred_applied) f1' pf_refl' *)
  (*   ) *)
  (* in tac step_one tp step_two. *)
  (* intros l h. *)
  (* rewrite (step_two l h). *)


  (* elim_refinement_types interval. *)

  (* intros x0 l h. *)
  (* split. *)
  (* intro H. *)
  (* elim_refinement_types fresh_2 interval. *)
  (* assert (pf_refl : forall l h , fresh_2 l h = proj1_sig (interval l h)) by reflexivity. *)

  (* elim_refinement_types fresh_1 InBoolRef. *)
  (* assert (pf_refl : fresh_1 = proj1_sig InBoolRef). *)
