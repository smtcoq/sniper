Require Import expand.
Require Import refinement_elimination_elpi.
Require Import reflexivity.
Require Import sig_expand_elpi.
Require Import unfold_reflexivity.
Require Import unfold_in.
From elpi Require Import elpi.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
Import Constr.Unsafe.
Require Import Sniper.
Require Import ZArith.

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

Tactic Notation "step_one" ident(i) constr(x) :=
  elpi step_one_tac ltac_string:(i) ltac_term:(x).

Tactic Notation "make_eq" constr(x) constr(y) :=
  elpi make_eq ltac_term:(x) ltac_term:(y).

Tactic Notation "sig_expand" ident(i) constr(x) :=
  elpi sig_expand_tac ltac_string:(i) ltac_term:(x).

Ltac elim_refinement_types p :=
  (* Step 1 *)
  let f1 := fresh "step_one" in
  let p2 := eval hnf in p in
  step_one f1 p2;
  (* we can't use red here since it will also replace step_one by its definition *)
  let f1 := eval cbn in f1 in

  (* Step 2 *)
  let pf_refl := fresh "step_two" in
  let tp_exp := fresh "tp_exp" in
  let tp := type of p in
  sig_expand tp_exp tp;
  let tp := eval red in tp_exp in (* eval red just replaces tp_exp by its definition *)
  let tac := ltac2:(f1' p' redPType pf_refl |-
    let f1'' := Option.get (Ltac1.to_constr f1') in
    let p'' := Option.get (Ltac1.to_constr p') in
    let redPType' := Option.get (Ltac1.to_constr redPType) in
    let eq := make_eq f1'' p'' redPType' in
    ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl
  ) in tac f1 p tp pf_refl;

  (* Step 3 *)
  let tac := ltac2:(f1' tp' pf_refl' |-
      let tp'' := Option.get (Ltac1.to_constr tp') in
      let (_, pred) := get_ret_sig tp'' in
      let pred_applied := make_pred (Option.get (Ltac1.to_constr f1')) pred in
      (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *)
      ltac1:(pred' f1'' pf_refl'' |-
        let pred' := eval cbn in pred' in
        assert (pred') by (intros; rewrite pf_refl''; apply proj2_sig)
      ) (Ltac1.of_constr pred_applied) f1' pf_refl'
    )
  in tac f1 tp pf_refl;

  (* Step 4 *)
  try rewrite <- pf_refl in *;

  (* clear pf_refl *)
  clear pf_refl tp_exp.

Section Examples.

  Set Default Proof Mode "Classic".

  Open Scope Z.

  Inductive data : Type := Nil | Cons (lo hi: Z) (tl: data).

  Fixpoint In (x: Z) (s: data) :=
    match s with
    | Nil => False
    | Cons l h s' => l <= x < h \/ In x s'
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

  Definition refData := { r : data | ok' r = true }.

  Axiom foo : forall l h , ok' (if l <? h then Cons l h Nil else Nil) = true.

  Program Definition interval (l h: Z) : refData :=
    exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.
  Next Obligation.
    exact (foo l h).
  Defined.

  Fixpoint InBool (x: Z) (s: data) : bool :=
    match s with
    | Nil => false
    | Cons l h s' => ((Z.leb l x) && (Z.ltb x h)) || InBool x s'
    end.

  Program Definition InBoolRef (x : Z) (s : refData) : bool := InBool x s.

  Axiom ok_ok' : forall x, ok x <-> ok' x = true.
  Trakt Add Relation 1 ok ok' ok_ok'.

  Goal forall l h , (proj1_sig (interval l h) = Nil) \/ (l <? h = true).
    intros l h.
    scope.
    - admit.
    - elim_refinement_types interval.
      scope.
      clear H0 H4 f. (* Need to fix, generated by Trakt *)
      verit.
  Admitted.

End Examples.
