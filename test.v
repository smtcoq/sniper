Require Import Sniper.

From Sniper Require Import expand.

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

Definition refData := { r : data | ok r }.
From elpi Require Import elpi.

Require Import sig_expand_elpi.

Tactic Notation "sig_expand" ident(i) constr(x) :=
  elpi sig_expand_tac ltac_string:(i) ltac_term:(x).

Local Close Scope Z_scope.

Fixpoint rep_sig (i : nat) : Set :=
  match i with
    | 0 => nat
    | S i' => @sig (rep_sig i') (fun x => x = x)
  end.

Fixpoint rep_sig2 (i : nat) : Set :=
  match i with
    | 0 => @sig nat (fun x => x = x)
    | S i' => nat -> (rep_sig2 i')
  end.

Eval compute in (rep_sig 2).

Eval compute in (rep_sig 10).

Elpi Trace "smart_expand_sig".

Goal True.
  sig_expand foo rep_sig.
  Abort.

Local Open Scope Z_scope.

Axiom foo : forall l h , ok' (if l <? h then Cons l h Nil else Nil).

Program Definition interval (l h: Z) : { r : data | ok' r } :=
  exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.
Next Obligation.
  exact (foo l h).
Defined.

Program Definition InBoolRef (x : Z) (s : refData) : bool := InBool x s.

Set Default Proof Mode "Classic".
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
Import Constr.Unsafe.

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

Tactic Notation "make_eq" constr(x) constr(y) :=
  elpi make_eq ltac_term:(x) ltac_term:(y).

Ltac elim_refinement_types p :=
  (* Step 1 *)
  idtac "1";
  let f1 := fresh "step_one" in
  let p2 := eval hnf in p in
  step_one f1 p2;
  idtac "2";

  (* Step 2 *)
  let pf_refl := fresh "step_two" in
  let f1 := eval cbn in f1 in
  let tp := type of p in
  let tp := eval hnf in tp in
  let tac := ltac2:(f1' p' redPType pf_refl |-
    let f1'' := Option.get (Ltac1.to_constr f1') in
    let p'' := Option.get (Ltac1.to_constr p') in
    let redPType' := Option.get (Ltac1.to_constr redPType) in
    let eq := make_eq f1'' p'' redPType' in
    ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl
  ) in tac f1 p tp pf_refl;

  (* Step 3 *)
  let tac := ltac2:(f1' tp' pf_refl' |-
      let tp'2 := Option.get (Ltac1.to_constr tp') in
      let (_, pred) := get_ret_sig tp'2 in
      (* let pred := Ltac1.of_constr pred' in *)
      let pred_applied := make_pred (Option.get (Ltac1.to_constr f1')) pred in
  (*     (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *) *)
      ltac1:(pred' f1'' pf_refl'' |-
        let pred' := eval cbn in pred' in
        assert (pred') by (intros; rewrite pf_refl''; apply proj2_sig)
      ) (Ltac1.of_constr pred_applied) f1' pf_refl'
    )
  in tac f1 tp pf_refl;


  (* Step 4 *)
  rewrite <- pf_refl in *;

  clear pf_refl.


Set Default Proof Mode "Classic".

Axiom ok_ok' : forall x, ok x <-> ok' x = true.
Trakt Add Relation 1 ok ok' ok_ok'.

Check interval.

Goal forall l h , (proj1_sig (interval l h) = Nil) \/ (l <? h = true).
  intros l h.
  scope.
  - admit.
  - admit.
  - elim_refinement_types interval.

    clear f H0 f0 H5 H3 H4 H p0.
    scope.
    verit.
  clearbody f.
  clear -H1.
  revert f H1.
  trakt Z bool.
  verit.
  scope.
  Focus 2.
  clearbody f.
  clearbody step_one.
  clear H.
  verit.

Open Scope bool_scope.

(* Definition interval2 (l h: Z) : refData := interval l h. *)


Fixpoint bar (n : nat) : nat :=
  match n with
    | O => O
    | S n' => bar n'
  end.

Fixpoint lt_nat (n m : nat) : bool :=
  match n with
    | O =>
        match m with
          | O => false
          | S _ => true
        end
    | S n' =>
        match m with
          | O => true
          | S m' => lt_nat n' m'
        end
    end.

(* Eval compute in lt_nat. *)

(* Eval compute in (fun (l h : Z) => (l + h)%Z). *)

Definition simple (z : Z) : bool :=
  match z with
    | Z.pos _ => true
    | _ => false
  end.



Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Local Open Scope positive_scope.

Fixpoint compare_cont (r:comparison) (x y:positive) {struct y} : comparison :=
  match x, y with
    | (xI p), (xI q) => compare_cont r p q
    | xI p, xO q => compare_cont Gt p q
    | xI p, 1 => Gt
    | xO p, xI q => compare_cont Lt p q
    | xO p, xO q => compare_cont r p q
    | xO p, 1 => Gt
    | 1, xI q => Lt
    | 1, xO q => Lt
    | 1, 1 => r
  end.

Definition k :=
  fun x y : Z =>
  match x with
  | Z.pos x' =>
                match y with
                | Z.pos y' => compare_cont Eq x' y'
                | _ => Gt
                end
  | _ => Eq
  end.

(* Eval compute in compare_cont. *)

(* Elpi Trace "refinefull". *)



Local Open Scope Z_scope.

Goal True.
  step_one foo (@id).
  step_one foo (compare_cont). (* Instantaneous *)
  step_one foo (k). (* Surprisingly slow (~1min) *)
  step_one foo (fun (l h : Z) => if l <? h then Cons l h Nil else Nil).


(* Local Open Scope Z_scope. *)


(* Theorem In_interval: forall x l h, (InBoolRef x (interval l h) = true) <-> l <= x < h. *)
(*   intros x l h. *)
(*   split. *)
(*   intro H. *)
(*   step_one foo (compare_cont). *)


(*   (* scope. *) *)
(*   (* Focus 3. *) *)

(*   (* pose (InBool' := fix InBool' x s := *) *)
(*   (*   match s with *) *)
(*   (*   | Nil => false *) *)
(*   (*   | Cons l h s' => ((Z.leb l x) && (Z.ltb x h)) || InBool' x s' *) *)
(*   (*   end). *) *)
(*   (* assert (H' : forall x s , InBool' x (proj1_sig s) = InBoolRef x s) by reflexivity. *) *)
(*   (* rewrite <- H' in H. *) *)

(*   (* elim_refinement_types interval. *) *)
(*   (* rewrite <- step_two in H. *) *)
(*   (* scope. *) *)
(*   (* clear H1 H3 H2 H7 H11 H' step_two H13 H0 H20 H23 H28 H31 f f1. *) *)
(*   (* clear H18 H8 H26. *) *)
(*   (* verit. *) *)

(*   (* Step 2 *) *)
(*   (* let f1 := eval cbn in f1 in *) *)
(*   (* let pf_refl := fresh "step_two" in *) *)
(*   (* let tp := type of p in *) *)
(*   (* let tp := eval red in tp in *) *)
(*   (* let tac := ltac2:(f1' p' redPType pf_refl |- *) *)
(*   (*   let f1'' := Option.get (Ltac1.to_constr f1') in *) *)
(*   (*   let p'' := Option.get (Ltac1.to_constr p') in *) *)
(*   (*   let redPType' := Option.get (Ltac1.to_constr redPType) in *) *)
(*   (*   let eq := make_eq f1'' p'' redPType' in *) *)
(*   (*   ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *) *)
(*   (* ) in tac f1 p tp pf_refl. *) *)
(*   (* elim_refinement_types InBoolRef. *) *)


(*   (* rewrite H8 in H. *) *)

(*   (* elim_refinement_types interval. *) *)
(*   (* assert (step_three: forall l h , ok' (step_one l h) = true). *) *)
(*   (* intros. *) *)
(*   (* rewrite step_two. *) *)
(*   (* apply proj2_sig. *) *)
(*   (* rewrite <- step_two in H. *) *)
(*   (* scope. *) *)

(*   (* Focus 2. *) *)
(*   (* verit. *) *)


(*   Abort. *)
