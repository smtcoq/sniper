Require Import expand.
Require Import unfold_reflexivity.
Require Import unfold_in.
Require Import reflexivity.
From elpi Require Import elpi.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
Import Constr.Unsafe.



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

Tactic Notation "make_eq" constr(x) constr(y) :=
  elpi make_eq ltac_term:(x) ltac_term:(y).

(* Require Import Psatz. *)

(* Eval compute in (fun n => Nat.add n 2). *)
(* Eval lazy beta delta iota zeta in 10000%nat. *)

(* Section Test. *)
(*   Variable n m : nat. *)
(*   Hypothesis H : n <= m. *)

(*   Lemma foob : n <= m+1. lia. Defined. *)
(*   Eval compute in foob. *)

(*   Eval compute in @exist _ (fun n' => n' <= m + 1) n foob. *)

(* End Test. *)

(* Definition a := 2. *)

(* Definition f : nat -> nat := fun _ => a. *)

(* Goal False. *)
(*   let f := eval hnf in f in *)
(*   replace bar f. *)
(*   Abort. *)

Definition P : nat -> Prop := fun x => x >= 3.

Definition tt := {x : nat | P x}.

Definition v : tt := exist P 3 (le_n 3).

Definition f : nat -> nat -> tt := fun _ _ => v.

Definition g : tt -> tt := fun r => r.

(* Fixpoint rep_sig (i : nat) : Set := *)
(*   match i with *)
(*     | 0 => nat *)
(*     | S i' => @sig (rep_sig i') (fun x => x = x) *)
(*   end. *)

(* Eval hnf in (match (rep_sig 2) with _ => 4 end). *)

(* Variable y : rep_sig 2. *)

(* Eval hnf in (fix x () : Set := rep_sig 2 in x). *)

(* Eval hnf in (fix rep_sig (i : (id nat)) : id Set := *)
(*      match i with *)
(*      | 0 => nat *)
(*      | S i' => {x : rep_sig i' | x = x} *)
(*      end). *)


(* Section foo. *)
(* Variable (A : Type) (x : A) (P : A -> Prop) (f : P x) (a : A) (e : x = a). *)
(* Print eq_ind. *)



(* Goal proj1_sig v - 1 >= 2. *)
(*   let f1 := fresh "step_one" in *)
(*   step_one f1 (match id e in (_ = a0) return (id (P a0)) with | eq_refl => f end). *)

(*   step_one foo v. *)
(*   step_one bar (rep_sig 150). *)

(*   Abort. *)

Ltac elim_refinement_types p :=
  (* Step 1 *)
  let f1 := fresh "step_one" in
  let p2 := eval hnf in p in (* Maybe we just want p2 to be the body of p, more precisely, we need to check whether p has a body - if it does then we proceed normally, otherwise we still have to figure out what to do *)
  step_one f1 p2.

  (* Step 2 *)
  (* let f1 := eval cbn in f1 in *)
  (* let pf_refl := fresh "step_two" in *)
  (* let tp := type of p in *)
  (* let tp := eval red in tp in *)
  (* let tac := ltac2:(f1' p' redPType pf_refl |- *)
  (*   let f1'' := Option.get (Ltac1.to_constr f1') in *)
  (*   let p'' := Option.get (Ltac1.to_constr p') in *)
  (*   let redPType' := Option.get (Ltac1.to_constr redPType) in *)
  (*   let eq := make_eq f1'' p'' redPType' in *)
  (*   ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *)
  (* ) in tac f1 p tp pf_refl. *)

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


(*   let f1 := eval cbn in step_one in *)
(*   let pf_refl := fresh "step_two" in *)
(*   let tp := type of g in *)
(*   let tp := eval unfold tt in tp in *)
(*   let tac := ltac2:(f1' p' redPType pf_refl |- *)
(*     let f1'' := Option.get (Ltac1.to_constr f1') in *)
(*     let p'' := Option.get (Ltac1.to_constr p') in *)
(*     let redPType' := Option.get (Ltac1.to_constr redPType) in *)
(*     let eq := make_eq f1'' p'' redPType' in *)
(*     ltac1:(eq' |- idtac eq') (Ltac1.of_constr eq) *)
(*     (* ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *) *)
(*   ) in tac f1 g tp pf_refl. *)


(*   let f1 := fresh "step_one" in *)
(*   let p2 := eval hnf in f in *)
(*   step_one f1 p2. *)

(*   elim_refinement_types f. *)

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

Axiom foo : forall l h , ok (if l <? h then Cons l h Nil else Nil).

Program Definition interval (l h: Z) : refData :=
  exist _ (if Z.ltb l h then Cons l h Nil else Nil) _.
Next Obligation.
  exact (foo l h).
Defined.



From Ltac2 Require Import Constr Printf Message.
Ltac2 rec message_of_kind (k : kind) : message :=
  let sep_msg x y := concat x (concat (of_string ", ") y) in
  let par_msg msg := concat (of_string "( ") (concat msg (of_string " )")) in
  match k with
  | Rel i => of_int i
  | Var i => concat (of_string "Var ") (of_ident i)
  | Meta _ => of_string "Meta"
  | Prod _ b => concat (of_string "Prod ") (message_of_kind (kind b))
  | Lambda _ b => concat (of_string "Lambda ") (message_of_kind (kind b))
  | LetIn _ v b =>
      let msg := sep_msg (message_of_kind (kind v)) (message_of_kind (kind b)) in
      concat (of_string "LetIn ") (par_msg msg)
  | App c cs =>
      let cs_msg_array := Array.map (fun cn => message_of_kind (kind cn)) cs in
      let cs_msg := Array.fold_left sep_msg (message_of_kind (kind c)) cs_msg_array in
      concat (of_string "App ") (par_msg cs_msg)
 (* NOTE: constant is opaque so you can't inspect it (you can't even print it apparently), but you probably can use ltac2 machinery to get a variable whose value corresponds to some coq constant, and then compare it with the constant you have *)
  | Constant _ _ => of_string "Constant"
  | Ind _ _ => of_string "Ind"
  | Constructor _ _ => of_string "Constructor"
  | Case _ _ _ _ _ => of_string "Case"
  | _ => of_constr (make k)
  end.

Ltac2 message_of_constr_opt o :=
  match o with
    | None => of_string "None"
    | Some c => concat (of_string "Some ") (of_constr c)
  end.

Ltac2 rec print_hyps_list xs :=
  match xs with
    | (i, opt, ty) :: tl =>
        let iM : message := of_string (Ident.to_string i) in
        let optM : message := message_of_constr_opt opt in
        let tyM : message := of_constr ty in
        print (concat iM (concat (of_string " := ") (concat optM (concat (of_string " : ") tyM))));
        print_hyps_list tl
    | _ => ()
  end.

Definition my_identity {A : Type} (x : A) := x.


Goal nat -> True.
  intro y.
  pose (z := 2).
  let x := Env.get [Option.get (Ident.of_string "my_identity")] in
  match x with
    | Some r => print (of_constr (Env.instantiate r))
    | _ => print (of_string "boo")
  end.
  let a := Control.hyps () in
  print_hyps_list a.

    let x := constr:(z) in
    print (message_of_kind (kind x)).


Program Definition InBoolRef (x : Z) (s : refData) : bool := InBool x s.

Theorem In_interval: forall x l h, (InBoolRef x (interval l h) = true) <-> l <= x < h.
  Proof.
  split.
  intro H.


  let f1 := fresh "step_one" in
  let p2 := eval hnf in interval in
  step_one f1 p2.

(*   let f1 := eval cbn in step_one in *)
(*   let tp := type of InBoolRef in idtac tp. *)
(*   let tp := type of InBoolRef in *)
(*   let tp := eval hnf in tp in idtac tp. *)

(*   (* Step 2 *) *)
(*   let f1 := eval cbn in f1 in *)
(*   let pf_refl := fresh "step_two" in *)
(*   let tp := type of p in *)
(*   let tp := eval red in tp in *)
(*   let tac := ltac2:(f1' p' redPType pf_refl |- *)
(*     let f1'' := Option.get (Ltac1.to_constr f1') in *)
(*     let p'' := Option.get (Ltac1.to_constr p') in *)
(*     let redPType' := Option.get (Ltac1.to_constr redPType) in *)
(*     let eq := make_eq f1'' p'' redPType' in *)
(*     ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *)
(*   ) in tac f1 p tp pf_refl. *)







(*   (* let f1 := fresh "step_one" in *) *)
(*   (* let p2 := eval hnf in interval in *) *)
(*   (* step_one f1 p2. *) *)

(*   (* let tp := type of interval in *) *)
(*   (* let tp := eval red in tp in *) *)
(*   (* let pf_refl := fresh "step_two" in *) *)
(*   (* let tac := ltac2:(f1' p' redPType pf_refl |- *) *)
(*   (*   let f1'' := Option.get (Ltac1.to_constr f1') in *) *)
(*   (*   let p'' := Option.get (Ltac1.to_constr p') in *) *)
(*   (*   let redPType' := Option.get (Ltac1.to_constr redPType) in *) *)
(*   (*   let eq := make_eq f1'' p'' redPType' in *) *)
(*   (*   ltac1:(eq' pf_refl' |- assert (pf_refl' : eq') by now simpl) (Ltac1.of_constr eq) pf_refl *) *)
(*   (* ) in tac step_one interval tp pf_refl. *) *)



(*   (* let tac := ltac2:(f1' tp' pf_refl' |- *) *)
(*   (*     let tp'2 := Option.get (Ltac1.to_constr tp') in *) *)
(*   (*     let (_, pred) := get_ret_sig tp'2 in *) *)
(*   (*     let pred_applied := make_pred (Option.get (Ltac1.to_constr f1')) pred in *) *)
(*   (* (* (*     (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *) *) *) *) *)
(*   (*     ltac1:(pred' f1'' pf_refl'' |- *) *)
(*   (*       idtac pred') *) *)
(*   (*       (* let pred' := eval cbn in pred' in *) *) *)
(*   (*       (* assert (pred') (*by (rewrite <- pf_refl''; apply proj2_sig)*)) *) (Ltac1.of_constr pred_applied) f1' pf_refl' *) *)
(*   (*   ) *) *)
(*   (* in tac step_one tp step_two. *) *)
(*   (* intros l h. *) *)
(*   (* rewrite (step_two l h). *) *)


(*   (* elim_refinement_types interval. *) *)

(*   (* intros x0 l h. *) *)
(*   (* split. *) *)
(*   (* intro H. *) *)
(*   (* elim_refinement_types fresh_2 interval. *) *)
(*   (* assert (pf_refl : forall l h , fresh_2 l h = proj1_sig (interval l h)) by reflexivity. *) *)

(*   (* elim_refinement_types fresh_1 InBoolRef. *) *)
(*   (* assert (pf_refl : fresh_1 = proj1_sig InBoolRef). *) *)
