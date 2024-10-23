(* DONE: Comment the code *)
(* TODO: Add unit tests in the tests file *)
(* TODO: Add examples of usage in the examples showroom *)
(* DONE: Find a better name for the symbol introduced (maybe based on the original name) *)
(* TODO: Step three does not work if `p` has refinement types in any argument and in the return type *)
(* TODO: The trigger should work with equality modulo delta, but it doesn't yet *)
(* TODO: Check again how far we are from proving automatically the `interval` example in CompCert *)
(* TODO: Currently we are relying on the fact that if the user has an application `f x` such that `f` takes *)
(*       a refinement type and `x` has a refinement in its type then the transformation will be fired on `f` before *)
(*       `x`. We shouldn't rely on this. Maybe we could split it into two transformations, one for generating the term *)
(*       and proving the equality; other for rewriting the equality. *)
(* TODO: Create a new version of this tactic that will operate in terms without a body. *)
(*   - The new symbol should be defined using `p` directly, instead of the body of `p` *)
(*   - After defining the new symbol, the rest of the tactic should be approximately the same *)
(* TODO: In the future we will want to support dependent records - for that we need to generalize the parts in *)
(*       which we deal specifically with `proj1_sig` *)

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
Require Import ZArith.

(* The trigger should be activated for any symbol that contains a refinement type in its type *)
(* param p: symbol whose type contain a refinement type *)
(* 1. Define new equivalent symbol free of refinement types *)
(* 2. Prove that the first projection of p is equal to the new symbol *)
(* 3. Prove that the new symbol satisfies the predicate of p *)
(* 4. Replace p by the new symbol everywhere *)

(* Assumes `t` is the type of a function. Computes the arity of the function. *)
Ltac2 rec arity (t : constr) : int :=
  match kind t with
    | Prod _ c => Int.add 1 (arity c)
    | _ => 0
  end.

(* Assumes that `t` is the type of a function that returns a refinement type. Returns the predicate of the return type. *)
Ltac2 rec get_ret_sig (t : constr) : constr option :=
  match kind t with
    | Prod _ c => get_ret_sig c
    | _ =>
       lazy_match! t with
         | @sig _ ?p => Some p
         | _ => None
       end
  end.

(* Auxiliary function for `make_eq`. Traverses the arrows of the type of `g`, adding `proj1_sig` whenever it encouters an argument *)
(* which is a refinement type. `i` is the De Bruijn index of the current argument. The arguments to be applied to `f` and `g` are *)
(* accumulated in `argsF` and `argsG`, respectively. *)
Ltac2 rec make_eq' (f : constr) (g : constr) (t : constr) (i : int) (argsF : constr list) (argsG : constr list) :=
  match kind t with
  | Prod b c =>
      (* If the current argument is a `sig`, we apply the function to `proj1_sig (Rel i)`, otherwise is just `Rel i` *)
      lazy_match! Constr.Binder.type b with
        | @sig ?d ?p =>
            let argF : constr := make (App constr:(@proj1_sig) (Array.of_list [d; p; make (Rel i)])) in
            make (Prod b (make_eq' f g c (Int.sub i 1) ((argF) :: argsF) (make (Rel i) :: argsG)))
        | _ => make (Prod b (make_eq' f g c (Int.sub i 1) (make (Rel i) :: argsF) (make (Rel i) :: argsG)))
      end
  | _ =>
      let lhs := make (App f (Array.of_list (List.rev argsF))) in
      let rhs := make (App g (Array.of_list (List.rev argsG))) in
      (* If the return type is a `sig` we apply `proj1_sig` to the right side of the equality *)
      lazy_match! t with
        | @sig ?d ?p =>
            let rhs' := make (App constr:(@proj1_sig) (Array.of_list [d; p; rhs])) in
            make (App constr:(@eq) (Array.of_list [d; lhs; rhs']))
        | _ => make (App constr:(@eq) (Array.of_list [t; lhs; rhs]))
      end
  end.

(* Given two symbols `f` and `g` produces the term corresponding to `forall x1 .. xn , f x1 .. xn = g x1 .. xn, applying `proj1_sig` *)
(* whenever necessary to the arguments or to the return value *)
Ltac2 make_eq (f : constr) (g : constr) (reducedTypeG : constr) :=
  make_eq' f g reducedTypeG (arity reducedTypeG) [] [].

Ltac2 rec make_pred' (f : constr) (tG : constr) (pred : constr) (i : int) (args : constr list) :=
  match kind tG with
  | Prod b c =>
      make (Prod b (make_pred' f c pred (Int.add i 1) (make (Rel i) :: args)))
  | _ =>
      let fApplied := make (App f (Array.of_list args)) in
      make (App pred (Array.of_list [fApplied]))
  end.

Ltac2 make_pred (f : constr) (pred : constr) :=
  make_pred' f (Constr.type f) pred 1 [].

Tactic Notation "convert_sigless" ident(i) constr(x) :=
  elpi convert_sigless_tac ltac_string:(i) ltac_term:(x).

Tactic Notation "sig_expand" ident(i) constr(x) :=
  elpi sig_expand_tac ltac_string:(i) ltac_term:(x).

Ltac elim_refinement_types p :=
  let sigless_p := fresh p in
  let reduced_p := eval hnf in p in

  (* Replace every `sig`s, `proj1_sig` and `exist` in reduced_p *)
  convert_sigless sigless_p reduced_p;

  (* Replace sigless_p by its body *)
  let sigless_p := eval cbn in sigless_p in

  let id_conversion := fresh "id_conversion" in
  let type_p := type of p in
  let type_p_expanded := fresh "type_symbol" in

  (* Delta expand every `sig` in type_p *)
  sig_expand type_p_expanded type_p;

  (* Extract body from type_p_expanded *)
  let body_type_p := eval red in type_p_expanded in

  (* Declare and prove equality between `p` and `sigless_p` *)
  let tac := ltac2:(sigless_p' p' body_type_p' id_conversion' |-
    let sigless_p'' := Option.get (Ltac1.to_constr sigless_p') in
    let p'' := Option.get (Ltac1.to_constr p') in
    let body_type_p'' := Option.get (Ltac1.to_constr body_type_p') in
    let eq := make_eq sigless_p'' p'' body_type_p'' in
    ltac1:(eq' id_conversion'' |- assert (id_conversion'' : eq') by now simpl) (Ltac1.of_constr eq) id_conversion'
  ) in tac sigless_p p body_type_p id_conversion;

  (* Declare and prove the fact that `sigless_p` also has the property of `p` *)
  let tac := ltac2:(sigless_p' body_type_p' id_conversion' |-
      let body_type_p'' := Option.get (Ltac1.to_constr body_type_p') in
      match get_ret_sig body_type_p'' with
        | Some pred =>
          let pred_applied := make_pred (Option.get (Ltac1.to_constr sigless_p')) pred in
          ltac1:(pred' sigless_p'' id_conversion'' |-
            (* TODO: We really just want to beta reduce one time, maybe head normal form is too strong, maybe a bit of ELPI here would help *)
            let pred' := eval cbn in pred' in
            assert (pred')  by (intros; rewrite id_conversion''; apply proj2_sig))
            (Ltac1.of_constr pred_applied) sigless_p' id_conversion'
        (* If `p` only has refinement types in its arguments we skip this step, since we can't guarantee the property for the returned value *)
        | _ => ()
      end
    )
  in tac sigless_p body_type_p id_conversion;

  (* Step 4 *)

  (* Replace `p` by `sigless_p` everywhere in the context *)
  try (rewrite <- id_conversion in *; clear id_conversion);
  clear type_p_expanded.


Definition p := fun x => x > 3.

Program Definition w : sig p := exist _ 4 _.
Next Obligation.
  unfold p.
  auto.
Qed.

Set Default Proof Mode "Classic".

Goal True.
  elim_refinement_types w.


Ltac tac p :=
  let t := type of p in
  let f := fresh t in
  idtac f.


Goal True -> True.
  intro h.
  tac h.
