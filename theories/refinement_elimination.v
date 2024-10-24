(* DONE: Comment the code *)
(* TODO: Add unit tests in the tests file *)
(* DONE: Add examples of usage in the examples showroom *)
(* DONE: Find a better name for the symbol introduced (maybe based on the original name) *)
(* DONE: Step three does not work if `p` has refinement types in any argument and in the return type *)
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

(* Assumes `t` is the type of a function. Computer the number of arguments that are refinement types. *)
Ltac2 rec count_ref_types (t : constr) : int :=
  match kind t with
    | Prod b c =>
        lazy_match! Constr.Binder.type b with
          | @sig _ _ => Int.add 1 (count_ref_types c)
          | _ => count_ref_types c
        end
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
Ltac2 rec make_eq' (f : constr) (g : constr) (body_type_g : constr) (i : int) (argsF : constr list) (argsG : constr list) :=
  match kind body_type_g with
  | Prod b c =>
      (* If the current argument is a `sig`, we apply the function to `proj1_sig (Rel i)`, otherwise is just `Rel i` *)
      lazy_match! Constr.Binder.type b with
        | @sig ?d ?p =>
            let argF : constr := make (App constr:(@proj1_sig) (Array.of_list [d; p; make (Rel i)])) in
            make (Prod b (make_eq' f g c (Int.sub i 1) (argF :: argsF) (make (Rel i) :: argsG)))
        | _ => make (Prod b (make_eq' f g c (Int.sub i 1) (make (Rel i) :: argsF) (make (Rel i) :: argsG)))
      end
  | _ =>
      let lhs := make (App f (Array.of_list (List.rev argsF))) in
      let rhs := make (App g (Array.of_list (List.rev argsG))) in
      (* If the return type is a `sig` we apply `proj1_sig` to the right side of the equality *)
      lazy_match! body_type_g with
        | @sig ?d ?p =>
            let rhs' := make (App constr:(@proj1_sig) (Array.of_list [d; p; rhs])) in
            make (App constr:(@eq) (Array.of_list [d; lhs; rhs']))
        | _ => make (App constr:(@eq) (Array.of_list [body_type_g; lhs; rhs]))
      end
  end.

(* Given two symbols `f` and `g` produces the term corresponding to `forall x1 .. xn , f x1 .. xn = g x1 .. xn, applying `proj1_sig` *)
(* whenever there is a type mismatch in the arguments or in the return value *)
Ltac2 make_eq (f : constr) (g : constr) (body_type_g : constr) :=
  (* `arity body_type_g` represents the De Bruijn index of `x1` in the final expression *)
  make_eq' f g body_type_g (arity body_type_g) [] [].

Ltac2 rec make_pred' (f : constr) (body_type_g : constr) (pred : constr) (i : int) (args : constr list) :=
  match kind body_type_g with
  | Prod b c =>
      lazy_match! Constr.Binder.type b with
        (* In this case we want to produce forall x : d , forall h : pred x , (recursive call) *)
        | @sig ?d ?p =>
            (* binder for a variable of type `d` *)
            let binder_d := Constr.Binder.make None d in
            (* binder for a proof of `pred` of the variable we just introduced *)
            let d_pred := make (App pred (Array.of_list [make (Rel 1)])) in
            let binder_d_pred := Constr.Binder.make None d_pred in
            (* Here instead of adding just `x` to the args of `f` in the final expression, we add `proj1_sig (exist x h)` *)
            (* Which evaluates to `x`. This is necessary since, when proving that the resulting expression holds, we will *)
            (* use the result of the previous step, which states that `f (proj1_sig x) = g x`. *)
            (* Note: `Rel i` is `x` and `Rel (Int.sub i 1)` is `h` in the final expression. *)
            let exist_arg := make (App constr:(@exist) (Array.of_list [d; p; make (Rel i); make (Rel (Int.sub i 1))])) in
            let arg := make (App constr:(@proj1_sig) (Array.of_list [d; p; exist_arg])) in
            (* We subtract 2 from `i` in the recursive call since we added two binders *)
            let rest := make_pred' f c pred (Int.sub i 2) (arg :: args) in
            make (Prod binder_d (make (Prod binder_d_pred rest)))
        | _ => make (Prod b (make_pred' f c pred (Int.sub i 1) (make (Rel i) :: args)))
      end
  | _ =>
      let fApplied := make (App f (Array.of_list (List.rev args))) in
      make (App pred (Array.of_list [fApplied]))
  end.

(* Given a symbol `f` and a predicate `pred`, produces the term corresponding to *)
(* `forall x1 .. xn , pred y1 -> .. -> pred ym -> pred (f x1 .. xn) *)
(* The variables `y1` .. `ym` are defined based on which parameters in `body_type_g` are refinement types. *)
(* The parameters of `f` and `g` need to have the same type, except for some parameters that have the form *)
(* `sig A P` in `g` and `A` in `f`. *)
Ltac2 make_pred (body_type_g : constr) (f : constr) (pred : constr) :=
  (* Int.add (arity body_type_g) (count_ref_types body_type_g) represents the De Bruijn index of x1 in the final expression *)
  make_pred' f body_type_g pred (Int.add (arity body_type_g) (count_ref_types body_type_g)) [].

Tactic Notation "convert_sigless" ident(i) constr(x) :=
  elpi convert_sigless_tac ltac_string:(i) ltac_term:(x).

Tactic Notation "sig_expand" ident(i) constr(x) :=
  elpi sig_expand_tac ltac_string:(i) ltac_term:(x).

Ltac elim_refinement_types p :=
  let sigless_p := fresh "sigless_symbol" in
  let reduced_p := eval hnf in p in

  (* Replace every `sig`s, `proj1_sig`s and `exist`s in reduced_p *)
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
    ltac1:(eq' id_conversion'' |- assert (id_conversion'' : eq') by now simpl ) (Ltac1.of_constr eq) id_conversion'
  ) in tac sigless_p p body_type_p id_conversion;

  (* Declare and prove the fact that `sigless_p` also has the property of `p` *)
  let tac := ltac2:(sigless_p' body_type_p' id_conversion' |-
      let body_type_p'' := Option.get (Ltac1.to_constr body_type_p') in
      match get_ret_sig body_type_p'' with
        | Some pred =>
          let pred_applied := make_pred body_type_p'' (Option.get (Ltac1.to_constr sigless_p')) pred in
          ltac1:(pred' sigless_p'' id_conversion'' |-
            let H := fresh "H" in
            assert (pred') by (intros; rewrite id_conversion''; apply proj2_sig);
            cbn in H (* eliminate `proj1_sig (exist ...)` introduced by make_pred *)
          ) (Ltac1.of_constr pred_applied) sigless_p' id_conversion'
        (* If `p` only has refinement types in its arguments we skip this step, since we can't guarantee the property for the returned value *)
        | _ => ()
      end
    )
  in tac sigless_p body_type_p id_conversion;

  (* Replace `p` by `sigless_p` everywhere in the context *)
  try (rewrite <- id_conversion in *; clear id_conversion);
  clear type_p_expanded.


Definition p := fun x => x > 3.

Set Default Proof Mode "Classic".

Program Definition k : nat -> sig p -> nat -> sig p -> nat -> sig p := fun _ _ _ _ _ => exist _ 4 _.
Next Obligation.
  unfold p.
  auto.
Qed.

Goal True.
  elim_refinement_types k.
  trivial.
Qed.
