From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Printf Message.
Import Unsafe.

(* | Rel (int) *)
(* | Var (ident) *)
(* | Meta (meta) *)
(* | Evar (evar, constr array) *)
(* | Sort (sort) *)
(* | Cast (constr, cast, constr) *)
(* | Prod (binder, constr) *)
(* | Lambda (binder, constr) *)
(* | LetIn (binder, constr, constr) *)
(* | App (constr, constr array) *)
(* | Constant (constant, instance) *)
(* | Ind (inductive, instance) *)
(* | Constructor (constructor, instance) *)
(* | Case (case, constr, case_invert, constr, constr array) *)
(* | Fix (int array, int, binder array, constr array) *)
(* | CoFix (int, binder array, constr array) *)
(* | Proj (projection, constr) *)
(* | Uint63 (uint63) *)
(* | Float (float) *)
(* | Array (instance, constr array, constr, constr) *)

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 rec first_some (args : 'a array) (f : 'a -> 'b option) : 'b option :=
  let rec loop args_list :=
    match args_list with
      | [] => None
      | arg::args_tail =>
          match f arg with
            | Some c => Some c
            | None => loop args_tail
          end
      end
  in
  loop (Array.to_list args).

Ltac2 rec find_case (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
    | Case _ _ _ _ _ => Some c
    | LetIn _ v b => find_case v
        (* find_case b will have the same problem as lambda and prod *)
    | App f args =>
        match find_case f with
          | Some x => Some x
          | None => first_some args find_case
        end
    (* Should we go inside lambdas and prods? Lambdas will be taken care of by another transformation, and we don't support prods *)
    | Prod _ b => None
    | Lambda _ b => None
    | _ => None
  end.

Ltac2 pose_case (_ : unit) : unit :=
  match find_case (Control.goal ()) with
    | Some c =>
        let fresh_id := Fresh.in_goal @pat in
        pose ($fresh_id := $c);
        let new_constr :=
          make (Var fresh_id) in
        fold $new_constr
    | None => fail "No pattern matching found in goal."
  end.

Set Default Proof Mode "Classic".

Ltac pose_case := ltac2:(pose_case ()).

Section Examples.

(* pose_case does not work here (but regular scope works) -> we have to avoid lambdas? *)
Goal forall x : nat , ((fun y => (match y with O => 42 | _ => 41 end)) x) = 41.
  intro x.
  (* pose_case. *)
  Abort.

(* This case was not covered before *)
Goal forall (x : nat) (f g : nat -> nat) , ((match x with O => f | S _ => g end) 42 = 42).
  intros x f g.
  pose_case.
  (* now one can do scope *)
  Abort.

(* Why this can't be solved by pose_case + scope + verit? *)
Goal forall (x : nat) , (match x with O => 42 | _ => 42 end) = 42.
  intro x.
  pose_case.
  Abort.

(* This one was already covered *)
Goal forall y : nat , let x := match y with | O => 2 | S _ => 3 end in x = x.
  intro y.
  pose_case.
  Abort.

End Examples.
