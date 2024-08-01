From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Printf Message.
Import Unsafe.

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
    | None => ()
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

(* veriT gets stuck here but z3 and cvc5 can solve it *)
Goal forall (x : nat) , (match x with O => 3 | _ => 3 end) = 3.
  intro x.
  (* scope. *)
  (* verit. *)
  Abort.

End Examples.
