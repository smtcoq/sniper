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
    | Prod _ b => find_case b
    | Lambda _ b => find_case b
    | LetIn _ v b =>
        match find_case v with
          | Some x => Some x
          | None => find_case b
        end
    | App f args =>
        match find_case f with
          | Some x => Some x
          | None => first_some args find_case
        end
    | _ => None
  end.

Ltac2 pose_case (_ : unit) : unit :=
  let g := Control.goal () in
  match find_case g with
    | Some c =>
        let fresh_id := Fresh.in_goal @f in
        pose ($fresh_id := $c)
        (* fold $c *)
    | None => fail "No pattern matching found in goal."
  end.

Goal forall x : nat , (match x with O => 42 | _ => 41 end) = 41.
  intro x.
  pose (f := match x with | 0 => 42 | S _ => 41 end).
  fold f.

Ltac poseCase := ltac2:(pose_case ()).

Set Default Proof Mode "Classic".

Goal (match S O with O => 42 | _ => 41 end) = 41.
  poseCase.

Ltac2 print_case_option (o : constr option) : unit :=
  match o with
    | None => printf "None"
    | Some c => printf "Some %t" c
  end.

Goal True.
  let x := constr:((fun x : nat => match S O with | O => 42 | S _ => 41 end) 5) in
  print_case_option (find_case x).

Ltac2 message_of_binder (b : binder) : message :=
  match Binder.name b with
    | Some i => of_ident i
    | None => of_string "upsie"
  end.

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

Definition f : nat :=
  match S O with | O => 42 | S _ => 41 end.

Goal True.
  let x := constr:(match S O with | O => 42 | S _ => 41 end) in
  print (message_of_kind (kind x)).
Abort.
