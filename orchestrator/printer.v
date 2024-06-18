Require Import triggers.
From Ltac2 Require Import Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Message.

Ltac2 print_case (c: constr) :=
  match Constr.Unsafe.kind c with
    | Constr.Unsafe.Case _ (c1, _) _ c2 ca =>  printf "%t" c1 ; printf "%t" c2 ; Array.iter (fun x => printf "%t" x) ca
    | _ => ()
  end.

Ltac2 rec print_interp_trigger (ll : constr list list) := 
  match ll with
    | [] => printf "no more triggers to print" 
    | l :: ll' => printf "trigger interpreted:" ; List.iter (fun x => printf "%t" x) l ; print_interp_trigger ll'
  end.

(* Ltac2 Eval (print_case '(match 1 as t return 
match t with | 0 => Type | S _ => nat end with | 0 => Prop | S x => x end)). *)

Ltac2 rec concat_list (l : message list) :=
  match l with
    | [] => of_string " "
    | x :: xs => concat x (concat (of_string " ") (concat_list xs))
  end.

Ltac2 print_bool b :=
if b then print (of_string "true") else 
print (of_string "false").

Ltac2 of_option_constr o :=
  match o with
    | None => (of_string "None")
    | Some x => (concat (of_string "Some ") (of_constr x))
  end.

Ltac2 print_hyp h :=
let (x, y, z) := h in
print
(concat_list [of_ident x; of_option_constr y ; of_constr z]).

Ltac2 print_hyps hyps :=
List.iter print_hyp hyps.

Ltac2 print_env env :=
List.iter (fun (x, y) => print (concat_list [of_string x; of_string "is"; of_constr y])) env.

Ltac2 print_state cg :=
let (hs, g) := cg in 
print (of_string "The goal in the state is") ;
print (of_option_constr g) ;
print (of_string "The hyps in the state are of type") ;
print_hyps hs ;
Message.print (Message.of_string "End state").

Ltac2 rec print_triggered_tacs trigtacs :=
  match trigtacs with
    | [] => Message.print (Message.of_string "empty list")
    | (name, l) :: xs => Message.print (Message.of_string name) ; 
print_triggered_tacs xs
  end.

Ltac2 print_goal () := 
let _ := print (of_string "The Goal is") in
let g := Control.goal () in
let _ := print (of_constr g) in
let _ := print (of_string "The hypotheses are") in
let hyps := Control.hyps () in
print_hyps hyps.

  
Ltac2 print_closed_subterms c :=
let lc := closed_subterms c in List.iter (fun x => printf "%t" x) lc.
