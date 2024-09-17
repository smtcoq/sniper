(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import MetaCoq.Template.All.
Require Import utilities.
Require Import reflexivity.
Require Import unfold_reflexivity.
Require Import unfold_in.
Require Import List.
Import ListNotations.
Require Import String.

Definition list_of_args_and_codomain (t : term) := 
let fix aux acc t := 
match t with
  | tProd _ t1 t2 => aux (t1 :: acc) t2
  | _ => (acc, t)
end in aux [] t.

Unset Guard Checking. (* Not dangerous: we do not use this function in proofs ! *)

(* Takes a term, if it is a function or a fixpoint
returns the names of its arguments, otherwise returns [].
The goal is to improve names generation in Sniper *) 

Fixpoint get_names_args_fix (f : mfixpoint term) :=
match f with
  | [] => []
  | {| dname := _ ; dtype := _ ; dbody := t ; rarg := _ |} :: xs => 
    get_names_args_fun t ++ get_names_args_fix xs
end with
get_names_args_fun (t : term) :=
match t with
  | tLambda {| binder_name := x; binder_relevance := _ |} _ u =>
    let na :=
    match x with
      | nAnon => "x"%bs
      | nNamed y => y
    end
    in na :: get_names_args_fun u
  | tFix f _ => get_names_args_fix f 
  | _ => []
end.

Set Guard Checking.

Open Scope string_scope. 

Definition names_aux (l : list bytestring.string) : 
(bytestring.string * list bytestring.string) :=
(hd "x"%bs l, tl l).

(* gen_eq [A1; ...; An] B t u = 
  tProd A1 ... (tProd An (tApp < @eq > (tApp (tApp ... (tApp (lift 1 n t) [tRel (n-1)]) ... [tRel 0])
(tApp (tApp ... (tApp (lift 1 n u) [tRel (n-1)]) ... [tRel 0]) *)

Fixpoint gen_eq 
(l : list term) (* types of args of the functions *)
(B : term) (* codomain of functions *)
(t : term) (* function 1 *)
(u : term) (* function 2 *)
(lnames : list bytestring.string) (* list of names *)
{struct l} := 
match l with
  | [] => mkEq B t u
  | A :: l' => 
    let p := names_aux lnames in
    mkProdName (p.1)%bs A 
    (gen_eq l' B (tApp (lift 1 0 t) [tRel 0]) (tApp (lift 1 0 u) [tRel 0]) p.2)
end.

(* if H : t = u then expand_hyp H produces the hypothesis forall x1 ... xn, t x1 ... xn = u x1 ... xn *)

Ltac expand_hyp_cont H := fun k =>
lazymatch type of H with 
| @eq ?A ?t ?u => 
let A := metacoq_get_value (tmQuote A) in
let t := metacoq_get_value (tmQuote t) in
let u := metacoq_get_value (tmQuote u) in
let names1 := eval cbv in (get_names_args_fun t) in
let names := 
    match names1 with
      | [] => constr:(get_names_args_fun u)
      | _ :: _ => names1
    end in
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u names)
in let z := metacoq_get_value (tmUnquote eq) in
let u := eval hnf in (z.(my_projT2)) in let H' := fresh in 
(assert (H': u) by now rewrite H ;
k H')
| _ => k H
end.

Ltac expand_tuple p := fun k => 
match constr:(p) with
| (?x, ?y) =>
expand_hyp_cont x ltac:(fun H' => expand_tuple constr:(y) ltac:(fun p => k (H', p))) ; clear x
| unit => k unit
end.

Ltac expand_hyp H := expand_hyp_cont H ltac:(fun _ => idtac).

Ltac expand_fun f :=
  let f_def := eval unfold f in f in
  let H := fresh in assert (H : f = f_def) by reflexivity ;
  expand_hyp H ; clear H. 

Section tests.

Goal False.
assert_refl length.
unfold_refl H.
expand_hyp H.
assert (forall x : string, length x = match x with 
| ""%string => 0
| String _ s' => S (length s') 
end). intros x. destruct x ; simpl ; reflexivity.
Abort. 

Goal False.
expand_fun Datatypes.length.
expand_fun hd.
Abort.

Variable (A B: Type).
Variable (f: A -> B).

Goal False.
pose (map' := List.map f).
assert_refl map'.
unfold_refl H.
expand_hyp H.
unfold_refl H0.
unfold_in H0 map.
Abort.

End tests.








