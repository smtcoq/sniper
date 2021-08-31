





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


Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.Template.All.
Require Import utilities.
Require Import definitions.
Require Import Coq.Arith.PeanoNat.
Require Import String.



Definition is_type_of_fun (T : term) :=
match T with
| tProd _ _ _ => true
| _ => false
end.

Definition list_of_args_and_codomain (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
| _ => (acc, t)
end in aux [] t.

Open Scope string_scope.
Fixpoint gen_eq (l : list term) (B : term) (t : term) (u : term) {struct l} := 
match l with
| [] => mkEq B t u
| A :: l' => mkProdName "x" A (gen_eq l' B (mkApp (lift 1 0 t) (tRel 0)) (mkApp (lift 1 0 u) (tRel 0)))
end.

(* if H : t = u then expand_hyp H produces the hypothesis forall x1 ... xn, t x1 ... xn = u x1 ... xn *)

Ltac expand_hyp H :=
lazymatch type of H with 
| @eq ?A ?t ?u => let A := metacoq_get_value (tmQuote A) in
let t := metacoq_get_value (tmQuote t) in
let u := metacoq_get_value (tmQuote u) in
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u)
in let z := metacoq_get_value (tmUnquote eq) in
let u := eval hnf in (z.(my_projT2)) in let H' := fresh in 
(assert (H': u) by (intros ; rewrite H; reflexivity))
| _ => fail "not an equality"
end.




Ltac expand_hyp_cont H := fun k =>
lazymatch type of H with 
| @eq ?A ?t ?u => let A := metacoq_get_value (tmQuote A) in
let t := metacoq_get_value (tmQuote t) in
let u := metacoq_get_value (tmQuote u) in
let p := eval cbv in (list_of_args_and_codomain A) in 
let l := eval cbv in (rev p.1) in 
let B := eval cbv in p.2 in 
let eq := eval cbv in (gen_eq l B t u)
in let z := metacoq_get_value (tmUnquote eq) in
let u := eval hnf in (z.(my_projT2)) in let H' := fresh in 
(assert (H': u) by (intros ; rewrite H; reflexivity) ; 
k H')
| _ => fail "not an equality"
end.

Ltac expand_tuple p := fun k => 
match constr:(p) with
| (?x, ?y) =>
expand_hyp_cont x ltac:(fun H' => expand_tuple constr:(y) ltac:(fun p => k (H', p))) ; clear x
| unit => k unit
end.

Ltac expand_fun f :=
let H:= get_def_cont f in expand_hyp H ; clear H.



Section tests.

Goal False.
get_def length.
expand_hyp length_def.
assert (forall x : string, length x = match x with 
| ""%string => 0
| String _ s' => S (length s') 
end). intros x. destruct x ; simpl ; reflexivity.
Abort. 


Goal False.
get_def length.
expand_hyp length_def.
expand_fun Datatypes.length.
Abort.

Goal forall (A: Type) (l : list A) (a : A), hd a l = a -> tl l = [].
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => idtac )).
Abort.


End tests.








