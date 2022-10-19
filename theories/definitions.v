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


Require Import String.
Require Import utilities.
From SMTCoq Require Import SMTCoq.

(* Recursive, be careful: it can unfold definitions that we want to keep folded *)
Ltac get_definitions := repeat match goal with 
| |- context C[?x] => let H := fresh x "_def" in
let x' := eval unfold x in x in (match goal with 
| _ : x = x' |- _ => fail 1
| _ => idtac
end ; let H := fresh x "_def" in 
 assert (H: x = x') by (unfold x ; reflexivity))
| _ : context C[?x] |- _ => let x' := eval unfold x in x in (match goal with 
                  | _ : x = x' |- _ => fail 1
                  | _ => idtac
end ;
 assert (H: x = x') by (unfold x ; reflexivity))
end.

Ltac get_definitions_aux p p' p'' := fun k =>
 match goal with 
| |- context C[?x] => 
let x' := eval unfold x in x in is_not_in_tuple p x ; 
let T := type of x in let T' := get_head T in is_not_in_tuple p'' T' ;
let H := fresh x "_def" in 
 (assert (H: x = x') by (unfold x ; reflexivity) ; k H ; clear H ;
get_definitions_aux (p, x) (p', x) p'' k)
| _ : context C[?x] |- _ => let x' := eval unfold x in x in is_not_in_tuple p x ; 
let T := type of x in let T' := get_head T in is_not_in_tuple p'' T' ;
let H := fresh x "_def" in (
 assert (H : x = x') by (unfold x ; reflexivity) ; k H ; clear H ; 
 get_definitions_aux (p, x) (p', x) p'' k)
| _ => generalize_dependent_tuple p'
end.

Ltac get_definitions_aux_no_generalize p p' := fun k =>
 match goal with 
| |- context C[?x] => 
let x' := eval unfold x in x in is_not_in_tuple p x ;
let T := type of x in let T' := get_head T in is_not_in_tuple p' T' ;
let H := fresh x "_def" in 
 (assert (H: x = x') by (unfold x ; reflexivity) ; k H ; clear H ;
get_definitions_aux_no_generalize (p, x) p' k)
| _ : context C[?x] |- _ => let x' := eval unfold x in x in is_not_in_tuple p x ; 
let T := type of x in let T' := get_head T in is_not_in_tuple p' T' ;
let H := fresh x "_def" in (
 assert (H : x = x') by (unfold x ; reflexivity) ; k H ; clear H ;
 get_definitions_aux_no_generalize (p, x) p' k)
| _ => idtac
end.

Ltac get_definitions_theories p0 := fun k =>
get_definitions_aux p0 default CompDec k.

Ltac get_definitions_theories_no_generalize p0 := fun k =>
get_definitions_aux_no_generalize p0 CompDec k.

(* The basic tactic, not recursive *)
Ltac get_def x := 
let x' := eval unfold x in x in 
let H := fresh x "_def" in assert (H : x = x') by reflexivity.

Ltac get_def_cont x := 
let H := fresh  x "_def" in
let _ := match goal with _ => 
let x' := eval unfold x in x in assert (H : x = x') by reflexivity end in H.
