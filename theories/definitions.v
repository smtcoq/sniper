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

(* For avoiding definitions with higher order terms we do not 
want to unfold definitions such as the one of List.map *)
Ltac contains_ho_argument t :=
let T := type of t in let Hfalse := fresh in 
assert (Hfalse : False -> T) by  
(intro Helim ;
let rec tac T :=
  lazymatch T with
  | forall (x : ?A), ?B => lazymatch A with
    | forall (y : ?C), ?D => inversion Helim
    | _ => try intro ; match goal with | |- ?G => tac G end
    end
  | _ => fail
  end in tac T) ; clear Hfalse.


(* Avoid to unfold CompDecs *)
Ltac has_subterms_type_CompDec t :=
  let T := type of t in 
  let T' := get_head T in 
  match T' with
  | CompDec => idtac
  | context c[@CompDec _ ] => idtac
  end.

Goal False.
contains_ho_argument (@List.fold_left).
(* contains_ho_argument (@List.hd). *) Abort.

Goal False.
has_subterms_type_CompDec (Nat_compdec).
has_subterms_type_CompDec (list_compdec).
Fail has_subterms_type_CompDec True.
Abort.
                
Ltac assert_and_prove_eq_cont x x' k := 
let H := fresh x "_def" in 
assert (H: x = x') by reflexivity ; k H ; clear H.

Ltac get_definitions_aux0 p p' p'' := fun k k' =>
 match goal with 
| |- context C[?x] => is_not_in_tuple p x ;
tryif (first [contains_ho_argument x | has_local_def x]) then 
(* we do not want to unfold : higher order functions and local definitions *)
get_definitions_aux0 (p, x) p' p'' k k' else
( let T := type of x in let T' := get_head T in is_not_in_tuple p'' T' ;
let x' := eval unfold x in x in 
assert_and_prove_eq_cont x x' k ;
get_definitions_aux0 (p, x) (p', x) p'' k k')
| _ : context C[?x] |- _ => is_not_in_tuple p x ; 
tryif (first [ first [contains_ho_argument x | has_local_def x] | has_subterms_type_CompDec x]) then
get_definitions_aux0 (p, x) p' p'' k k' else
(let T := type of x in let T' := get_head T in is_not_in_tuple p'' T' ;
let x' := eval unfold x in x in  
assert_and_prove_eq_cont x x' k ;
 get_definitions_aux0 (p, x) (p', x) p'' k k')
| _ => k' p'
end.

Ltac get_definitions_aux p p' p'' := fun k =>
get_definitions_aux0 p p' p'' k ltac:(generalize_dependent_tuple).

Ltac get_definitions_aux_no_generalize p p' p'' := fun k =>
get_definitions_aux0 p p' p'' k ltac:(fun _ => idtac).

Ltac get_definitions_theories p0 := fun k =>
get_definitions_aux p0 default CompDec k.

Ltac get_definitions_theories_no_generalize p0 := fun k =>
get_definitions_aux_no_generalize p0 default CompDec k.

(* The basics tactics, not recursive, used for tests *)
Ltac get_def x := 
let x' := eval unfold x in x in 
let H := fresh x "_def" in assert (H : x = x') by reflexivity.

Ltac get_def_cont x := 
let H := fresh  x "_def" in
let _ := match goal with _ => 
let x' := eval unfold x in x in assert (H : x = x') by reflexivity end in H.

Goal forall (l : list nat) (x : nat), List.hd_error l = Some x -> (l <> nil)
-> List.map S nil = nil.
Proof. get_definitions_theories unit ltac:(fun H => idtac). Abort.

(* We do not want to unfold terms which are of type CompDec T *)
Definition c := Nat_compdec.

Goal CompDec nat -> eqb_of_compdec c 0 0 -> True. intros.
get_definitions_theories unit ltac:(fun H => idtac). Abort.
