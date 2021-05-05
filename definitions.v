Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import utilities.
Require Import ZArith.
Require Import SMTCoq.bva.BVList.

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

(* Tuple of symbols we do not want to unfold *)
Definition prod_of_symb := (unit, Zplus, 
         Zminus, 
         Zmult, 
         Zlt_bool, 
         Zle_bool, 
         Zge_bool, 
         Zgt_bool,
         negb,
         not,
         andb,
         orb,
         implb,
         xorb,
         eqb,
         iff,
         @BITVECTOR_LIST.bv_eq,
         @BITVECTOR_LIST.bv_and,
         @BITVECTOR_LIST.bv_or,
         @BITVECTOR_LIST.bv_xor,
         @BITVECTOR_LIST.bv_add,
         @BITVECTOR_LIST.bv_mult,
         @BITVECTOR_LIST.bv_ult,
         @BITVECTOR_LIST.bv_slt,
         @BITVECTOR_LIST.bv_concat,
         @BITVECTOR_LIST.bv_shl,
         @BITVECTOR_LIST.bv_shr,
         @FArray.select,
         @FArray.diff).



Ltac get_definitions_aux p := fun k =>
 match goal with 
| |- context C[?x] => 
let x' := eval unfold x in x in is_not_in_tuple p x ; 
let H := fresh x "_def" in 
 (assert (H: x = x') by (unfold x ; reflexivity) ; k H ; clear H ;
get_definitions_aux (p, x) k)
| _ : context C[?x] |- _ => let x' := eval unfold x in x in is_not_in_tuple p x ; 
let H := fresh x "_def" in (
 assert (H : x = x') by (unfold x ; reflexivity) ; k H ; clear H ; 
 get_definitions_aux (p, x) k)
| _ => idtac 
end.

Ltac get_definitions_theories := fun k =>
let p := eval unfold prod_of_symb in prod_of_symb in get_definitions_aux p k.



(* The basic tactic, not recursive *)
Ltac get_def x := 
let x' := eval unfold x in x in 
let H := fresh x "_def" in assert (H : x = x') by reflexivity.

Ltac get_def_cont x := 
let H := fresh  x "_def" in
let _ := match goal with _ => 
let x' := eval unfold x in x in assert (H : x = x') by reflexivity end in H.











