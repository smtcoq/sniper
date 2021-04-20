Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import Bool Int63 PArray BinNat BinPos ZArith SMT_classes_instances.
Require Import Misc State BVList. (* FArray Equalities DecidableTypeEx. *)
Require FArray.




Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

(* [inverse_tactic tactic] succceds when [tactic] fails, and the other way round *)
Ltac inverse_tactic tactic := try (tactic; fail 1).

(* [constr_neq t u] fails if and only if [t] and [u] are convertible *)
Ltac constr_neq t u := inverse_tactic ltac:(constr_eq t u).

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


Definition prod_of_symb := (unit, Zplus, 
         Zminus, 
         Zmult, 
         Zlt_bool, 
         Zle_bool, 
         Zge_bool, 
         Zgt_bool,
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

Ltac get_definitions_built_in_theories :=  
repeat match goal with 
| |- context C[?x] =>  
         constr_neq Zplus x ;
         constr_neq Zminus x ;
         constr_neq Zmult x ;
         constr_neq Zlt_bool x ;
         constr_neq Zle_bool x ;
         constr_neq Zge_bool x ;
         constr_neq Zgt_bool x ;
         constr_neq Typ.i_eqb x ;
         constr_neq @BITVECTOR_LIST.bv_and x ;
         constr_neq @BITVECTOR_LIST.bv_or x ;
         constr_neq @BITVECTOR_LIST.bv_xor x ;
         constr_neq @BITVECTOR_LIST.bv_add x ;
         constr_neq @BITVECTOR_LIST.bv_mult x ;
         constr_neq @BITVECTOR_LIST.bv_ult x ;
         constr_neq @BITVECTOR_LIST.bv_slt x ;
         constr_neq @BITVECTOR_LIST.bv_concat x ;
         constr_neq @BITVECTOR_LIST.bv_shl x ;
         constr_neq @BITVECTOR_LIST.bv_shr x ;
         constr_neq FArray.select x ;
         constr_neq FArray.diff x ;
let H := fresh x "_def" in
let x' := eval unfold x in x in (match goal with 
| _ : x = x' |- _ => fail 1
| _ => idtac
end ; let H := fresh x "_def" in 
 assert (H: x = x') by (unfold x ; reflexivity))
| _ : context C[?x] |- _ =>  constr_neq Zplus x ;
         constr_neq Zminus x ;
         constr_neq Zmult x ;
         constr_neq Zlt_bool x ;
         constr_neq Zle_bool x ;
         constr_neq Zge_bool x ;
         constr_neq Zgt_bool x ;
         constr_neq Typ.i_eqb x ;
         constr_neq @BITVECTOR_LIST.bv_and x ;
         constr_neq @BITVECTOR_LIST.bv_or x ;
         constr_neq @BITVECTOR_LIST.bv_xor x ;
         constr_neq @BITVECTOR_LIST.bv_add x ;
         constr_neq @BITVECTOR_LIST.bv_mult x ;
         constr_neq @BITVECTOR_LIST.bv_ult x ;
         constr_neq @BITVECTOR_LIST.bv_slt x ;
         constr_neq @BITVECTOR_LIST.bv_concat x ;
         constr_neq @BITVECTOR_LIST.bv_shl x ;
         constr_neq @BITVECTOR_LIST.bv_shr x ;
         constr_neq FArray.select x ;
         constr_neq FArray.diff x ;
let x' := eval unfold x in x in (match goal with 
                  | _ : x = x' |- _ => fail 1
                  | _ => idtac
end ;
 assert (H: x = x') by (unfold x ; reflexivity))
end.


Goal forall (x y : Z), Zplus x y = Zminus x y.
get_definitions_built_in_theories.
get_definitions.
Abort.




Ltac is_not_in_tuple p z := 
match constr:(p) with
| (?x, ?y) => constr_neq y z ; is_not_in_tuple constr:(x) z ; idtac x "1" ; idtac y "2" ; idtac z "3"
| unit => idtac p
end.

Ltac get_definitions_ho p := fun k =>
match goal with 
| |- context C[?x] => 
let x' := eval unfold x in x in is_not_in_tuple p x ; let H := fresh in 
 (assert (H: x = x') by (unfold x ; reflexivity) ; k H ; clear H ; get_definitions_ho (p, x) k)
| _ : context C[?x] |- _ => let x' := eval unfold x in x in is_not_in_tuple p x ; let H := fresh in (
 assert (H : x = x') by (unfold x ; reflexivity) ; k H ; clear H ; get_definitions_ho (p, x) k)
| _ => idtac 
end
.
Ltac get_definitions_aux p := fun k =>
 match goal with 
| |- context C[?x] => 
let x' := eval unfold x in x in is_not_in_tuple p x ; 
let H := fresh x "_def" in 
 (assert (H: x = x') by (unfold x ; reflexivity) ; k H ; clear H ;
get_definitions_aux ((p, x), unit) k)
| _ : context C[?x] |- _ => let x' := eval unfold x in x in is_not_in_tuple p x ; 
let H := fresh x "_def" in (
 assert (H : x = x') by (unfold x ; reflexivity) ; k H ; clear H ; 
 get_definitions_aux ((p, x), unit) k)
| _ => idtac 
end
.



Ltac get_definitions_theories := fun k =>
let p := eval unfold prod_of_symb in prod_of_symb in get_definitions_aux p k.

Goal forall (A: Type) (l : list A) (a : A), hd a l = a -> tl l = [] -> (forall (x y : Z), (x +y)%Z = 
(x-y)%Z).
get_definitions_theories ltac:(fun p => let T:= type of p in pose T).
Abort.


(* The basic tactic, not recursive *)
Ltac get_def x := 
let x' := eval unfold x in x in 
let H := fresh x "_def" in assert (H : x = x') by reflexivity.

Ltac get_def_cont x := 
let H := fresh  x "_def" in
let _ := match goal with _ => 
let x' := eval unfold x in x in assert (H : x = x') by reflexivity end in H.


Ltac unfold_recursive x := let x' := eval unfold x in x in try unfold_recursive x' ; 
(match goal with 
| H : x = x' |- _ => fail 1
| _ => idtac
end ; let H := fresh in
 assert (H : x = x') by (unfold x ; reflexivity)).

Ltac subst_def_no_clear x := repeat match goal with
| H : x = ?x', H' : ?x' = ?x''|- _ => rewrite H' in H ; subst_def_no_clear x''
end.


Ltac subst_def x := repeat match goal with
| H : x = ?x', H' : ?x' = ?x''|- _ => rewrite H' in H ; clear H' ; subst_def x''
end.

Ltac unfold_recursive_subst x := 
unfold_recursive x ; subst_def x.

(* MetaCoq version of the same tactic *)

Ltac unquote_env_aux e := match e with 
| [] => idtac
| ?x :: ?xs => unquote_term x ; unquote_env_aux xs
end.

(* Nothing about inductives for now *)
Fixpoint get_decl (e : global_env) := match e with 
| [] => []
| x :: e' => match (snd x) with
      | ConstantDecl u => match u.(cst_body) with
            | Some v => v :: get_decl e'
            | None => get_decl e'
            end
      | InductiveDecl u => get_decl e'
      end
end.

Ltac unquote_env e := let e' := constr:(fst e) in 
let l := constr:(get_decl e') in let l':= eval compute in l in 
unquote_env_aux l'.

Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t) ltac:(fun x => (pose  x as idn))).

Ltac get_definition_standard_library t := let e := fresh in rec_quote_term t e ;
unquote_env e ; clear e.









