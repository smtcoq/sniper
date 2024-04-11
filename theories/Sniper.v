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



Require Export SMTCoq.SMTCoq.

From elpi Require Import elpi.

Require Export utilities.
Require Export definitions.
Require Export higher_order.
Require Export anonymous_functions.
Require Export elimination_fixpoints.
Require Export expand.
Require Export elimination_pattern_matching. 
Require Export instantiate_type.
Require Export case_analysis.
Require Export case_analysis_existentials.
Require Export interpretation_algebraic_types.
Require Export instantiate_inductive_pars.
Require Export indrel.
Require Export add_hypothesis_on_parameters.
Require Export compdec_plugin.
Require Export generate_fix.
Require Export proof_correctness.
Require Import ZArith.
Require Import PArith.BinPos.
Require Import SMTCoq.bva.BVList.
Require Import NArith.BinNatDef.
From Trakt Require Export Trakt.
From Ltac2 Require Import Ltac2.

(** Preprocessing for SMTCoq (first-order classical logic with interpreted theories) **)

(* Tuple of symbols we do not want to unfold 
in the default tactic *)
Definition prod_of_symb := (default,
         Zplus,
         Zminus, 
         Zmult,
         Z.eqb,
         Zlt_bool, 
         Zle_bool, 
         Zge_bool, 
         Zgt_bool,
         Z.lt,
         Z.le,
         Z.ge,
         Z.gt,
         Pos.lt, 
         Pos.le, 
         Pos.ge, 
         Pos.gt,
         Z.to_nat,
         Pos.mul,
         Pos.add,
         Pos.sub,
         Init.Nat.add,
         Init.Nat.mul,
         Nat.eqb,
         Nat.leb,
         Nat.ltb,
         Init.Peano.lt,
         Init.Peano.ge,
         Init.Peano.gt,
         N.add,
         N.mul,
         N.eqb,
         N.leb,
         N.ltb,
         Init.Peano.lt,
         Init.Peano.ge,
         Init.Peano.gt,
         negb,
         not,
         andb,
         orb,
         implb,
         xorb,
         Bool.eqb,
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
         @FArray.diff,
         is_true,
         @eqb_of_compdec, 
         @CompDec, 
         Nat_compdec,
         list_compdec,
         prod_compdec,
         Z_compdec).

Definition prod_types := (Z, bool, True, False, positive, N, and, or, nat, Init.Peano.le,
@CompDec, Comparable, EqbType, Inhabited, OrderedType.Compare).

(* Whenever a constant is defined as foo : CompDec A, 
we do not want to unfold foo *) 
Definition tuple_type_of_opaque_def := CompDec.

Ltac def_and_pattern_matching p1 k := 
anonymous_funs ; prenex_higher_order_with_equations ;
let p1' := eval unfold p1 in p1 in
k p1' ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_dependent_pattern_matching H')).

Ltac def_fix_and_pattern_matching p1 k := 
anonymous_funs ; prenex_higher_order_with_equations ;
let p1' := eval unfold p1 in p1 in
k p1' ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_cont H' ltac:(fun H'' =>
try (eliminate_dependent_pattern_matching H'')))).

Ltac def_and_pattern_matching_mono p1 k :=
def_and_pattern_matching p1 k ; inst.

Ltac def_and_pattern_matching_mono_param p1 t k :=
def_and_pattern_matching p1 k ; inst t.

Ltac def_fix_and_pattern_matching_mono_param p1 t k :=
def_fix_and_pattern_matching p1 ; k.

Ltac scope_param p1 p2 t := revert_all ; trakt bool ;
let p2' := eval unfold p2 in p2 in
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2' ; (def_fix_and_pattern_matching p1 
ltac:(fun x x' => inst t; get_definitions_theories x x'; intros; inst)).


Ltac scope_no_param p1 p2 := revert_all ; trakt bool ; 
let p2' := eval unfold p2 in p2 in
intros ; 
repeat match goal with
| H : _  |- _ => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2'; try (def_fix_and_pattern_matching p1 
ltac:(get_definitions_theories); intros ; inst) ;
let function := ltac2:(p2' |- match (Ltac2.Ltac1.to_constr (p2'))
with | None => fail | Some pr => get_projs_in_variables pr end) in function p2'.

Ltac snipe_param_no_check p1 p2 t :=
scope_param p1 p2 t ; verit_no_check.

Ltac snipe_no_param_no_check p1 p2 :=
scope_no_param p1 p2 ; verit_no_check.

Ltac snipe_param p1 p2 t :=
scope_param p1 p2 t ; verit.

Ltac snipe_no_param p1 p2 :=
scope_no_param p1 p2 ; verit.

Tactic Notation "elimination_polymorphism" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.

Tactic Notation "scope2_aux" constr(p1) constr(p2) uconstr_list_sep(l, ",") := 
let p2' := eval unfold p2 in p2 in
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching p1 ltac:(get_definitions_theories_no_generalize) ; 
elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context) ;
let function :=
ltac2:(p2' |- match (Ltac2.Ltac1.to_constr (p2'))
with | None => fail | Some pr => get_projs_in_variables pr end) in function p2'.

Tactic Notation "snipe2" uconstr_list_sep(l, ",") :=
let p2' := eval unfold prod_types in prod_types in
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching prod_of_symb ltac:(get_definitions_theories_no_generalize); intros ;
elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context) ;
let function :=
ltac2:(p2' |- match (Ltac2.Ltac1.to_constr (p2'))
with | None => fail | Some pr => get_projs_in_variables pr end) in function p2' ; verit.


Tactic Notation "snipe_no_check" constr(t) := snipe_param_no_check prod_of_symb prod_types t.
Tactic Notation "snipe_no_check" := snipe_no_param_no_check prod_of_symb prod_types.

Tactic Notation "scope" constr(t) := scope_param prod_of_symb prod_types t.
Tactic Notation "scope" := scope_no_param prod_of_symb prod_types.

Tactic Notation "snipe" constr(t) := snipe_param prod_of_symb prod_types t.
Tactic Notation "snipe" := snipe_no_param prod_of_symb prod_types.


Tactic Notation "snipe_no_check_timeout" constr(t) int_or_var(n) := scope_param prod_of_symb prod_types t ; verit_no_check_timeout n.
Tactic Notation "snipe_no_check_timeout" int_or_var(n) := scope_no_param prod_of_symb prod_types ; verit_no_check_timeout n.

Tactic Notation "snipe_timeout" constr(t) int_or_var(n) := scope_param prod_of_symb prod_types t ; verit_timeout n.
Tactic Notation "snipe_timeout" int_or_var(n) := scope_no_param prod_of_symb prod_types ; verit_timeout n.

(** Preprocessing for first-order intuitionistic logic with no interpreted symbols **)

Definition tuple_def := (iff, not).

Ltac scope_param_intuitionistic t := 
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal default; try (def_fix_and_pattern_matching_mono_param tuple_def t 
ltac:(get_definitions_theories_no_generalize); inv_principle_all; inst) ; 
let function := 
ltac2:(tuple_def |- match (Ltac2.Ltac1.to_constr (tuple_def))
with | None => fail | Some pr => get_projs_in_variables pr end) in function tuple_def.

Ltac scope_no_param_intuitionistic := 
intros ; 
repeat match goal with
| H : _ |- _  => eliminate_dependent_pattern_matching H
| _ => fail
end ;
try interp_alg_types_context_goal default ; try (def_fix_and_pattern_matching tuple_def 
ltac:(get_definitions_theories_no_generalize) ; inv_principle_all ; inst) ; 
let function :=
ltac2:(tuple_def |- match (Ltac2.Ltac1.to_constr (tuple_def))
with | None => fail | Some pr => get_projs_in_variables pr end) in function tuple_def.