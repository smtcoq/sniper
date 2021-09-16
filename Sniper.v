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

From MetaCoq Require Export All.
Require Export MetaCoq.Template.All.
Require Export MetaCoq.Template.Universes.
Require Export MetaCoq.PCUIC.PCUICSubstitution.
Require Export MetaCoq.Template.All.
Require Export String.
Require Export List.
Require Export ZArith.
Require Export utilities.
Require Export definitions.
Require Export elimination_fixpoints.
Require Export expand.
Require Export elimination_pattern_matching. 
Require Export elimination_polymorphism.
Require Export interpretation_algebraic_types.



Ltac def_and_pattern_matching := 
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_dependent_pattern_matching H')).


Ltac def_fix_and_pattern_matching :=
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun H'' =>
try (eliminate_dependent_pattern_matching H'')))).


Ltac def_and_pattern_matching_mono :=
def_and_pattern_matching ; inst_clear.

Ltac def_and_pattern_matching_mono_param t :=
def_and_pattern_matching ; instanciate_type_tuple t ; specialize_context_clear.
Ltac def_fix_and_pattern_matching_mono_param t :=
def_fix_and_pattern_matching ; instanciate_type_tuple t ; specialize_context_clear.



Ltac scope_param t :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t ; try nat_convert).
(* besoin de nat_convert parce que sinon, on risque de déplier des définitions et ajouter des 
hypothèses dans nat et ensuite verit se met à peiner *)

Ltac scope_no_param :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst_clear ; try nat_convert).

Ltac scope_param_no_nat_convert t :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t).
(* besoin de nat_convert parce que sinon, on risque de déplier des définitions et ajouter des 
hypothèses dans nat et ensuite verit se met à peiner *)

Ltac scope_no_param_no_nat_convert :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst_clear).

Ltac snipe_param t := 
scope_param t ; verit.

Ltac snipe_no_param := 
scope_no_param ; verit.

Ltac snipe_param_no_nat t :=
scope_param_no_nat_convert t ; verit.

Ltac snipe_no_param_no_nat :=
scope_no_param_no_nat_convert ; verit.

Tactic Notation "snipe_no_nat" constr(t) := snipe_param_no_nat t.
Tactic Notation "snipe_no_nat" := snipe_no_param_no_nat.

Tactic Notation "scope" constr(t) := scope_param t.
Tactic Notation "scope" := scope_no_param.

Tactic Notation "snipe" constr(t) := snipe_param t.
Tactic Notation "snipe" := snipe_no_param.
