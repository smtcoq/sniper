From Ltac2 Require Import Ltac2.

Require Import ZArith.
Require Import PArith.BinPos.
Require Import NArith.BinNatDef.

From SMTCoq Require Import SMT_classes SMT_classes_instances BVList FArray.

From Trakt Require Import Trakt.

From Sniper Require Import Transfos.

Require Import triggers_tactics.
Require Import triggers.
Require Import printer.
Require Import orchestrator.
Require Import filters.

Set Default Proof Mode "Classic".

Ltac revert_all :=
repeat match goal with
| H : _ |- _ => try revert H
end.

Ltac my_reflexivity t := assert_refl t.

Ltac my_unfold_refl H := unfold_refl H.

(* Ltac my_trakt_bool := revert_all ; trakt bool ; intros.  *)

Ltac my_higher_order_equalities H := expand_hyp H ; clear H.

Ltac my_higher_order := prenex_higher_order_with_equations.

Ltac my_fixpoints H := eliminate_fix_hyp H.

Ltac my_pattern_matching H := try (eliminate_dependent_pattern_matching H).

Ltac my_anonymous_functions := anonymous_funs. (* TODO : wrong trigger, avoid higher order equalities (= priorities ??) *)

Ltac my_algebraic_types t := try (interp_alg_types t).

Ltac my_gen_principle t := 
 pose_gen_statement t.

Definition prod_types := (Z, bool, True, False, positive, N, and, or, nat, Init.Peano.le,
@CompDec, Comparable, EqbType, Inhabited, OrderedType.Compare).

Ltac my_gen_principle_temporary := ltac2:(get_projs_in_variables 'prod_types).

Ltac my_polymorphism_elpi := elimination_polymorphism.

Ltac my_polymorphism := elimination_polymorphism_exhaustive unit. 

Ltac my_add_compdec t := add_compdecs_terms t.

Ltac2 trigger_generation_principle := TOneTime.

Ltac2 trigger_anonymous_funs := TOneTime.

Ltac2 trigger_higher_order :=
  TOneTime.

Ltac2 scope () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs, trivial_filter) ;
("my_higher_order", trigger_higher_order, trivial_filter) ; 
("my_reflexivity", trigger_reflexivity (), filter_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity (), trivial_filter);
("my_higher_order_equalities", trigger_higher_order_equalities, trivial_filter); 
("my_fixpoints", trigger_fixpoints, trivial_filter);
("my_pattern_matching", trigger_pattern_matching, trivial_filter);
("my_algebraic_types", trigger_algebraic_types, filter_algebraic_types ());
("my_gen_principle_temporary", trigger_generation_principle, trivial_filter) ;
("my_polymorphism_elpi", trigger_polymorphism (), trivial_filter) ;
("my_add_compdec", trigger_add_compdecs (), filter_add_compdecs ())] }
{ triggered_tacs := [] } {old_types_and_defs  := [] } Nothing.

Ltac2 scope_debug () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs, trivial_filter) ;
("my_higher_order", trigger_higher_order, trivial_filter) ; 
("my_reflexivity", trigger_reflexivity (), filter_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity (), trivial_filter);
("my_higher_order_equalities", trigger_higher_order_equalities, trivial_filter); 
("my_fixpoints", trigger_fixpoints, trivial_filter);
("my_pattern_matching", trigger_pattern_matching, trivial_filter);
("my_algebraic_types", trigger_algebraic_types, filter_algebraic_types ());
("my_gen_principle_temporary", trigger_generation_principle, (* filter_generation_principle () *) trivial_filter) ;
("my_polymorphism_elpi", trigger_polymorphism (), trivial_filter) ;
("my_add_compdec", trigger_add_compdecs (), filter_add_compdecs ())] }
{ triggered_tacs := [] } {old_types_and_defs  := [] } Debug.

Ltac2 scope_full () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs, trivial_filter) ;
("my_higher_order", trigger_higher_order, trivial_filter) ; 
("my_reflexivity", trigger_reflexivity (), filter_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity (), trivial_filter);
("my_higher_order_equalities", trigger_higher_order_equalities, trivial_filter); 
("my_fixpoints", trigger_fixpoints, trivial_filter);
("my_pattern_matching", trigger_pattern_matching, trivial_filter);
("my_algebraic_types", trigger_algebraic_types, filter_algebraic_types ());
("my_gen_principle_temporary", trigger_generation_principle, (* filter_generation_principle () *) trivial_filter) ;
("my_polymorphism_elpi", trigger_polymorphism (), trivial_filter) ;
("my_add_compdec", trigger_add_compdecs (), filter_add_compdecs ())] }
{ triggered_tacs := [] } {old_types_and_defs  := [] } Full.

Ltac2 scope2 () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs, trivial_filter) ;
("my_higher_order", trigger_higher_order, trivial_filter) ; 
("my_reflexivity", trigger_reflexivity (), filter_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity (), trivial_filter);
("my_higher_order_equalities", trigger_higher_order_equalities, trivial_filter); 
("my_fixpoints", trigger_fixpoints, trivial_filter);
("my_pattern_matching", trigger_pattern_matching, trivial_filter);
("my_algebraic_types", trigger_algebraic_types, filter_algebraic_types ());
("my_gen_principle_temporary", trigger_generation_principle, (* filter_generation_principle () *) trivial_filter) ;
("my_polymorphism", trigger_polymorphism (), trivial_filter) ;
("my_add_compdec", trigger_add_compdecs (), filter_add_compdecs ())] }
{ triggered_tacs := [] } { old_types_and_defs  := [] } Nothing.

Tactic Notation "scope" := ltac2:(scope ()).

Tactic Notation "scope_debug" := ltac2:(scope_debug ()).

Tactic Notation "scope_full" := ltac2:(scope_full ()).

Tactic Notation "scope" := ltac2:(Control.enter (fun () => scope ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => scope2 ())).

Tactic Notation "scope" := ltac2:(Control.enter (fun () => intros; scope ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => intros ; scope2 ())).

Tactic Notation "snipe_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe2_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe" :=
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit))).

Tactic Notation "snipe2" :=
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit))).