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

Ltac2 scope_verbos v := orchestrator 5
[(trigger_anonymous_funs, "my_anonymous_functions", trivial_filter) ;
(trigger_higher_order, "my_higher_order", trivial_filter) ; 
(trigger_reflexivity (), "my_reflexivity", filter_reflexivity ());
(trigger_unfold_reflexivity (), "my_unfold_refl", trivial_filter) ;
(trigger_higher_order_equalities, "my_higher_order_equalities", trivial_filter); 
(trigger_fixpoints, "my_fixpoints", trivial_filter);
(trigger_pattern_matching, "my_pattern_matching",  trivial_filter);
(trigger_algebraic_types, "my_algebraic_types", filter_algebraic_types ());
(trigger_generation_principle, "my_gen_principle_temporary", trivial_filter) ;
(trigger_polymorphism (), "my_polymorphism_elpi", trivial_filter) ;
(trigger_add_compdecs (), "my_add_compdec",  filter_add_compdecs ())]
{ already_triggered := [] } v.

Ltac2 scope () := scope_verbos Nothing.

Ltac2 scope_info () := scope_verbos Info.

Ltac2 scope_debug () := scope_verbos Debug.

Ltac2 scope_full () := scope_verbos Full.

Ltac2 scope2_verbos v := orchestrator 5
[(trigger_anonymous_funs, "my_anonymous_functions", trivial_filter) ;
(trigger_higher_order, "my_higher_order", trivial_filter) ; 
(trigger_reflexivity (), "my_reflexivity", filter_reflexivity ());
(trigger_unfold_reflexivity (), "my_unfold_refl", trivial_filter);
(trigger_higher_order_equalities, "my_higher_order_equalities", trivial_filter); 
(trigger_fixpoints, "my_fixpoints", trivial_filter);
(trigger_pattern_matching, "my_pattern_matching",  trivial_filter);
(trigger_algebraic_types, "my_algebraic_types", filter_algebraic_types ());
(trigger_generation_principle, "my_gen_principle_temporary", trivial_filter) ;
(trigger_polymorphism (), "my_polymorphism_elpi", trivial_filter) ;
(trigger_add_compdecs (), "my_add_compdec",  filter_add_compdecs ())]
{ already_triggered := [] } v.

Ltac2 scope2 () := scope_verbos Nothing.

Ltac2 scope2_info () := scope_verbos Info.

Ltac2 scope2_debug () := scope_verbos Debug.

Ltac2 scope2_full () := scope_verbos Full.

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
