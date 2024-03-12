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

Local Open Scope bs_scope.

Ltac revert_all :=
repeat match goal with
| H : _ |- _ => try revert H
end.

Ltac my_reflexivity t := assert_refl t.

Ltac my_unfold_refl H := unfold_refl H.

Ltac my_unfold_in H t := unfold_in H t.

(* Ltac my_trakt_bool := revert_all ; trakt bool ; intros.  *)

Ltac my_higher_order_equalities H := expand_hyp H ; clear H.

Ltac my_higher_order := prenex_higher_order.

Ltac my_fixpoints H := eliminate_fix_hyp H.

Ltac my_pattern_matching H := try (eliminate_dependent_pattern_matching H).

Ltac my_anonymous_functions := anonymous_funs.

Ltac my_algebraic_types t := try (interp_alg_types t).

Ltac my_gen_principle t := 
 pose_gen_statement t.

Ltac my_gen_principle_temporary := ltac2:(get_projs_in_variables '(Z, bool, True, False, positive, N, and, or, nat, Init.Peano.le,
@CompDec, Comparable, EqbType, Inhabited, OrderedType.Compare)).

Ltac my_polymorphism_elpi := elimination_polymorphism.

Ltac my_polymorphism := elimination_polymorphism_exhaustive unit. 

Ltac my_add_compdec t := add_compdecs_terms t.

Ltac my_fold_local_def_in_hyp_goal H t := fold_local_def_in_hyp_goal H t.

Ltac2 trigger_generation_principle := TAlways.

Ltac2 trigger_anonymous_funs := TAlways.

Ltac2 trigger_higher_order :=
  TAlways.

Ltac2 scope_verbos v := orchestrator 5
{ all_tacs := [((trigger_anonymous_funs, false, None), "my_anonymous_functions", trivial_filter);
((trigger_higher_order, false, None), "my_higher_order", trivial_filter) ; 
((trigger_reflexivity (), false, None), "my_reflexivity", filter_reflexivity ());
((trigger_unfold_reflexivity (), false, None), "my_unfold_refl",  filter_unfold_reflexivity ());
((trigger_unfold_in (), false, None), "my_unfold_in", filter_unfold_in ());
((trigger_higher_order_equalities, false, None), "my_higher_order_equalities", trivial_filter) ;
((trigger_fixpoints, false, None), "my_fixpoints", trivial_filter) ;
((trigger_pattern_matching, false, None), "my_pattern_matching",  trivial_filter);
((trigger_algebraic_types, false, None), "my_algebraic_types", filter_algebraic_types ()) ;
((trigger_generation_principle, false, None), "my_gen_principle_temporary", trivial_filter) ; 
((trigger_polymorphism (), true, None), "my_polymorphism_elpi", trivial_filter) ;
((trigger_fold_local_def_in_hyp (), false, None), "my_fold_local_def_in_hyp_goal", trivial_filter);
((trigger_add_compdecs (), false, Some (2, 2)), "my_add_compdec",  filter_add_compdecs ()) ]}
{ already_triggered := [] } v.

Ltac2 scope () := scope_verbos Nothing.

Ltac2 scope_info () := scope_verbos Info.

Ltac2 scope_debug () := scope_verbos Debug.

Ltac2 scope_full () := scope_verbos Full.

Ltac2 scope2_verbos v := orchestrator 5
{ all_tacs := 
[((trigger_anonymous_funs, false, None), "my_anonymous_functions", trivial_filter) ;
((trigger_higher_order, false, None), "my_higher_order", trivial_filter) ; 
((trigger_reflexivity (), false, None), "my_reflexivity", filter_reflexivity ());
((trigger_unfold_reflexivity (), false, None), "my_unfold_refl", trivial_filter);
((trigger_higher_order_equalities, false, None), "my_higher_order_equalities", trivial_filter); 
((trigger_fixpoints, false, None), "my_fixpoints", trivial_filter);
((trigger_pattern_matching, false, None), "my_pattern_matching",  trivial_filter);
((trigger_algebraic_types, false, None), "my_algebraic_types", filter_algebraic_types ());
((trigger_generation_principle, false, None), "my_gen_principle_temporary", trivial_filter) ;
((trigger_fold_local_def_in_hyp (), false, None), "my_fold_local_def_in_hyp_goal", trivial_filter);
((trigger_polymorphism (), false, Some (2, 2)), "my_polymorphism", trivial_filter) ]
(* ((trigger_add_compdecs (), false), "my_add_compdec",  filter_add_compdecs ())] *) }
{ already_triggered := [] } v.

Ltac2 scope2 () := scope2_verbos Nothing.

Ltac2 scope2_info () := scope2_verbos Info.

Ltac2 scope2_debug () := scope2_verbos Debug.

Ltac2 scope2_full () := scope2_verbos Full.

Tactic Notation "scope" := ltac2:(Control.enter (fun () => intros; scope ())).

Tactic Notation "scope_info" := ltac2:(Control.enter (fun () => intros; scope_info ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => intros ; scope2 ())).

Tactic Notation "snipe_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe2_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe" :=
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit))).

Tactic Notation "snipe2" :=
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit))).




