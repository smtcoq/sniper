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

Ltac my_unfold_in H t := unfold_in H t.

(* Ltac my_trakt_bool := revert_all ; trakt bool ; intros.  *)

Ltac my_higher_order_equalities H := expand_hyp H ; clear H.

Ltac my_higher_order := prenex_higher_order.

Ltac my_fixpoints H := eliminate_fix_hyp H.

Ltac my_pattern_matching H := try (eliminate_dependent_pattern_matching H).

Ltac my_anonymous_functions := anonymous_funs. (* TODO : wrong trigger, avoid higher order equalities (= priorities ??) *)

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
{ all_tacs := [((trigger_anonymous_funs, false), "my_anonymous_functions", trivial_filter) ;
((trigger_higher_order, false), "my_higher_order", trivial_filter) ; 
((trigger_reflexivity (), false), "my_reflexivity", filter_reflexivity ());
((trigger_unfold_reflexivity (), false), "my_unfold_refl", trivial_filter);
((trigger_unfold_in (), false), "my_unfold_in", trivial_filter);
((trigger_higher_order_equalities, false), "my_higher_order_equalities", trivial_filter); 
((trigger_fixpoints, false), "my_fixpoints", trivial_filter);
((trigger_pattern_matching, false), "my_pattern_matching",  trivial_filter);
((trigger_algebraic_types, false), "my_algebraic_types", filter_algebraic_types ());
((trigger_generation_principle, false), "my_gen_principle_temporary", trivial_filter) ;
((trigger_fold_local_def_in_hyp (), false), "my_fold_local_def_in_hyp_goal", trivial_filter)
(* ((trigger_polymorphism (), true), "my_polymorphism_elpi", trivial_filter) ; *)
(* ((trigger_add_compdecs (), false), "my_add_compdec",  filter_add_compdecs ())]  *) ] }
{ already_triggered := [] } v.

Ltac2 scope () := scope_verbos Nothing.

Ltac2 scope_info () := scope_verbos Info.

Ltac2 scope_debug () := scope_verbos Debug.

Ltac2 scope_full () := scope_verbos Full.

Ltac2 scope2_verbos v := orchestrator 5
{ all_tacs := 
[((trigger_anonymous_funs, false), "my_anonymous_functions", trivial_filter) ;
((trigger_higher_order, false), "my_higher_order", trivial_filter) ; 
((trigger_reflexivity (), false), "my_reflexivity", filter_reflexivity ());
((trigger_unfold_reflexivity (), false), "my_unfold_refl", trivial_filter);
((trigger_higher_order_equalities, false), "my_higher_order_equalities", trivial_filter); 
((trigger_fixpoints, false), "my_fixpoints", trivial_filter);
((trigger_pattern_matching, false), "my_pattern_matching",  trivial_filter);
((trigger_algebraic_types, false), "my_algebraic_types", filter_algebraic_types ());
((trigger_generation_principle, false), "my_gen_principle_temporary", trivial_filter) ;
((trigger_fold_local_def_in_hyp (), false), "my_fold_local_def_in_hyp_goal", trivial_filter);
((trigger_polymorphism (), false), "my_polymorphism", trivial_filter) ]
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

Set Default Proof Mode "Classic".

Section test.

Variable (A B C : Type).

Lemma map_compound : forall (f : A -> B) (g : B -> C) (l : list A), 
map g (map f l) = map (fun x => g (f x)) l.
Proof.
Time induction l.
- ltac2:(scope_info ()). unfold_in H f1.
 Focus 2. fold elpi_ctx_entry_31_.
fold elpi_ctx_entry_30_.   Qed.


