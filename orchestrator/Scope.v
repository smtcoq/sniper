From Ltac2 Require Import Ltac2.
From Trakt Require Import Trakt.

From Sniper Require Import definitions.
From Sniper Require Import expand.
From Sniper Require Import elimination_fixpoints.
From Sniper Require Import elimination_pattern_matching.
From Sniper Require Import interpretation_algebraic_types.
From Sniper Require Import case_analysis.
From Sniper Require Import higher_order.
From Sniper Require Import anonymous_functions.
From Sniper Require Import instantiate.

Require Import Tactics.
Require Import Triggers.
Require Import Printer.
Require Import Orchestrator.

Set Default Proof Mode "Classic".

Ltac2 trigger_polymorphism () :=
 TDisj (TIs (TSomeHyp, NotArg)  (TProd (TSort TSet NotArg) tDiscard NotArg)) (TIs (TSomeHyp, NotArg) (TProd (TSort TBigType NotArg) tDiscard NotArg)).

Ltac2 scope_triggers () := 
  [trigger_trakt_bool ();
   trigger_definitions; 
   trigger_higher_order_equalities;
   trigger_fixpoints;
   trigger_pattern_matching;
   trigger_higher_order;
   trigger_anonymous_funs ();
   trigger_algebraic_types;
   trigger_generation_principle;
   trigger_polymorphism ()].

Ltac my_get_def t := get_def t.

(* Ltac my_trakt_bool := trakt bool. *)

Ltac my_higher_order_equalities H := expand_hyp H ; clear H.

Ltac my_fixpoints H := eliminate_fix_hyp H.

Ltac my_pattern_matching H := eliminate_dependent_pattern_matching H.

(* Ltac my_anonymous_functions := anonymous_funs. *)

Ltac my_algebraic_types t := try (interp_alg_types t).

Ltac my_gen_principle t := pose_gen_statement t.

Ltac my_polymorphism := elimination_polymorphism.

(* [(* "my_trakt_bool"; TODO *) "my_get_def"; 
"my_higher_order_equalities"; "my_fixpoints" ; "my_pattern_matching"; (* "my_anonymous_functions"; *)
"my_algebaraic_types"; "my_gen_principle"; "my_polymorphism"] *)


Ltac2 scope () := orchestrator 10 [trigger_definitions; trigger_higher_order_equalities; 
trigger_fixpoints; trigger_pattern_matching; trigger_algebraic_types; trigger_polymorphism ()] ["my_get_def"; "my_higher_order_equalities"; "my_fixpoints";
"my_pattern_matching"; "my_algebraic_types"; "my_polymorphism"] { triggered_tacs := [] }.

Tactic Notation "scope" := ltac2:(scope ()).

Lemma toto A : length (@nil A) = 0.
Proof.
Time scope.








   