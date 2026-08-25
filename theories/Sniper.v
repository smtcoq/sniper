From SMTCoq Require Export SMTCoq.

From Ltac2 Require Import Ltac2.

From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Import NArith.BinNatDef.

From SMTCoq Require Import CompDec CompDecInstances BVList FArray.

From Trakt Require Import Trakt.

From Sniper Require Import Transfos.

Require Export triggers_tactics.
Require Import run_tactic.
Require Export triggers.
Require Import printer.
Require Import orchestrator.
Require Export filters.

Require Import tree.

Local Open Scope bs_scope.

Ltac revert_all :=
repeat match goal with
| H : _ |- _ => try revert H
end.

Ltac tactic_reflexivity t := assert_refl t.
Ltac2 transfo_reflexivity () :=
  ((trigger_reflexivity (), false, None), "tactic_reflexivity", filter_reflexivity (),
    "State reflexivity of a constant",
    "Given a term `t`, this transformation states the hypothesis `t = t`. This is the first step to give semantics to constants, in combination with other transformations that will further transform the right hand side of the equality."
  ).

Ltac tactic_unfold_refl H := unfold_refl H.
Ltac2 transfo_unfold_refl () :=
  ((trigger_unfold_reflexivity (), false, None), "tactic_unfold_refl", filter_unfold_reflexivity (),
    "Unfolds the right hand side of an equality of the shape `x = x`",
    "Given an hypothesis `H : x = x`, unfolds the right hand side of the equality. This is part of the transformations that give semantics to constants."
  ).
(* TODO: probably a mistake to use the trivial filter? *)
Ltac2 transfo_unfold_refl2 () :=
  ((trigger_unfold_reflexivity (), false, None), "tactic_unfold_refl", trivial_filter,
    "Unfolds the right hand side of an equality of the shape `x = x`",
    "Given an hypothesis `H : x = x`, unfolds the right hand side of the equality. This is part of the transformations that give semantics to constants."
  ).

Ltac tactic_unfold_in H t := unfold_in H t.
Ltac2 transfo_unfold_in () :=
  ((trigger_unfold_in (), false, None), "tactic_unfold_in", filter_unfold_in (),
    "Unfolds a term in an hypothesis",
    "Given an hypothesis H and a term t, unfold t in H; H must be an equality whose right hand side contains t. This is part of the transformations that give semantics to constants."
  ).

(* Ltac my_trakt_bool := revert_all ; trakt bool ; intros.  *)

Ltac tactic_higher_order_equalities H := expand_hyp H ; clear H.
Ltac2 transfo_higher_order_equalities () :=
  ((trigger_higher_order_equalities, false, None), "tactic_higher_order_equalities", trivial_filter,
    "Eta expands a higher order equality",
    "Given an hypothesis H of the form `a = b` where `a` (and `b`) have a function types, eta expands it by adding prenex quantification."
  ).

Ltac tactic_higher_order := prenex_higher_order.
Ltac2 transfo_higher_order () :=
  ((TAlways, false, None), "tactic_higher_order", trivial_filter,
    "Give a name to an applied higher order function",
    "If an hypothesis contains an applied higher order function, gives a name to the first order part of this application"
  ).

Ltac tactic_fixpoints H := eliminate_fix_hyp H.
Ltac2 transfo_fixpoints () :=
  ((trigger_fixpoints, false, None), "tactic_fixpoints", trivial_filter,
    "Eliminate a fixpoint in a given hypothesis",
    "Given an hypothesis `H : A` where `A` cointains an anonymous fixpoint, replaces this anonymous fixpoint by the constant that defines it."
  ).

Ltac tactic_pattern_matching H := try (eliminate_dependent_pattern_matching H).
Ltac2 transfo_pattern_matching () :=
  ((trigger_pattern_matching, false, None), "tactic_pattern_matching",  trivial_filter,
    "Eliminate pattern matching in a given hypothesis",
    "Given an hypothesis `H : A` where `A` cointains an pattern matching, splits H into one hypothesis per branch."
  ).

Ltac tactic_anonymous_function f := anonymous_fun f.
Ltac2 transfo_anonymous_function () :=
  ((trigger_anonymous_fun (), false, None), "tactic_anonymous_function", trivial_filter,
    "Give a name to a given anonymous function",
    "Given an anonymous function `f`, give a name to it and use the name everywhere instead of the function."
  ).

Ltac tactic_algebraic_types t := try (interp_alg_types t).
Ltac2 transfo_algebraic_types () :=
  ((trigger_algebraic_types, false, None), "tactic_algebraic_types", filter_algebraic_types (),
    "Gives (part of the) semantics to a given algebraic type",
    "Given an algebraic type `t`, states (1) that constructors are pairwise disjoint and (2) that constructors are injective."
  ).

(* Ltac tactic_gen_principle t := *)
(*  pose_gen_statement t. *)

Ltac tactic_gen_principle_experimental :=
  ltac2:(get_projs_in_variables (filter_inductive_types ())).
Ltac2 transfo_gen_principle_experimental () :=
  ((TAlways, false, None), "tactic_gen_principle_experimental", trivial_filter,
    "Generates generation principle of algebraic types. Experimental",
    "This experimental tactic generates the generation principles of algebraic types that are present in the goal or the context. To avoid existential quantifiers, the shape of these principles involves projections which are also generated by the tactic (using default values from CompDec)."
  ).

Ltac tactic_polymorphism_state :=
  ltac2:(Notations.do0 max_quantifiers elimination_polymorphism) ;
    clear_prenex_poly_hyps_in_context.
Ltac2 transfo_polymorphism_state () :=
  ((trigger_polymorphism (), true, None), "tactic_polymorphism_state", trivial_filter,
    "Locally monomorphizes the context",
    "This transformation monomorphizes the current state of the orchestrator. It is based on a strategy that generates only the instances in which polymorphic inductive types are applied only to types for which they are already applied elsewhere in the context."
  ).

Ltac tactic_polymorphism := elimination_polymorphism_exhaustive unit.
Ltac2 transfo_polymorphism () :=
  ((trigger_polymorphism (), false, Some (2, 2)), "tactic_polymorphism", trivial_filter,
    "Globally monomorphizes the context",
    "This gobal transformation eagerly monomorphizes the context by applying universally quantified hypotheses to every concrete type present in the goal or the context."
  ).

Ltac tactic_add_compdecs t := add_compdecs_terms t.
Ltac2 transfo_add_compdecs () :=
  ((trigger_add_compdecs (), false, Some (2, 2)), "tactic_add_compdecs",  filter_add_compdecs (),
    "Adds the hypothesis `CompDec t` of a given term `t`",
    "Given a term `t`, this tranformation adds the hypothesis `CompDec t`."
  ).
(* TODO: probably a mistake not to look at the second goal only? *)
Ltac2 transfo_add_compdecs2 () :=
  ((trigger_add_compdecs (), false, None), "tactic_add_compdecs",  filter_add_compdecs (),
    "Adds the hypothesis `CompDec t` of a given term `t`",
    "Given a term `t`, this tranformation adds the hypothesis `CompDec t`."
  ).

Ltac tactic_fold_local_def_in_hyp_goal H t := fold_local_def_in_hyp_goal H t.
Ltac2 transfo_fold_local_def_in_hyp_goal () :=
  ((trigger_fold_local_def_in_hyp (), false, None), "tactic_fold_local_def_in_hyp_goal", trivial_filter,
    "Given an hypothesis and a term, folds the term in the hypothesis",
    "Given an hypothesis `H` and a term `t`, folds the term in the hypothesis"
  ).

Ltac tactic_pose_case := pose_case.
Ltac2 transfo_pose_case () :=
  ((trigger_pose_case (), false, None), "tactic_pose_case", trivial_filter,
    "Replaces a pattern matching in a goal by a local constant",
    "If the goal contains a pattern matching, it is replaced by a new constant. This allows us to avoid an explosion of goals containing pattern matching."
  ).


Ltac2 mutable sniper_transformations () :=
  [
    transfo_pose_case ();
    transfo_anonymous_function ();
    transfo_higher_order ();
    transfo_reflexivity ();
    transfo_unfold_refl ();
    transfo_unfold_in ();
    transfo_higher_order_equalities ();
    transfo_fixpoints ();
    transfo_pattern_matching ();
    transfo_algebraic_types ();
    transfo_gen_principle_experimental ();
    transfo_polymorphism_state ();
    transfo_fold_local_def_in_hyp_goal ();
    transfo_add_compdecs ()
  ].
(* To add a new transformation `my_transfo`:

     Ltac2 Set sniper_transformations as st := fun () =>
       ((trigger_my_transfo (), is_global, continue_on_subgoals), "my_transfo", filter_my_transfo ())::(st ()).

   - `trigger_my_transfo` is what triggers the transformation

   - `is_global` is a boolean stating if the transformation acts on the
     whole goal or on a single hypothesis or on the conclusion

   - `continue_on_subgoals`, of type `option (int * int)`, states on
     which subgoals to continue the transformations, if the tactic may
     produce multiple subgoals; for example:

     + if set to `None`, the transformations will continue on all the
       generated goals

     + if set to `Some (2, 4)`, the transformations will continue on
       subgoals 2 to 4 inclusive, starting at 1, if it produces at least
       4 subgoals; otherwise it will continue on all subgoals

   - `"my_transfo"` is the name of the transformation, which must be an
     Ltac tactic

   - `filter_my_transfo` contains particular cases for which the
     transformation may be triggered while we do not want to

   - `"Short description"` is a short description of the transformation

   - `"Long description"` is a long description of the transformation
 *)

Ltac2 scope_verbos v := orchestrator 0 5 { all_tacs := sniper_transformations ()} { already_triggered := [] } v.

Ltac2 scope () := scope_verbos Nothing.

Ltac2 scope_info () := scope_verbos Info.

Ltac2 scope_debug () := scope_verbos Debug.

Ltac2 scope_full () := scope_verbos Full.

Ltac2 scope2_verbos v := orchestrator 0 5
  { all_tacs :=
      [
        transfo_pose_case ();
        transfo_anonymous_function ();
        transfo_higher_order ();
        transfo_reflexivity ();
        transfo_unfold_refl2 ();
        transfo_higher_order_equalities ();
        transfo_fixpoints ();
        transfo_pattern_matching ();
        transfo_algebraic_types ();
        transfo_gen_principle_experimental ();
        transfo_fold_local_def_in_hyp_goal ();
        transfo_polymorphism ();
        transfo_add_compdecs2 ()
      ]
  }
  { already_triggered := [] } v.

Ltac2 scope2 () := scope2_verbos Nothing.

Ltac2 scope2_info () := scope2_verbos Info.

Ltac2 scope2_debug () := scope2_verbos Debug.

Ltac2 scope2_full () := scope2_verbos Full.

Tactic Notation "scope" := ltac2:(Control.enter (fun () => intros; scope ())).

Tactic Notation "scope_info" := ltac2:(Control.enter (fun () => intros; scope_info ())).

Tactic Notation "scope_full" := ltac2:(Control.enter (fun () => intros; scope_full ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => intros ; scope2 ())).

Tactic Notation "snipe_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit_no_check_nocompdecs))).

Tactic Notation "snipe2_no_check" := 
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit_no_check_nocompdecs))).

Tactic Notation "snipe" :=
  ltac2:(Control.enter (fun () => intros; scope (); ltac1:(verit_nocompdecs))).

Tactic Notation "snipe2" :=
  ltac2:(Control.enter (fun () => intros; scope2 (); ltac1:(verit_nocompdecs))).
