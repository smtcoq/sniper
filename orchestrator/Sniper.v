From Ltac2 Require Import Ltac2.

Require Import ZArith.
Require Import PArith.BinPos.
Require Import NArith.BinNatDef.

From SMTCoq Require Import SMT_classes SMT_classes_instances BVList FArray.

From Sniper Require Import Transfos.

Require Import triggers_tactics.
Require Import triggers.
Require Import printer.
Require Import orchestrator.

Set Default Proof Mode "Classic".

From Ltac2 Require Import Printf.

Ltac2 init_triggered ():=
[("my_reflexivity", [constr:(Z.add)]);
("my_reflexivity", [constr:(Z.sub)]);
("my_reflexivity", [constr:(Z.mul)]);
("my_reflexivity", [constr:(Z.eqb)]);
("my_reflexivity", [constr:(Z.ltb)]);
("my_reflexivity", [constr:(Z.leb)]);
("my_reflexivity", [constr:(Z.geb)]);
("my_reflexivity", [constr:(Z.gtb)]);
("my_reflexivity", [constr:(Z.lt)]);
("my_reflexivity", [constr:(Z.le)]);
("my_reflexivity", [constr:(Z.ge)]);
("my_reflexivity", [constr:(Z.gt)]);
("my_reflexivity", [constr:(Pos.lt)]);
("my_reflexivity", [constr:(Pos.le)]);
("my_reflexivity", [constr:(Pos.ge)]);
("my_reflexivity", [constr:(Pos.gt)]);
("my_reflexivity", [constr:(Z.to_nat)]);
("my_reflexivity", [constr:(Pos.mul)]);
("my_reflexivity", [constr:(Pos.add)]);
("my_reflexivity", [constr:(Pos.sub)]);
("my_reflexivity", [constr:(Init.Nat.add)]);
("my_reflexivity", [constr:(Init.Nat.mul)]);
("my_reflexivity", [constr:(Nat.eqb)]);
("my_reflexivity", [constr:(Nat.leb)]);
("my_reflexivity", [constr:(Nat.ltb)]);
("my_reflexivity", [constr:(Peano.lt)]);
("my_reflexivity", [constr:(ge)]); 
("my_reflexivity", [constr:(gt)]);
("my_reflexivity", [constr:(N.add)]);
("my_reflexivity", [constr:(N.mul)]);
("my_reflexivity", [constr:(N.eqb)]);
("my_reflexivity", [constr:(N.leb)]);
("my_reflexivity", [constr:(N.ltb)]);
("my_reflexivity", [constr:(Peano.lt)]);
("my_reflexivity", [constr:(ge)]); 
("my_reflexivity", [constr:(gt)]);
("my_reflexivity", [constr:(negb)]);
("my_reflexivity", [constr:(not)]);
("my_reflexivity", [constr:(andb)]);
("my_reflexivity", [constr:(orb)]);
("my_reflexivity", [constr:(implb)]);
("my_reflexivity", [constr:(xorb)]);
("my_reflexivity", [constr:(Bool.eqb)]);
("my_reflexivity", [constr:(iff)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_eq)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_and)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_or)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_xor)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_add)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_mult)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_ult)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_slt)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_concat)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_shl)]);
("my_reflexivity", [constr:(BITVECTOR_LIST.bv_shr)]);
("my_reflexivity", [constr:(@FArray.select)]);
("my_reflexivity", [constr:(@FArray.diff)]);
("my_reflexivity", [constr:(is_true)]);
("my_reflexivity", [constr:(@eqb_of_compdec)]);
("my_reflexivity", [constr:(CompDec)]);
("my_reflexivity", [constr:(Nat_compdec)]);
("my_reflexivity", [constr:(list_compdec)]);
("my_reflexivity", [constr:(prod_compdec)]);
("my_reflexivity", [constr:(Z_compdec)]);
("my_algebraic_types", [constr:(Z)]);
("my_algebraic_types", [constr:(bool)]);
("my_algebraic_types", [constr:(positive)]);
("my_algebraic_types", [constr:(N)]);
("my_algebraic_types", [constr:(nat)]);
("my_algebraic_types", [constr:(EqbType)]);
("my_algebraic_types", [constr:(@CompDec)]);
("my_algebraic_types", [constr:(Comparable)]);
("my_algebraic_types", [constr:(Inhabited)]);
("my_algebraic_types", [constr:(OrderedType.Compare)]);
("my_gen_principle", [constr:(Z)]);
("my_gen_principle", [constr:(bool)]);
("my_gen_principle", [constr:(positive)]);
("my_gen_principle", [constr:(N)]);
("my_gen_principle", [constr:(nat)]);
("my_gen_principle", [constr:(EqbType)]);
("my_gen_principle", [constr:(@CompDec)]);
("my_gen_principle", [constr:(Comparable)]);
("my_gen_principle", [constr:(Inhabited)]);
("my_gen_principle", [constr:(OrderedType.Compare)]);
("my_add_compdec", [constr:(FArray.farray)]);
("my_add_compdec", [constr:(Z)]);
("my_add_compdec", [constr:(nat)]);
("my_add_compdec", [constr:(positive)]);
("my_add_compdec", [constr:(bool)])
].

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

Ltac my_polymorphism := inst.

Ltac my_add_compdec t := add_compdecs_terms t.

Ltac2 trigger_generation_principle := TOneTime.

Ltac2 trigger_anonymous_funs := TOneTime.


Ltac2 trigger_higher_order :=
  TOneTime.


Ltac2 scope () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs) ;
("my_higher_order", trigger_higher_order) ; 
("my_reflexivity", trigger_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity ()) ;
("my_higher_order_equalities", trigger_higher_order_equalities); 
("my_fixpoints", trigger_fixpoints);
("my_pattern_matching", trigger_pattern_matching);
("my_algebraic_types", trigger_algebraic_types);
("my_gen_principle_temporary", trigger_generation_principle) ;
("my_polymorphism_elpi", trigger_polymorphism ()) ;
("my_add_compdec", trigger_add_compdecs ())] }
{ triggered_tacs := (init_triggered ()) } {old_types_and_defs  := [] } Nothing.

Ltac2 scope2 () := orchestrator 5
{ all_tacs := 
[
("my_anonymous_functions", trigger_anonymous_funs) ;
("my_higher_order", trigger_higher_order) ; 
("my_reflexivity", trigger_reflexivity ());
("my_unfold_refl", trigger_unfold_reflexivity ()) ;
("my_higher_order_equalities", trigger_higher_order_equalities); 
("my_fixpoints", trigger_fixpoints);
("my_pattern_matching", trigger_pattern_matching);
("my_algebraic_types", trigger_algebraic_types);
("my_gen_principle_temporary", trigger_generation_principle) ;
("my_polymorphism", trigger_polymorphism ()) ;
("my_add_compdec", trigger_add_compdecs ())] }
{ triggered_tacs := (init_triggered ()) } {old_types_and_defs  := [] } Nothing.

Tactic Notation "scope" := ltac2:(Control.enter (fun () => scope ())).

Tactic Notation "scope2" := ltac2:(Control.enter (fun () => scope2 ())).

Tactic Notation "snipe_no_check" := 
  ltac2:(Control.enter (fun () => scope (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe2_no_check" := 
  ltac2:(Control.enter (fun () => scope2 (); ltac1:(verit_no_check_orch))).

Tactic Notation "snipe" :=
  ltac2:(Control.enter (fun () => scope (); ltac1:(verit))).

Tactic Notation "snipe2" :=
  ltac2:(Control.enter (fun () => scope2 (); ltac1:(verit))).