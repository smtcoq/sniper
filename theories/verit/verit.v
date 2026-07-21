From Ltac2 Require Import Ltac2.
From Trakt Require Import Trakt.
From Stdlib Require Import ZArith.

From Sniper Require Import transformations.add_compdecs.

From SMTCoq Require CompDec Conversion Tactics.
Import Tactics.


(** Remove add compdecs from SMTCoq's preprocess1 *)

Ltac preprocess1 Hs :=
    Conversion.remove_compdec_hyps_option Hs;
    let cpds := Conversion.collect_compdecs in
    let rels := Conversion.generate_rels cpds in
    Conversion.trakt1 rels Hs.


Tactic Notation "verit_no_check_orch" constr(global) :=
  let tac :=
  ltac2:(h |- intros; unfold is_true in *; Tactics.get_hyps_cont_ltac1 (ltac1:(h local |-
  let Hsglob := Conversion.pose_hyps h (@None unit) in
  let Hs :=
      lazymatch local with
      | Some ?local' => Conversion.pose_hyps local' Hsglob
      | None => constr:(Hsglob)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := Conversion.intros_names in
    Conversion.preprocess2 Hs';
    verit_bool_no_check_base_auto Hs';
    QInst.vauto
  ]) h)) in tac global.

Tactic Notation "verit_no_check_orch"           :=
  ltac2:(intros; unfold is_true in *; Tactics.get_hyps_cont_ltac1 ltac1:(local |-
  let Hs :=
      lazymatch local with
      | Some ?local' => Conversion.pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := Conversion.intros_names in
    Conversion.preprocess2 Hs';
    verit_bool_no_check_base_auto Hs';
    QInst.vauto
  ])).


Tactic Notation "verit_orch" constr(global) :=
  let tac :=
  ltac2:(h |- intros; unfold is_true in *; Tactics.get_hyps_cont_ltac1 (ltac1:(h local |-
  let Hsglob := Conversion.pose_hyps h (@None unit) in
  let Hs :=
      lazymatch local with
      | Some ?local' => Conversion.pose_hyps local' Hsglob
      | None => constr:(Hsglob)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := Conversion.intros_names in
    Conversion.preprocess2 Hs';
    verit_bool_base_auto Hs';
    QInst.vauto
  ]) h)) in tac global.

Tactic Notation "verit_orch" :=
  ltac2:(intros; unfold is_true in *; Tactics.get_hyps_cont_ltac1 ltac1:(local |-
  let Hs :=
      lazymatch local with
      | Some ?local' => Conversion.pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := Conversion.intros_names in
    Conversion.preprocess2 Hs';
    verit_bool_base_auto Hs';
    QInst.vauto
  ])).
