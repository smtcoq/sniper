From Ltac2 Require Import Ltac2.
From Trakt Require Import Trakt.
Require Import ZArith.

Require Import add_compdecs.

From SMTCoq Require SMT_classes Conversion Tactics.

Ltac trakt_rels rels :=
  lazymatch rels with
  | Some ?rels' => first [trakt Z bool with rel rels' | trakt bool with rel rels']
  | None => first [trakt Z bool | trakt bool]
  end.

Ltac revert_and_trakt Hs rels :=
  lazymatch Hs with
  | (?Hs, ?H) =>
    revert H;
    revert_and_trakt Hs rels
    (* intro H *)
  | ?H =>
    revert H;
    trakt_rels rels
    (* intro H *)
  end.

Definition sep := True.

Ltac get_hyps_upto_sep :=
  lazymatch goal with
  | H' : ?P |- _ =>
    lazymatch P with
    | sep => constr:(@None unit)
    | _ =>
      let T := type of P in
      lazymatch T with
      | Prop =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        lazymatch acc with
        | Some ?acc' => constr:(Some (acc', H'))
        | None => constr:(Some H')
        end
      | _ =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        acc
      end
    end
  end.


(* Goal False -> 1 = 1 -> unit -> false = true -> True. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   assert (H : sep) by exact I. *)
(*   intros H3 H4. *)
(*   let Hs := get_hyps_upto_sep in idtac Hs. *)
(* Abort. *)


Ltac intros_names :=
  let H := fresh in
  let _ := match goal with _ => assert (H : sep) by exact I; intros end in
  let Hs := get_hyps_upto_sep in
  let _ := match goal with _ => clear H end in
  Hs.


(* Goal False -> 1 = 1 -> unit -> false = true -> True. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   let Hs := intros_names in idtac Hs. *)
(* Abort. *)


Ltac post_trakt Hs :=
  lazymatch Hs with
  | (?Hs1, ?Hs2) =>
    post_trakt Hs1;
    post_trakt Hs2
  | ?H => try (revert H; trakt_reorder_quantifiers; trakt_boolify_arrows; intro H)
  end.

Ltac trakt1 rels Hs :=
  lazymatch Hs with
  | Some ?Hs => revert_and_trakt Hs rels
  | None => trakt_rels rels
  end.

(** Remove add compdecs from SMTCoq's preprocess1 *)

Ltac preprocess1 Hs :=
    Conversion.remove_compdec_hyps_option Hs;
    let cpds := Conversion.collect_compdecs in
    let rels := Conversion.generate_rels cpds in
    trakt1 rels Hs.


Declare ML Module "coq-smtcoq.smtcoq".
Tactic Notation "verit_bool_no_check_base_auto" constr(h) := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit_bool_no_check" constr(h) :=
  let tac :=
  ltac2:(h |- Tactics.get_hyps_cont_ltac1 (ltac1:(h hs |-
  match hs with
  | Some ?hs => verit_bool_no_check_base_auto (Some (h, hs))
  | None => verit_bool_no_check_base_auto (Some h)
  end;
  QInst.vauto) h)) in tac h.

Tactic Notation "verit_bool_no_check" :=
  ltac2:(Tactics.get_hyps_cont_ltac1 ltac1:(hs |- verit_bool_no_check_base_auto hs; QInst.vauto)).

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