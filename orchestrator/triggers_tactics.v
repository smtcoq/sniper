From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
From Ltac2 Require Import String.
Require Import List.
Import ListNotations.
Require Import printer.
Require Import triggers.

From Sniper Require Import utilities.

From SMTCoq Require SMT_classes Conversion Tactics Trace State QInst.

Declare ML Module "coq-smtcoq.smtcoq".

(** Add compdecs is an atomic transformation not related to Trakt *)

Ltac add_compdecs_terms t :=
  let T := type of t in
  first [ first [constr_eq T Type | constr_eq T Set] ;
  match goal with
      (* If it is already in the local context, do nothing *)
    | _ : SMT_classes.CompDec t |- _ => idtac
    (* Otherwise, add it in the local context *)
    | _ =>
      let p := fresh "p" in 
        assert (p:SMT_classes.CompDec t);
        [ try (exact _)       (* Use the typeclass machinery *)
        | .. ]
  end | idtac].

(** Remove add compdecs from SMTCoq's preprocess1 *)

Ltac preprocess1 Hs :=
    Conversion.remove_compdec_hyps_option Hs;
    let cpds := Conversion.collect_compdecs in
    let rels := Conversion.generate_rels cpds in
    Conversion.trakt1 rels Hs.

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

Tactic Notation "verit_no_check" constr(global) :=
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

Tactic Notation "verit_no_check"           :=
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



(** We need to use a trick here: there
is no function in Ltac2's API which returns 
a Ltac1 value given its ident. We always need the absolute path
and we cannot look at several paths because the function [Ltac1.ref] 
throws an uncatchable exception whenever the path is not the good one.
Consequently, all the Orchestrator's tactics should be in one file, or the user has to 
provide the absolute path herself, which is not convenient at all.
Using elpi avoid these difficulties, even if the user needs
to create its own copy of all the tactic which take arguments 
TODO : a PR in Coq to avoid this problem *)

From elpi Require Import elpi.

Elpi Tactic apply_ltac1.
Elpi Accumulate lp:{{

  solve ((goal _ _ _ _ [str S| H]) as G) GS :-
    coq.ltac.call S H G GS.

}}.
Elpi Typecheck.

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

(** [run] runs a Ltac1 tactic given its ident and its arguments (provided as a string) *) 

Ltac2 run (s : string) (l : constr list) :=
let id := Ident.of_string s in
let id := of_ident (get_opt id) in
let l := of_list (List.map of_constr l) in
Ltac1.apply ltac1val:(fun s l => 
  let id := s in elpi apply_ltac1 ltac_string:(id) ltac_term_list:(l)) [id; l] run.

Section tests.

(** For tests *)
Ltac myapply2 A B := split ; [apply A | apply B].
Ltac myexact t := exact t.

Goal (True /\ True) /\ (True -> True -> True /\ True).
Proof.
run "split" [].
let str := "split" in run str [].
run "myexact" ['I].
run "myexact" ['I].
intros H1 H2.
run "myapply2" ['H1; 'H2].
Qed.

End tests.

Ltac2 is_prod (c: constr) :=
  match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod _ _ => true
    | _ => false
  end.

Ltac2 not_higher_order (c: constr) :=
let t := Constr.type c in
let rec aux t :=
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod bind t' => 
        Bool.and (let ty := Constr.Binder.type bind in Bool.neg (is_prod ty)) (aux t')
    | _ => true
  end
in aux t.

(* Ltac2 Eval (not_higher_order '@map). *)

(** Triggers for Sniper tactics *)


Ltac2 trigger_definitions () :=
  TDisj (TMetaLetIn (TContains (TGoal, NotArg) (TConstant None (Arg id))) ["def"]
         (TPred (TNamed "def", Arg id) not_higher_order))
        (TMetaLetIn (TContains (TSomeHyp, NotArg) (TConstant None (Arg id))) ["def"]
         (TPred (TNamed "def", Arg id) not_higher_order)).

Ltac2 trigger_higher_order_equalities :=
  TIs (TSomeHyp, Arg id) (TEq (TProd tDiscard tDiscard NotArg) tDiscard tDiscard NotArg).

Ltac2 trigger_fixpoints :=
  TContains (TSomeHyp, Arg id) (TFix tDiscard tDiscard NotArg).

Ltac2 trigger_pattern_matching :=
  TContains (TSomeHyp, Arg id) (TCase tDiscard tDiscard None NotArg).

Ltac2 trigger_polymorphism () :=
 TDisj (TIs (TSomeHypProp, NotArg) 
       (TProd (TSort TSet NotArg) tDiscard NotArg))
       (TIs (TSomeHypProp, NotArg) 
       (TProd (TSort TBigType NotArg) tDiscard NotArg)).

Ltac2 trigger_higher_order :=
  TContains (TSomeHyp, NotArg) (TProd (TProd tDiscard tDiscard NotArg) tDiscard NotArg).

Ltac2 trigger_algebraic_types :=
  TDisj (TContains (TGoal, NotArg) (TInd None (Arg id))) (TContains (TSomeHyp, NotArg) (TInd None (Arg id))).

Ltac2 rec codomain_not_prop_aux (c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Prod bi c' => codomain_not_prop_aux c'
  | Constr.Unsafe.App x1 arr => codomain_not_prop_aux x1
  | _ => if Constr.equal c 'Prop then false else true
  end.

Ltac2 codomain_not_prop (c: constr) := codomain_not_prop_aux (Constr.type c).

Ltac2 trigger_generation_principle () :=
  TDisj (TMetaLetIn (TContains (TGoal, NotArg) (TInd None (Arg id))) ["Indu"]
         (TPred (TNamed "Indu", Arg id) codomain_not_prop))
        (TMetaLetIn (TContains (TSomeHyp, NotArg) (TInd None (Arg id))) ["Indu"] 
        (TPred (TNamed "Indu", Arg id) codomain_not_prop)).

Ltac2 trigger_anonymous_funs () :=
  TDisj (
  TMetaLetIn (TContains (TSomeHyp, Arg Constr.type) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg)))))
  (TMetaLetIn (TContains (TGoal, Arg id) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg))))).

Ltac2 trigger_add_compdecs () :=
  TDisj (TDisj
  (triggered when (AnyHyp) contains TEq (TApp (TAny (Arg id)) tDiscard NotArg) tDiscard tDiscard NotArg)
  (triggered when (AnyHyp) contains TEq (TAny (Arg id)) tDiscard tDiscard NotArg))
(TDisj
  (triggered when (TGoal) contains TEq (TApp (TAny (Arg id)) tDiscard NotArg) tDiscard tDiscard NotArg)
  (triggered when (TGoal) contains TEq (TAny (Arg id)) tDiscard tDiscard NotArg)). 

(** warning A TNot is not interesting whenever all hypotheses are not considered !!! *)
Ltac2 trigger_trakt_bool () :=
  TMetaLetIn (TIs (TSomeHyp, (Arg Constr.type)) (TType 'Prop NotArg)) ["H"]
  (TNot (TIs (TNamed "H", NotArg) (TEq (TTerm 'bool NotArg) tDiscard tDiscard NotArg))).
(* 
Ltac2 trigger_trakt_Z_bool :=
  TOneTime. *)



