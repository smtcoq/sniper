From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
From Ltac2 Require Import String.
Require Import List ZArith.
Import ListNotations.
Require Import printer.
Require Import triggers.
Require Import filters.

From SMTCoq Require SMT_classes Conversion Tactics Trace State SMT_classes_instances QInst BVList FArray.

Ltac2 is_prod (c: constr) :=
  match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod _ _ => true
    | _ => false
  end.

Ltac2 higher_order (c: constr) :=
let t := Constr.type c in
let rec aux t :=
  match Constr.Unsafe.kind t with
    | Constr.Unsafe.Prod bind t' => 
        Bool.or (let ty := Constr.Binder.type bind in (is_prod ty)) (aux t')
    | _ => false
  end
in aux t.


Ltac2 rec codomain_not_prop_aux (c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Prod bi c' => codomain_not_prop_aux c'
  | Constr.Unsafe.App x1 arr => codomain_not_prop_aux x1
  | _ => if Constr.equal c 'Prop then false else true
  end.

Ltac2 codomain_not_prop (c: constr) := codomain_not_prop_aux (Constr.type c).

Ltac2 codomain_prop (c: constr) := Bool.neg (codomain_not_prop c).

(* Ltac2 Eval (higher_order '@nth). *) 

(** Triggers and filters for Sniper tactics *)

Ltac2 trigger_reflexivity () :=
  TDisj (TIs (TSomeDef, (Arg id)) (TAny NotArg))
        (TDisj (TContains (TSomeHyp, NotArg) (TConstant None (Arg id)))
        (TContains (TGoal, NotArg) (TConstant None (Arg id)))).

Ltac2 filter_reflexivity () :=
  FConj 
    (FConstr 
      ['Z.add; 'Z.sub; 'Z.mul; 'Z.eqb; 'Z.ltb; 'Z.leb; 'Z.geb; 'Z.gtb; 'Z.lt;
      'Z.le; 'Z.ge; 'Z.gt; 'Pos.lt; 'Pos.le; 'Pos.ge; 'Pos.gt; 'Z.to_nat; 'Pos.mul;
      'Pos.sub; 'Init.Nat.add; 'Init.Nat.mul; 'Nat.eqb; 'Nat.leb; 'Nat.ltb; 'ge; 'gt; 
      'N.add; 'N.mul; 'N.eqb; 'N.leb; 'N.leb; 'N.ltb; 'Peano.lt; 'negb; 'not; 'andb; 'orb; 'implb; 'xorb;
      'Bool.eqb; 'iff; 'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_eq; 
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_and;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_or;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_xor;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_add;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_mult;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_ult;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_slt;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_concat;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_shl;
      'SMTCoq.bva.BVList.BITVECTOR_LIST.bv_shr;
      '@FArray.select;
      '@FArray.diff;
      'is_true;
      '@SMTCoq.classes.SMT_classes.eqb_of_compdec;
      '@SMTCoq.classes.SMT_classes.CompDec;
      '@SMTCoq.classes.SMT_classes_instances.Nat_compdec;
      '@SMTCoq.classes.SMT_classes_instances.list_compdec;
      '@SMTCoq.classes.SMT_classes_instances.prod_compdec;
      '@SMTCoq.classes.SMT_classes_instances.option_compdec;
      '@SMTCoq.classes.SMT_classes_instances.Z_compdec]) 
      (FPred higher_order).

Ltac2 trigger_unfold_reflexivity () :=
 TIs (TSomeHyp, Arg id) (TEq tDiscard tDiscard tDiscard NotArg).

Ltac2 filter_unfold_reflexivity () :=
 FPred (fun x => (Bool.neg 
  (
  let ty := Constr.type x in 
    match! ty with
    | @eq ?a ?t ?u => Constr.equal t u
    | _ => false
    end))).

Ltac2 trigger_unfold_in () :=
 TDisj (TMetaLetIn (TIs (TSomeHyp, Arg id) (TEq tDiscard tDiscard (TAny (Arg id)) NotArg)) ["H"; "eq"]
      (TConj (TIs (TNamed "H", Arg id) tDiscard)
      (TContains (TNamed "eq", NotArg) (TConstant None (Arg id)))))
      (TMetaLetIn (TIs (TSomeHyp, Arg id) (TEq tDiscard tDiscard tDiscard (Arg id))) ["H"; "eq"]
      (TConj (TIs (TNamed "H", Arg id) tDiscard)
      (TContains (TNamed "eq", NotArg) (TVar TLocalDef (Arg id))))).

Ltac2 filter_unfold_in () :=
  FPredList (fun l => match l with | [x; y] => 
    Bool.or
    (let t := type x in 
      match! t with
        | @eq ?a ?u ?v => Bool.neg (Constr.is_var u)
      end) (Bool.neg (higher_order y)) | _ => true end).

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

Ltac2 filter_algebraic_types () :=
  FConj (FConstr 
          ['Z; 'bool; 'positive; 'N; 'nat ; 'FArray.farray; 'SMTCoq.classes.SMT_classes.EqbType; 
          'SMTCoq.classes.SMT_classes.CompDec;
          'SMTCoq.classes.SMT_classes.Comparable;
          'SMTCoq.classes.SMT_classes.Inhabited ; 'Coq.Structures.OrderedType.Compare])
        (FPred codomain_prop).

Ltac2 trigger_generation_principle () :=
  TIs (TSomeHyp, NotArg) (TInd None (Arg id)).

Ltac2 filter_generation_principle () :=
  FConj (FConstr 
          ['Z; 'bool; 'positive; 'FArray.farray; 'SMTCoq.classes.SMT_classes.EqbType;
          'SMTCoq.classes.SMT_classes.CompDec;
          'SMTCoq.classes.SMT_classes.Comparable;
          'SMTCoq.classes.SMT_classes.Inhabited ; 'Coq.Structures.OrderedType.Compare])
        (FPred codomain_prop).

Ltac2 trigger_anonymous_fun () :=
  TDisj (
  TMetaLetIn (TContains (TSomeHyp, Arg Constr.type) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
    (TConj (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
    (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg))))
            (TIs (TNamed "f", Arg id) tDiscard)))
  (TMetaLetIn (TContains (TGoal, Arg id) (TLambda tDiscard tDiscard (Arg id))) ["H"; "f"]
  (TConj (TNot (TMetaLetIn (TContains (TNamed "H", NotArg) (TCase tDiscard tDiscard None (Arg id))) ["c"]
  (TContains (TNamed "c", NotArg) (TTrigVar (TNamed "f") NotArg)))) (TIs (TNamed "f", Arg id) tDiscard))).

Ltac2 trigger_add_compdecs () :=
  TDisj
  (triggered when (AnyHyp) contains TEq (TAny (Arg id)) tDiscard tDiscard NotArg) 
  (triggered when (TGoal) contains TEq (TAny (Arg id)) tDiscard tDiscard NotArg).

Ltac2 filter_add_compdecs () :=
FConj
(FConstr ['Z; 'bool; 'positive; 'nat ; 'FArray.farray; 'Prop; 'Set; 'Type])
(FPred (fun x => Bool.or (is_prod x)
    (match Constr.Unsafe.kind x with | Constr.Unsafe.App u ca => (Constr.equal u '@SMT_classes.CompDec) | _=> false end ))).
   
(* Ltac2 trigger_fold_local_def () :=
  tlet def ; def_unfold := (triggered when (TSomeDef) is (tArg) on (Arg id)) in
  TConj (triggered when (TSomeHypProp) contains (TTrigVar (TNamed "def_unfold") (NotArg)) on (NotArg))
        (triggered when (TNamed "def") is (TTrigVar (TNamed "def") (NotArg)) on (Arg id)) 
(* trick to get as argument the definition not unfolded*).  *)

 Ltac2 trigger_fold_local_def_in_hyp () :=
TDisj 
  (tlet def ; def_unfold := (triggered when (TSomeDef) is (tArg) on (Arg id)) in
  TConj (triggered when (TSomeHypProp) contains (TTrigVar (TNamed "def_unfold") (NotArg)) on (Arg id))
        (triggered when (TNamed "def") is (TTrigVar (TNamed "def") (NotArg)) on (Arg id)))
  (tlet def ; def_unfold := (triggered when (TSomeDef) is (tArg) on (Arg id)) in
  TConj (triggered when (TSomeDef) contains (TTrigVar (TNamed "def_unfold") (NotArg)) on (Arg id))
        (triggered when (TNamed "def") is (TTrigVar (TNamed "def") (NotArg)) on (Arg id))).
(* trick to get as argument the definition not unfolded*)

(** warning A TNot is not interesting whenever all hypotheses are not considered !!! *)
Ltac2 trigger_trakt_bool_hyp () :=
  (TNot (TIs (TSomeHypProp, Arg id) (TEq (TTerm 'bool NotArg) tDiscard tDiscard NotArg))).

Ltac2 trigger_trakt_bool_goal () :=
  (TNot (TIs (TGoal, NotArg) (TEq (TTerm 'bool NotArg) tDiscard tDiscard NotArg))).

Ltac2 trigger_pose_case () :=
  TMetaLetIn (TContains (TGoal, NotArg) (TCase tDiscard tDiscard None (Arg id))) ["M"]
    (TConj
       (TNot (TMetaLetIn (TContains (TGoal, NotArg) (TProd tArg tDiscard NotArg)) ["f"]
               (TContains (TNamed "f", NotArg) (TTrigVar (TNamed "M") NotArg))))
       (TIs (TNamed "M", Arg id) tDiscard)).
