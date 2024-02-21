From Ltac2 Require Import Ltac2 Init.

(** A filter is useful to block the application of a transformation
even if the transformation is triggered *)

Ltac2 Type rec filter := [
  | FConstr (constr list) 
  | FPred (constr -> bool)
  | FConstrList (constr list list)
  | FPredList (constr list -> bool) 
  | FConj (filter, filter) 
  | FTrivial ].

Ltac2 trivial_filter := FTrivial.

Ltac2 Type exn ::= [ WrongArgNumber(string) ].

(** [l] is the list of arguments of the tactic (returned by the interpretation
of the trigger 
and f is the filter applied to them *)

Ltac2 rec pass_the_filter 
  (l : constr list)
  (f : filter) : bool :=
    match f with
      | FConstr lc => 
          if Int.equal (List.length l) 1 then if List.exist (Constr.equal (List.hd l)) lc then false else true
          else Control.throw (WrongArgNumber "this filter is valid only for transformations taking one argument")
      | FPred p => if List.exist p l then false else true 
      | FConstrList lc => if List.exist (List.equal Constr.equal l) lc then false else true
      | FPredList p => if p l then false else true
      | FConj f1 f2 => Bool.and (pass_the_filter l f1) (pass_the_filter l f2)
      | FTrivial => true
    end.