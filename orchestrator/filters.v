From Ltac2 Require Import Ltac2 Init.

(** A filter is useful to block the application of a transformation
even if the transformation is triggered *)

Ltac2 Type filter := [
  | FConstr (constr) 
  | FPred (constr -> bool)
  | FConstrList (constr list)
  | FPredList (constr list -> bool) ].

Ltac2 Type exn ::= [ WrongArgNumber(string) ].


(** [l] is the list of arguments of the tactic (returned by the interpretation
of the trigger 
and f is the filter applied to them *)

Ltac2 pass_the_filter 
  (l : constr list)
  (f : filter) : bool :=
    match f with
      | FConstr c => 
          if Int.equal (List.length l) 1 then if Constr.equal c (List.hd l) then false else true
          else Control.throw (WrongArgNumber "this filter is valid only for transformations taking one argument")
      | FPred p => if List.exist p l then false else true 
      | FConstrList l' => if List.equal Constr.equal l l' then false else true
      | FPredList p => if p l then false else true
    end.