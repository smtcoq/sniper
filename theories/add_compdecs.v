From Ltac2 Require Import Ltac2.
From SMTCoq Require SMT_classes SMT_classes_instances.
Require Import ZArith.

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

Goal (forall (A: Type) (l : list A), False).
intros. ltac1:(add_compdecs_terms A). Abort.
