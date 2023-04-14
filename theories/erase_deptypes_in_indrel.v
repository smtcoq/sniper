Require Import utilities.
Require Import MetaCoq.Template.All.
Require Import erase_type_in_indexes.


(** Description of the transformation erase_deptype_in_inrel :

Notation : ?Ak means that this type could be present or not.

A non-mutual inductive relation

R (P1 : T1) ... (Pk : Tk) : X1 -> ... Xp -> (A11 : Type) -> ... -> (Aml : Type) -> 
I1 A11 ... Al1 -> ... -> Im Am1 ... Aml -> ?A11 -> ... -> ?Al1 ->
?A1m -> ... -> ?Aml -> Prop := 

C1 : forall (x1 : T1) ... (xj : Tj) (H ... : Prop) : R P1 ... Pk X1 ... Xp 
    TYC11 ... TYCml 

where all the Ij could be transformed by the transformation 
erase_type_in_indexes and all the Aiks are different non 
isomorphic types for each i fixed.
The Xis are not sorts.

will be transformed into

R' (P1 : T1) ... (Pk : Tk) : X1 -> ... Xp -> I1' -> ... Im' -> ?{TYC111  + ... + TYC1m1} 
-> ... -> ?{?TYCjl1 + ... + TYCjml} :=
| C1' : forall (x1 : T1) ... (xj : Tj) (H ... : Prop) : R' P1 Pk X1 ... Xp (inl ( inl ( ... )))
 
*)

Record env := mk_env 
  { env_parameters : list (aname*term*nat); (* the name of a parameter, its type and its db index *)
    env_args : list (aname*term*nat); (* idem for the arguments of the inductive *)
    env_types : list (aname*term*nat); (* idem for its args of type Type *)
    env_inductives : list (aname*term*nat); (* idem for the inductives arguments *)
    env_elems : list (aname*term*nat); (* idem for the args of the args of type Type *)
 }.

Definition lift10_term_and_db (p : aname*term*nat) :=
let x := p.1.1 in 
let y := p.1.2 in
let z := p.2 in
(x, lift 1 0 y, S z).

Fixpoint get_env_aux (e : env) (t : term) := 


Inductive doors_o_callee : Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| doors_o_callee_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : doors_o_callee ω bool (IsOpen d) x

(** - There is no particular doors_o_calleeises on the result [x] of a request for [ω] to
      close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.
