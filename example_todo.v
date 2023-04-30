From MetaCoq Require Import All.
Require Import Sniper.
Require Import erase_deptypes_in_indrel.
Import Decide.

Inductive trm : Type -> Type :=
| Zero : trm nat
| Succ : trm nat -> trm nat
| B : bool -> trm bool.

Inductive trm_le : forall (A B : Type), trm A -> trm B -> Prop :=
| lez (n : trm nat) : trm_le nat nat (Zero) (Succ n) 
| leS (n : trm nat) (m : trm nat) : trm_le nat nat n m -> trm_le nat nat n (Succ m)
| leB : trm_le bool bool (B false) (B true).

Inductive trm' : Type :=
| Zero' : trm'
| Succ' : trm' -> trm'
| B' : bool -> trm'.

Inductive trm_le' : trm' -> trm' -> Prop :=
| lez' (n : trm') : trm_le' (Zero') (Succ' n) 
| leS' (n : trm') (m : trm') : trm_le' n m -> trm_le' n (Succ' m)
| leB' : trm_le' (B' false) (B' true).

MetaCoq Run (decide trm_le' []).
Next Obligation. Admitted.

Print trm_le'_decidable.
(* MetaCoq Run (erase_ty_erase_dep [<%trm%>] <%trm_le%>). *)