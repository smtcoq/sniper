From MetaCoq Require Import All.
Require Import Sniper.
Require Import erase_deptypes_in_indrel.
Require Import ZArith.
Import Decide.

Inductive mem : nat -> list nat -> Prop :=
    MemMatch : forall (xs : list nat) (n : nat), mem n (n :: xs)
  | MemRecur : forall (xs : list nat) (n n' : nat), mem n xs -> mem n (n' :: xs).

MetaCoq Run (decide mem []). 
Next Obligation.
apply decidable_proof. Qed.

Print mem_linear_decidable.

Trakt Add Relation 2 mem mem_linear_decidable decidable_lemma.

Lemma mem_id : 
  forall (l : list nat) (n : nat), mem n l -> mem (S n) (map (fun x => x+1) l).
Proof.
 induction l; snipe. Undo. 
 induction l.
  - 
    trakt bool.
    anonymous_funs.
    intros;
    prenex_higher_order.
    get_def mem_linear_decidable.
    expand_hyp mem_linear_decidable_def; clear mem_linear_decidable_def.
    expand_hyp H1; clear H1.
    expand_hyp H; clear H.
    eliminate_fix_hyp H2; clear H2.
    eliminate_fix_hyp H3; clear H3.
    eliminate_dependent_pattern_matching H.
    eliminate_dependent_pattern_matching H2.
    interp_alg_types (list).
    get_projs_st (list).
    elimination_polymorphism.
    generalize dependent f0.
    generalize dependent mem_linear_decidable.
    generalize dependent f.
    trakt Z bool. verit. Abort.


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