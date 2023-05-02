From MetaCoq Require Import All.
Require Import Sniper.
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
    generalize dependent f. revert elpi_ctx_entry_62_. 
    revert elpi_ctx_entry_80_.
    trakt Z bool. verit. Abort.