From MetaCoq Require Import All.
Require Import Sniper.
Require Import ZArith.
Import Decide.

Inductive mem : Z -> list Z -> Prop :=
    MemMatch : forall (xs : list Z) (n : Z), mem n (n :: xs)
  | MemRecur : forall (xs : list Z) (n n' : Z), mem n xs -> mem n (n' :: xs).

MetaCoq Run (decide mem []). 
Next Obligation.
apply decidable_proof. Qed.

Print mem_linear_decidable.

Trakt Add Relation 2 mem mem_linear_decidable decidable_lemma.

Lemma mem_S : 
  forall (l : list Z) (n : Z), mem n l -> mem (n + 1) (map (fun x => x + 1)%Z l).
Proof.
 induction l; snipe. Undo. 
 induction l.
  - 
    trakt bool.
    intros;
    prenex_higher_order.
    get_def mem_linear_decidable.
    expand_hyp mem_linear_decidable_def; clear mem_linear_decidable_def.
    eliminate_fix_hyp H1.
    expand_hyp H0; clear H0.
    eliminate_dependent_pattern_matching H1.
    interp_alg_types (list).
    get_projs_st (list).
    elimination_polymorphism.
    generalize dependent f.
    generalize dependent mem_linear_decidable.
    trakt bool. verit. Abort.