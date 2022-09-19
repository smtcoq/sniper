From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect zify. 
From Sniper Require Import Sniper.
From Trakt Require Import Trakt.

Trakt Add Relation 2 (Nat.eqb) (Z.eqb) (ZifyBool.Z_of_nat_eqb_iff).

Trakt Add Relation 2 (Nat.leb) (Z.leb) (ZifyBool.Z_of_nat_leb_iff).

(* lambda terms *)

Inductive term : Type := var of nat | app of term & term | abs of term.

Instance CD_term : CompDec term. Admitted.

Trakt Add Relation 2 (@eq term) (@SMT_classes.eqb_of_compdec term CD_term)
          (@SMT_classes.compdec_eq_eqb term CD_term).

Fixpoint shift (d c : nat) (t : term) : term :=
  match t with
    | var n => var (if c <=? n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Fixpoint subst (n : nat) (u t : term) : term :=
  match t with
    | var m =>
      if m =? n then shift n 0 u else var (if m <=? n then m else m - 1)
    | app t1 t2 => app (subst n u t1) (subst n u t2)
    | abs t' => abs (subst (S n) u t')
  end.

Reserved Notation "t ->b1 t'" (at level 70, no associativity).

Inductive betared1 : term -> term -> Prop :=
  | betared1beta t1 t2     : app (abs t1) t2 ->b1 subst 0 t2 t1
  | betared1appl t1 t1' t2 : t1 ->b1 t1' -> app t1 t2 ->b1 app t1' t2
  | betared1appr t1 t2 t2' : t2 ->b1 t2' -> app t1 t2 ->b1 app t1 t2'
  | betared1abs t t'       : t ->b1 t' -> abs t ->b1 abs t'
  where "t ->b1 t'" := (betared1 t t').

Lemma shiftzero n t : shift 0 n t = t.
Proof. elim: t n; snipe. Qed.

Lemma shift_add d d' c c' t :
  c <=? c' -> c' <=? c + d -> shift d' c' (shift d c t) = shift (d' + d) c t.
Proof. elim: t d d' c c'; snipe. Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <=? c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof. elim: t d d' c c'; snipe. Qed.
