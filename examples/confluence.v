From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect zify.
From Sniper Require Import Sniper.
From Trakt Require Import Trakt.

(* lambda terms *)

Inductive term : Type :=
  | var : nat -> term
  | app : term -> term -> term
  | abs : term -> term.

Fixpoint shift (d c : nat) (t : term) : term :=
  match t with
    | var n => var (if c <= n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (S c) t1)
  end.

Fixpoint subst (n : nat) (u t : term) : term :=
  match t with
    | var m => if m == n then shift n 0 u else var (if m <= n then m else m - 1)
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
Proof.
elim: t n; simpl; try congruence.
by move=> n m; rewrite addn0 if_same.
Qed.

Lemma shift_add d d' c c' t :
  c <= c' <= c + d -> shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
move=> /andP [] /subnKC <-; rewrite leq_add2l => /subnKC <-.
move: (c' - _) (d - _) => {}c' {}d.
elim: t c; simpl; try (move: addSn; congruence).
by move=> n c; f_equal; do !case: ifP; lia.
Qed.

Lemma shift_shift_distr d c d' c' t :
  c' <= c -> shift d' c' (shift d c t) = shift d (d' + c) (shift d' c' t).
Proof.
move=> /subnKC <-; move: (c - _) => {}c.
elim: t c'; simpl; try (move: addSn addnS; congruence).
by move=> n c'; f_equal; do !case: ifP; lia.
Qed.

Lemma shift_subst_distr n d c u t :
  c <= n -> shift d c (subst n u t) = subst (d + n) u (shift d c t).
Proof.
move=> /subnKC <-; move: (n - _) => {}n.
elim: t c; simpl; try (move: addSn addnS; congruence).
move=> v c; do !(case: ifP; simpl); try (intros; congr var); try lia.
by move=> ? ? ?; rewrite shift_add //; lia.
Qed.

Lemma subst_shift_distr n d c u t :
  n <= c ->
  shift d c (subst n u t) = subst n (shift d (c - n) u) (shift d c.+1 t).
Proof.
move=> /subnKC <-; move: (c - _) => {}c; rewrite addKn.
elim: t n; simpl; try (move: addSn; congruence).
move=> v n; do !(case: ifP; simpl); try (intros; congr var); try lia.
by move=> ? ?; rewrite -shift_shift_distr.
Qed.

Lemma subst_shift_cancel n d c u t :
  c <= n < d + c -> subst n u (shift d c t) = shift d.-1 c t.
Proof.
move=> /andP [] /subnKC <-; rewrite addnC ltn_add2r => /subnKC <-.
move: (n - _) (d - _) => {}n {}d.
rewrite addSn /=; elim: t c; simpl; try (move: addnS; congruence).
by move=> v c; do !(case: ifP; simpl); try (intros; congr var); try lia.
Qed.

Lemma subst_subst_distr n m x y t :
  m <= n ->
  subst n x (subst m y t) = subst m (subst (n - m) x y) (subst n.+1 x t).
Proof.
move=> /subnKC <-; move: (n - _) => {}n; rewrite addKn.
elim: t m; simpl; try (move: addSn; congruence).
move=> v m; do !(case: ifP; simpl); try (intros; congr var); try lia.
  by move=> ? ? ? ?; rewrite shift_subst_distr.
by move=> ? ? ? ?; rewrite subst_shift_cancel //; lia.
Qed.
