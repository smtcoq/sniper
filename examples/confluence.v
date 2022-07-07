From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect zify.
From SMTCoq Require Import SMTCoq.
From Trakt Require Import Trakt.
From Sniper Require Import Sniper.

Lemma nat_Z_gof_id (n : nat) : n = Z.to_nat (Z.of_nat n).
Proof. exact/esym/Nat2Z.id. Qed.

Lemma nat_Z_bool_fog_cond_id (z : Z) : (0 <=? z)%Z -> Z.of_nat (Z.to_nat z) = z.
Proof. by move=> HPz; apply/Z2Nat.id/Z.leb_spec0. Qed.

Lemma nat_Z_bool_cond_f_always_true (n : nat) : (0 <=? Z.of_nat n)%Z.
Proof. exact/Z.leb_spec0/Nat2Z.is_nonneg. Qed.

Trakt Add Embedding
  (nat) (Z) (Z.of_nat) (Z.to_nat) (nat_Z_gof_id) (nat_Z_bool_fog_cond_id)
    (nat_Z_bool_cond_f_always_true).

Trakt Add Symbol (O%N) (0%Z) (erefl).

Trakt Add Symbol (S) (fun x => Z.add x 1%Z) (Nat2Z.inj_succ).

Trakt Add Symbol (addn) (Z.add) (Nat2Z.inj_add).

Trakt Add Relation (Nat.eqb) (Z.eqb) (ZifyBool.Z_of_nat_eqb_iff).

Trakt Add Relation (Nat.leb) (Z.leb) (ZifyBool.Z_of_nat_leb_iff).

(* lambda terms *)

Inductive term : Type := var of nat | app of term & term | abs of term.

Instance CD_term : CompDec term. Admitted.

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
Proof.
(* Trakt does not seem to properly handle universal quantifiers in hypotheses. *)
(* elim: t n; scope; trakt Z Prop. *)
(* With Trakt-like manual preprocessing, SMTCoq does not work. *)
(*
elim: t n; scope.
- have {}H13 (d c v : Z) :
    (0 <=? d)%Z -> (0 <=? c)%Z -> (0 <=? v)%Z -> (c <=? v)%Z -> t (Z.to_nat d) (Z.to_nat c) (var (Z.to_nat v)) = var (Z.to_nat (v + d)).
    admit.
  have {}H10 (d c v : Z) :
    (0 <=? d)%Z -> (0 <=? c)%Z -> (0 <=? v)%Z -> (c <=? v)%Z = false -> t (Z.to_nat d) (Z.to_nat c) (var (Z.to_nat v)) = var (Z.to_nat v).
    admit.
  have {}H8 (d c : Z) (t0 : term) :
    (0 <=? d)%Z -> (0 <=? c)%Z -> t (Z.to_nat d) (Z.to_nat c) (abs t0) = abs (t (Z.to_nat d) (Z.to_nat (c + 1)) t0).
    admit.
  Fail smt.
  Fail verit.
  Fail cvc4.
*)
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
