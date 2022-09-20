From Coq Require Import ZArith.
Require Import PeanoNat.
From mathcomp Require Import all_ssreflect zify. 
From Sniper Require Import Sniper.
Require Import Bool OrderedType OrderedTypeEx.
From Trakt Require Import Trakt.

Trakt Add Relation 2 (Nat.eqb) (Z.eqb) (ZifyBool.Z_of_nat_eqb_iff).

Trakt Add Relation 2 (Nat.leb) (Z.leb) (ZifyBool.Z_of_nat_leb_iff).

(* lambda terms *)

Inductive term : Type := var of nat | app of term & term | abs of term.

Scheme Equality for term.

Lemma nat_beq_is_nat_eqb n n' : Nat.eqb n n' = nat_beq n n'.
Proof. induction n'; auto. Qed.

Lemma term_beq_spec : forall (t1 t2 : term), term_beq t1 t2 = true <-> t1 = t2.
Proof.
intros t1 t2; split.
- generalize dependent t2. induction t1 as [n | t1' IHt1' t1'' IHt1'' | t1'];
intros t2; intro H; destruct t2 as [n' | t2' t2'' | t2']; simpl in H; try rewrite H; 
try inversion H ; auto.
  + rewrite <- nat_beq_is_nat_eqb in H. apply Nat.eqb_eq in H. auto.
  + revert H. trakt Prop. intros H. destruct H as [H' H'']. 
  apply IHt1'' in H''. subst. apply IHt1' in H'. subst. auto.
  + apply IHt1' in H. subst. auto.
- intros H. subst; induction t2 ; simpl.
  + rewrite <- nat_beq_is_nat_eqb. lia.
  + trakt Prop. auto.
  + auto.
Qed.  

Fixpoint term_lt (t1 t2 : term) : bool :=
 match t1, t2 with
| var n, var n' => n <? n'
| app t1 t2, app t1' t2' => if term_lt t1 t1' then true else term_beq t1 t1' && term_lt t2 t2'
| abs u, abs v => term_lt u v
| var _, _=> true
| _, var _ => false
| abs _, app _ _ => true
| app _ _, abs _ => false
 end.

Lemma term_lt_trans : forall (x y z : term),
      term_lt x y -> term_lt y z -> term_lt x z.
Proof.
intros x. induction x; intros y z; destruct y; destruct z; intros; simpl in * ; try lia.
- destruct (term_lt x1 z1) eqn:E; auto.
  + destruct (term_lt x1 y1) eqn:E'. destruct (term_lt y1 z1) eqn:E''. 
apply (IHx1 y1 z1 E') in E''. unfold is_true in E''.
rewrite E'' in E. inversion E. 
destruct (term_beq y1 z1) eqn:F. apply term_beq_spec in F. subst.
rewrite E in E'. inversion E'. simpl in H0. inversion H0.
destruct (term_beq x1 y1) eqn:F. simpl in H. apply term_beq_spec in F. subst.
rewrite E in H0. destruct (term_beq y1 z1) eqn:F. simpl in *.
eapply IHx2; eauto. simpl in H0. auto.
simpl in H. auto. 
eapply IHx; eauto. Qed.

Lemma term_lt_not_eq : forall (x y : term), term_lt x y -> x <> y.
Proof.
intros x.
induction x ; destruct y ; intros H ; intros HFalse; unfold term_lt; simpl in *; inversion HFalse.
+ lia.
+ subst. destruct (term_lt y1 y1) eqn: E. apply IHx1 in E. elim E; reflexivity.
destruct (term_beq y1 y1) eqn:E'; simpl in H. apply IHx2 in H. elim H; reflexivity.
inversion H. apply IHx in H. elim H. assumption. Qed.

Definition term_compare : forall (x y : term), Compare term_lt Logic.eq x y.
  Proof.
intros x ; induction x; destruct y; simpl in * ; auto.
+ case_eq (n < n0); intros H.
 - apply LT. simpl. lia.
 - case_eq (n =? n0). intros H1. apply EQ. apply f_equal. lia.
 intros H1. apply GT. simpl. lia.
+ apply LT; auto.
+ apply LT; auto.
+ apply GT; auto.
+ specialize (IHx1 y1); specialize (IHx2 y2) ; inversion IHx1 ; inversion IHx2.
    * apply LT; simpl ; rewrite H; auto.
    * apply LT; simpl; rewrite H; auto.
    * apply LT; simpl; rewrite H; auto.
    * apply LT; simpl. destruct (term_lt x1 y1) eqn:E; auto. rewrite H0. 
rewrite H. rewrite andb_true_r. 
apply term_beq_spec; auto.
    * subst. apply EQ. auto.
    * subst. apply GT. simpl. destruct (term_lt y1 y1) eqn:E; auto. rewrite H0.
rewrite andb_true_r. apply term_beq_spec; auto.
    * apply GT. simpl. rewrite H. auto.
    * apply GT. simpl. rewrite H. auto.
    * apply GT. simpl. rewrite H. auto.
    * apply GT. simpl; auto.
    * apply GT. simpl; auto.
    * apply LT. simpl; auto. 
+ specialize (IHx y). inversion IHx.
  * apply LT; auto.
  * apply EQ; apply f_equal ; auto.
  * apply GT; auto. Qed.

Instance term_compdec : CompDec term :=
    CompDec_from _ _ term_beq_spec _ term_lt_trans term_lt_not_eq
                 term_compare (var 0).

#[export] Hint Resolve term_compdec : typeclass_instances.


Trakt Add Relation 2 (@eq term) (@SMT_classes.eqb_of_compdec term term_compdec)
          (@SMT_classes.compdec_eq_eqb term term_compdec).

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
