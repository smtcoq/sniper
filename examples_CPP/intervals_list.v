Require Import ZArith Lia.
From Sniper Require Import Sniper.
From SMTCoq Require Import SMTCoq.
Require Import Bool OrderedType OrderedTypeEx.
Open Scope Z_scope.
Import BinInt.

(** This file is adapted from Amélie Ledein and Catherine 
Dubois's development: 
https://gitlab.com/finite_set_Coq/real_intervals_list **)


(*** 1 : Definitions and proofs ***)

Definition extractionOption (A : Type)  (op : option A) (val_def : A) :=
 match op with
  |None => val_def
  |Some x => x
 end.

Parameters min_int (*max_int*) : Z.

(*********************************************************************)
(** *                    Types and invariants                        *)
(*********************************************************************)

(***************************************************)
(** ** Type and invariant of real intervals list   *)
(***************************************************)

(** *** Type of elt_list *)
Inductive elt_list :=
 |Nil : elt_list
 |Cons : Z -> Z -> elt_list -> elt_list.

(** *** Invariant of elt_list *)
Inductive Inv_elt_list : Z -> elt_list -> Prop :=
 | invNil  : forall b, Inv_elt_list b Nil
 | invCons : forall (a b  j: Z) (q : elt_list),
     j <= a -> a <= b ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

(***************************************************)
(** ** Size, max and min on real intervals list    *)
(***************************************************)

(** *** Size of elt_list *)
Fixpoint ps (s : Z) (l : elt_list) := match l with
|Nil => s
|Cons min max q => ps (max-min+1 + s) q
end.
Definition process_size (l : elt_list) := ps 0 l.

(** *** Maximum of elt_list *)
Fixpoint pm (m : Z) (l : elt_list) := match l with
|Nil => m
|Cons _ b q => pm b q
end.
Definition process_max (l : elt_list) := pm min_int l.

(** *** Minimum of elt_list *)
Definition get_min (l : elt_list) (e : Z) : Z := match l with
|Nil => e
|Cons a _ _ => a
end.

(**************************************)
(** ** Type and invariant of domain   *)
(**************************************)

(** *** Type of domain *)
Record t := mk_t {
  domain : elt_list ;
  size : Z ;
  max  : Z ;
  min  : Z }.

(** *** Invariant of domain *)
Definition Inv_t (d : t) := Inv_elt_list (min d) (domain d)
                              /\ (min d) = get_min (domain d) min_int
                              /\ (max d) = process_max (domain d)
                              /\ (size d) = process_size (domain d).

Fixpoint elt_list_length (l : elt_list) : nat := match l with
 | Nil => 0
 | Cons _ _ q => 2 + elt_list_length q
end.

(** elt_list_is_compdec **)

Fixpoint elt_list_eqb e1 e2 :=
match e1, e2 with
| Nil, Nil => true
| Cons a b e1', Cons a' b' e2' => if a =? a' then if b =? b' then elt_list_eqb e1' e2' else false else false
| _ , _ => false
end.

Lemma elt_list_eqb_spec : forall (e1 e2 : elt_list), elt_list_eqb e1 e2 = true <-> e1 = e2.
Proof.
intros e1 e2; split.
- intros H. generalize dependent e2. induction e1; destruct e2; intros H ; try reflexivity; try inversion H.
    * simpl in H. destruct (z=? z1) eqn:E1. destruct (z0=? z2) eqn:E2.
rewrite Z.eqb_eq in *. rewrite E1. rewrite E2. apply IHe1 in H. rewrite H. reflexivity. inversion H.
inversion H.
- intros H. induction H. induction e1. reflexivity.  
simpl.
destruct (z=?z) eqn:E1; destruct (z0 =? z0) eqn:E2; try reflexivity.
assumption. rewrite Z.eqb_neq in E2. elim E2; reflexivity. 
rewrite Z.eqb_neq in E1. elim E1; reflexivity.   
rewrite Z.eqb_neq in E2. elim E2; reflexivity. Qed. 

  Fixpoint elt_list_lt (t1 t2 : elt_list) : Prop :=
    match t1, t2 with
    | Nil, Nil => False
    | Nil, Cons _ _ _ => True
    | Cons _ _ _, Nil => False
    | Cons a1 b1 t1',  Cons a2 b2 t2' => (Z.lt a1 a2) \/ (Z.eqb a1 a2 /\ Z.lt b1 b2)
\/ (Z.eqb a1 a2 /\ Z.eqb b1 b2 /\ elt_list_lt t1' t2')
    end.


Lemma elt_list_lt_trans : forall (x y z : elt_list),
      elt_list_lt x y -> elt_list_lt y z -> elt_list_lt x z.
Proof.
intros x.
induction x; intros y y'.
- intros H1 H2. destruct y ; inversion H1. destruct y' ; auto.
- intros H H1. simpl. destruct y'.
    + destruct y ; inversion H1.
    + destruct y.
      * inversion H.
      * inversion H; inversion H1; try lia.
        destruct H2 as [H2 | H3]. left. 
        destruct H2 as [H2 H2']. apply Z.eqb_eq in H2. subst; assumption.
        destruct H3 as [H3 [H4 H5]]. left. apply Z.eqb_eq in H3. subst; assumption.
        destruct H0 as [H0 | H0']. destruct H0 as [H0' H0''].  apply Z.eqb_eq in H0'. 
        subst; lia. destruct H0' as [H01 [H02 H03]]. apply Z.eqb_eq in H01. subst; lia.
        destruct H0 as [H0 | H0']. destruct H0 as [H01 H02]. destruct H2 as [H2 | H2'].
        destruct H2 as [H2 H2']. apply Z.eqb_eq in H01. subst. apply Z.eqb_eq in H2. subst.
        right. left. split. apply Z.eqb_eq; reflexivity. eapply Z.lt_trans. 
        eauto; assumption. assumption.
        destruct H2' as [H20 [H21  H22]]. apply Z.eqb_eq in H01. apply Z.eqb_eq in H20.
        apply Z.eqb_eq in H21. subst. right. left. split; try apply Z.eqb_eq; auto.
        destruct H2 as [H2 | H2']. destruct H0' as [H01 [H02 H03]]. 
        destruct H2 as [H21 H22]. apply Z.eqb_eq in H21. apply Z.eqb_eq in H01.
        apply Z.eqb_eq in H02. subst. right. left. split; try apply Z.eqb_eq; auto.
        destruct H0' as [H01 [H02 H03]]. destruct H2' as [H21 [H22 H23]]. 
        apply Z.eqb_eq in H01. apply Z.eqb_eq in H02. apply Z.eqb_eq in H21.
        apply Z.eqb_eq in H22. subst. right. right. split ; try split; try apply Z.eqb_eq; auto.
        eapply IHx; eauto. Qed.

Lemma elt_list_lt_not_eq : forall (x y : elt_list), elt_list_lt x y -> x <> y.
Proof.
 induction x as [ |a b x1 IHx1]; intros [ |a' b' y1]; simpl; auto.
    - discriminate.
    - intros [H1 |[ [H1 H2] | [H3 [H4 H5]]]]; intros H; inversion H; subst.
      + lia. 
      + lia. 
      + apply IHx1 in H5. elim H5. reflexivity. 
  Qed.

Definition elt_list_compare : forall (x y : elt_list), Compare elt_list_lt Logic.eq x y.
  Proof.
    induction x as [ |a b x IHx]; intros [ |a' b' y]; simpl.
    - now apply EQ.
    - now apply LT.
    - now apply GT.
    - specialize (IHx y). case_eq (compare a a'); intros l H.
      + apply LT. simpl. now left. 
      + destruct IHx as [H1 | H2 | H3].
        * case_eq (compare b b'). intros l1 H2. apply LT.
 right. left. split; auto. apply Z.eqb_eq. assumption.
intros l1 H2.
apply LT.
 right. right. split. apply Z.eqb_eq. assumption. split.
apply Z.eqb_eq. all: try assumption.
intros l0. intros H2. apply GT. simpl. 
right. left. split; auto. apply Z.eqb_eq. symmetry. assumption.
     * case_eq (compare b b'); intros l1 H1. apply LT. simpl. right. left. 
split. apply Z.eqb_eq. all: try assumption.
apply EQ. rewrite l. rewrite l1. rewrite H2. reflexivity.
apply GT. simpl. right. left. split. apply Z.eqb_eq. symmetry. all: try assumption.
        * case_eq (compare b b'); intros l1 H1. apply LT. simpl. right. left. 
split. apply Z.eqb_eq. all: try assumption.
apply GT. simpl. right; right; split. apply Z.eqb_eq. symmetry. assumption.
split. apply Z.eqb_eq. symmetry. all: try assumption.  
apply GT. simpl. right. left. split. apply Z.eqb_eq. symmetry. all: try assumption.
      +  apply GT. simpl. left. assumption.
  Defined.

Instance elt_list_compdec : CompDec elt_list :=
    CompDec_from _ _ elt_list_eqb_spec _ elt_list_lt_trans elt_list_lt_not_eq
                 elt_list_compare Nil.

#[export] Hint Resolve elt_list_compdec : typeclass_instances.

(* Boolean version of the invariant *)

Fixpoint Inv_elt_list_bool (z : Z) (e : elt_list) : bool :=
match e with
| Nil => true
| Cons a b e' => (z <=? a) && (a <=? b) && Inv_elt_list_bool (b + 2) e'
end.

Lemma Inv_elt_list_decidable : forall b e, 
Inv_elt_list b e <-> Inv_elt_list_bool b e = true.
Proof.
intros b e; split.
- intros H; induction H as [ | a b j q H H0].
  + reflexivity.
  + simpl. apply and_andb_impl. split.
     * apply and_andb_impl; apply Zle_imp_le_bool in H; apply Zle_imp_le_bool in H0. 
    split; [assumption | assumption].
     * assumption.
- generalize dependent b. induction e.
  + intros ; constructor.
  + intros b H. constructor; simpl in H; revert H; trakt Z Prop; intros H ; destruct H as [H1 H2];
revert H1; trakt Z Prop ; intros H1 ; destruct H1 as [H1 H1']; try (apply Zle_bool_imp_le; assumption).
apply IHe. assumption. Qed.

Trakt Add Relation 2 (Inv_elt_list) (Inv_elt_list_bool) (Inv_elt_list_decidable).

Definition t_eqb (t1 t2 : t) :=
match t1, t2 with
| {| domain := d1; size := s1; max := max1 ; min := min1 |},
  {| domain := d2; size := s2; max := max2 ; min := min2 |} => elt_list_eqb d1 d2 && Z.eqb s1 s2 && Z.eqb max1 max2 && 
  Z.eqb min1 min2
end.

Lemma t_eqb_spec : forall (t1 t2 : t), t_eqb t1 t2 = true <-> t1 = t2.
Proof.
intros t1 t2; split.
- intros H. destruct t1 as [domain0 size0 max0 min0] ; 
destruct t2 as [domain1 size1 max1 min1]; try reflexivity; try inversion H;
simpl in H; destruct (elt_list_eqb domain0 domain1) eqn:E1.
    rewrite elt_list_eqb_spec in E1;
    destruct (max0 =? max1) eqn:E2;
    destruct (min0 =? min1) eqn:E3;
    destruct (size0 =? size1) eqn:E4. 
rewrite Z.eqb_eq in *. subst. reflexivity. all: inversion H. 
- intros H. unfold t_eqb. subst. destruct t2 as [domain1 size1 max1 min1].
trakt Z Prop.
pose proof elt_list_eqb_spec. rewrite H. 
pose proof Z.eqb_eq. repeat rewrite H0. auto. Qed. 

Definition t_lt (t1 t2 : t) : Prop :=
 match t1, t2 with
| {| domain := d1; size := s1; max := max1 ; min := min1 |},
  {| domain := d2; size := s2; max := max2 ; min := min2 |} => elt_list_lt d1 d2 \/ (d1 = d2 /\ Z.lt s1 s2) \/ 
(d1 = d2 /\ s1 = s2 /\ Z.lt max1 max2) \/ ( d1 = d2 /\ s1 = s2 /\ max1 = max2 /\ Z.lt min1 min2)
 end.

Lemma t_lt_trans : forall (x y z : t),
      t_lt x y -> t_lt y z -> t_lt x z.
Proof.
destruct x as [domain0 size0 max0 min0] ; 
destruct y as [domain1 size1 max1 min1] ; destruct z as [domain2 size2 max2 min2].
intros H1 H2.
inversion H1; inversion H2.
- eapply elt_list_lt_trans with domain0 domain1 domain2 in H. 
firstorder. auto.
- unfold t_lt. destruct H0 as [H0  | [H4 | H5]].
destruct H0 as [H01  H02]. rewrite H01 in H.
repeat left. auto.
destruct H4 as [H41 H42]. 
rewrite H41 in H. auto.
destruct H5 as [H51 [H52 [H53 H54]]].
subst. auto.
- unfold t_lt. destruct H as [[H H'] | [[H3 [H4 H5]] | [H6 [H7 [H8 H9]]]]];
subst; auto.
- unfold t_lt. 
destruct H as [[H H'] | [[H3 [H4 H5]] | [H6 [H7 [H8 H9]]]]];
destruct H0 as 
[[H0 H0'] | [[H03 [H04 H05]] | [H06 [H07 [H08 H09]]]]].
eapply Z.lt_trans in H0'. right. repeat left. subst. eauto. 
apply H'.
subst. right. auto. all: subst; auto.
eapply Z.lt_trans in H05. right. right. left. eauto. assumption.
right. right. left. auto.
right. right. auto.
repeat right. eapply Z.lt_trans in H09. eauto. assumption. 
 Qed.

Lemma t_lt_not_eq : forall (x y : t), t_lt x y -> x <> y.
Proof.
 destruct x as [domain0 size0 max0 min0]. intros y ; destruct y as
[domain1 size1 max1 min1]; unfold t_lt; intros H.
intros HFalse.
inversion HFalse. subst. inversion H. apply elt_list_lt_not_eq in H0. 
elim H0; reflexivity.
inversion H0. lia. lia.
  Qed.

Definition t_compare : forall (x y : t), Compare t_lt Logic.eq x y.
  Proof.
    destruct x as [domain0 size0 max0 min0]; intros y ; 
destruct y as [domain1 size1 max1 min1].
case_eq (compare domain0 domain1); intros l; intros H.
- apply LT. simpl. auto.
- case_eq (compare size0 size1); intros l1 ; intros H1.
apply LT. simpl. auto.
case_eq (compare max0 max1); intros l2; intros H2.
apply LT. simpl. right. right. left. auto.
case_eq (compare min0 min1); intros l3; intros H3.
apply LT. simpl; firstorder.
apply EQ. subst. auto.
apply GT. subst. simpl. firstorder.
apply GT. subst. simpl. firstorder.
apply GT. subst. simpl. firstorder.
- apply GT. simpl. firstorder. Defined.

Instance t_compdec : CompDec t :=
    CompDec_from _ _ t_eqb_spec _ t_lt_trans t_lt_not_eq
                 t_compare {| domain := Nil; size := 0; max := 0 ; min := 0 |}.

#[export] Hint Resolve t_compdec : typeclass_instances.


(* Boolean version of the invariant on domain *)
Definition Inv_t_bool (d : t) := Inv_elt_list_bool (min d) (domain d)
                              && ((min d) =? get_min (domain d) min_int)
                              && ((max d) =? process_max (domain d))
                              && ((size d) =? process_size (domain d)).

Lemma Inv_t_decidable : forall d, Inv_t d <-> Inv_t_bool d = true.
Proof.
intros d.
split.
- intros H. inversion H. unfold Inv_t_bool. repeat split; auto; verit.
- intros H. unfold Inv_t. unfold Inv_t_bool in H. verit.
Qed.

Trakt Add Relation 1 (Inv_t) (Inv_t_bool) (Inv_t_decidable).

(*** 2 : Some examples ***) 

Section Paper_examples.

Theorem inv_elt_list_monoton : forall l y z, 
Inv_elt_list y l -> z <= y -> Inv_elt_list z l.
Proof.
induction l; snipe_with_trakt.
Qed.


Theorem inv_elt_list_restrict : forall l a b c d y, c <= d ->
((a<=c)/\(c<=b)) /\ ((a<=d)/\(d<=b)) ->
Inv_elt_list y (Cons a b l) -> Inv_elt_list y (Cons c d l).
Proof.
snipe_with_trakt inv_elt_list_monoton. Qed.


Lemma inv_elt_list_simpl : forall l z1 z2 z0 z y, 
Inv_elt_list y (Cons z1 z2 (Cons z z0 l)) -> 
Inv_elt_list y (Cons z1 z2 l).
Proof. snipe_with_trakt inv_elt_list_monoton.
Qed.

Lemma evenLength : forall (l : elt_list), Init.Nat.even (elt_list_length l) = true.
Proof. induction l ; snipe. Qed. 

(** Example: invariant on empty domain **) 


(************************************)
(** * Definition                    *)
(************************************)
Definition empty : t := mk_t Nil 0 min_int min_int.

(************************************)
(** * Construction of the invariant *)
(************************************)

Theorem empty_inv : Inv_t (empty).
Proof. snipe_with_trakt. Qed.

(************************************)
(** * Specification                 *)
(************************************)
Lemma equiv_empty_Nil : forall d, Inv_t d -> 
domain d = Nil <-> d = empty.
Proof. snipe_with_trakt. Qed.

(* Manual proof : split;intro Hyp.
- unfold Inv_t in H. decompose [and] H. destruct d. unfold empty.
  rewrite Hyp in H2;simpl in H2;rewrite H2.
  rewrite Hyp in H1;unfold process_max in H1;unfold pm in H1;
  simpl in H1;rewrite H1.
  rewrite Hyp in H4;unfold process_size in H4;unfold ps in H4;
  simpl in H4;rewrite H4.  
  simpl in Hyp;rewrite Hyp. reflexivity.
- unfold Inv_t in H. decompose [and] H. unfold empty in Hyp. 
  rewrite Hyp. unfold domain. reflexivity. 
Qed. *)








