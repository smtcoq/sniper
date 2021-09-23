(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SMTCoq.SMTCoq.
Require Import Bool OrderedType OrderedTypeEx.

Section tree.

Variable A : Type.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.



Definition is_empty (t : tree) :=
 match t with
 | Leaf => true
 | _ => false
 end.


Fixpoint rev_elements_aux acc s :=
  match s with
   | Leaf => acc
   | Node l x r => rev_elements_aux (x :: rev_elements_aux acc l) r
  end.

Definition rev_elements := rev_elements_aux nil.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0
   | Node l _ r => S (cardinal l + cardinal r)
  end.

Fixpoint maxdepth s :=
 match s with
 | Leaf => 0
 | Node l _ r => S (max (maxdepth l) (maxdepth r))
 end.




 Context `{HA : CompDec A}.


  Fixpoint tree_eqb (xs ys : tree) : bool :=
    match xs, ys with
    | Leaf, Leaf => true
    | Node t1 a t2, Node u1 b u2 => @eqb_of_compdec _ HA a b && tree_eqb t1 u1 && tree_eqb t2 u2
    | _, _ => false
    end.




  Lemma  tree_eqb_spec : forall (t t' : tree), tree_eqb t t' = true <-> t = t'.
  Proof.
    induction t as [ |t1 IHt1 a t2 IHt2]; intros [ |t1' b t2']; simpl; split; try discriminate; auto.
    - rewrite andb_true_iff. intros [H1 H2].
destruct (eqb_of_compdec HA a b) eqn:E. rewrite Typ.eqb_compdec_spec in E.
simpl in H1. rewrite IHt1 in H1. rewrite IHt2 in H2. now subst.
inversion H1.
    - intros H. inversion H as [H1]. rewrite andb_true_iff; split.
      + rewrite andb_true_iff; split. now rewrite Typ.eqb_compdec_spec.
            * subst t1'. now rewrite IHt1. 
      + subst t2'. now rewrite IHt2.
  Qed.

  Instance tree_eqbtype : EqbType (tree) := Build_EqbType _ _ tree_eqb_spec.

  Fixpoint tree_lt (t1 t2 : tree) : Prop :=
    match t1, t2 with
    | Leaf, Leaf => False
    | Leaf, Node _ _ _ => True
    | Node _ _ _, Leaf => False
    | Node t1 a t2,  Node u1 b u2 => (lt a b) \/ (@eqb_of_compdec _ HA a b /\ tree_lt t1 u1)
\/ (tree_eqb t1 u1 /\ @eqb_of_compdec _ HA a b /\ tree_lt t2 u2)
    end.


  Lemma tree_lt_trans : forall (x y z : tree),
      tree_lt x y -> tree_lt y z -> tree_lt x z.
  Proof.
    induction x as [ |x1 IHx1 a x2 IHx2]; intros [ |y1 b y2] [ |z1 c z2]; simpl; auto.
    - inversion 1.
    - intros [H1a | H1b] [H2a | H2b].
      + left; eapply lt_trans; eauto.
      + left. destruct H2b as [H2b | H2c].
          * destruct H2b as [H2c H2d]. unfold is_true in H2c. rewrite Typ.eqb_compdec_spec in H2c.
subst c. assumption.
          * destruct H2c as [H2c [H2d H2e]]. unfold is_true in H2d. rewrite Typ.eqb_compdec_spec in H2d.
subst c. assumption.
      + left. destruct H1b as [ [H1b H1c]  | [H1d [H1e H1f]]]. unfold is_true in H1b. rewrite Typ.eqb_compdec_spec in H1b. 
now subst b. unfold is_true in H1e. rewrite Typ.eqb_compdec_spec in H1e. now subst b.
      + right. destruct H1b as [ [H1c H1d] | [H1e [H1f H1g]]]. destruct H2b as [ [H2c H2d] | [H2e [H2f H2g]]]. left. split.

        * unfold is_true in H1c. rewrite Typ.eqb_compdec_spec in H1c. now subst a.
        * apply IHx1 with y1. assumption. assumption.
        * left. split.  unfold is_true in H2f. rewrite Typ.eqb_compdec_spec in H2f. now subst b. unfold is_true in H2e.
rewrite tree_eqb_spec in H2e. subst. assumption.
        * destruct H2b as [ [H2c H2d] | [H2e [H2f H2g]]]. 
          { left. unfold is_true in H1f. rewrite Typ.eqb_compdec_spec in H1f. subst.
split. assumption. unfold is_true in H1e. rewrite tree_eqb_spec in H1e. subst. assumption. }
      right. unfold is_true in H1e. rewrite tree_eqb_spec in H1e. subst. split. assumption.
unfold is_true in H1f. rewrite Typ.eqb_compdec_spec in H1f. subst b. split. assumption.
apply IHx2 with y2; easy.
Qed.
        


  Lemma tree_lt_not_eq : forall (x y : tree), tree_lt x y -> x <> y.
  Proof.
    induction x as [ |x1 IHx1 a x2 IHx2]; intros [ |y1 b y2]; simpl; auto.
    - discriminate.
    - intros [H1 |[ [H1 H2] | [H3 [H4 H5]]]]; intros H; inversion H; subst.
      + apply lt_not_eq in H1. auto.
      + eapply IHx1; eauto.
      + apply IHx2 in H5. auto.
  Qed.


  Instance tree_ord : OrdType (tree) :=
    Build_OrdType _ _ tree_lt_trans tree_lt_not_eq.

  Definition tree_compare : forall (x y : tree), Compare tree_lt Logic.eq x y.
  Proof.
    induction x as [ |x1 IHx1 a x2 IHx2]; intros [ |y1 b y2]; simpl.
    - now apply EQ.
    - now apply LT.
    - now apply GT.
    - specialize (IHx1 y1). case_eq (compare a b); intros l H.
  
      + apply LT. simpl. now left.
      + destruct IHx1 as [H1 | H2 | H3].
        * apply LT. simpl. right. left. split; auto. now apply Typ.eqb_compdec_spec.
        * specialize (IHx2 y2). destruct IHx2 as [H4 |  H5  | H6]. apply LT. subst.
simpl. right. right. split. apply tree_eqb_spec. reflexivity.
split. apply Typ.eqb_compdec_spec. reflexivity. assumption. apply EQ. subst. reflexivity.
        apply GT. simpl. right. right. split; auto. now apply tree_eqb_spec. split. 
now apply Typ.eqb_compdec_spec. easy.
         * apply GT. simpl. right. left. split. apply Typ.eqb_compdec_spec. subst. reflexivity.
assumption.
      + specialize (IHx2 y2). destruct IHx2 as [H4 |  H5  | H6].
        * apply GT. simpl. left. assumption.
        * apply GT. simpl. left. assumption.
        * apply GT. simpl. left. assumption. 
  Defined.


  Instance tree_comp : Comparable (tree) := Build_Comparable _ _ tree_compare.


  Instance tree_inh : Inhabited (tree) := Build_Inhabited _ Leaf.


  Instance tree_compdec : CompDec (tree) := {|
    Eqb := tree_eqbtype;
    Ordered := tree_ord;
    Comp := tree_comp;
    Inh := tree_inh
  |}.




End tree. 

Arguments tree {_}.
Arguments Leaf {_}.
Arguments Node {_} _ _ _.
Arguments is_empty {_} _.



#[export] Hint Resolve tree_compdec : typeclass_instances.
