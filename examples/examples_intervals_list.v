Require Import definitions_intervals_list.
(* Add Rec LoadPath "~/github.com/louiseddp/sniper" as Sniper. *)
From Sniper Require Import Sniper.
Require Import ZArith.
Local Open Scope Z_scope.

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
