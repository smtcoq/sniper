From Sniper Require Import Sniper. 
From SMTCoq Require SMTCoq.
Require Import ZArith Psatz.
From Trakt Require Trakt.
From Hammer Require Hammer.
From mathcomp Require all_ssreflect all_algebra.
From mathcomp.zify Require ssrZ zify_algebra.
Require Cdcl.NOlia.
Import ListNotations.
From Coq Require ZifyClasses ZifyBool ZifyInst.

Module small_examples.
Import Trakt.
Import Hammer.


(* SMTCoq provides a smt tactic, but itauto provides a tactic with 
the same name so we introduce notations to prevent the confusion *)

Tactic Notation "smt_SMTCoq" := smt.

Tactic Notation "smt_itauto" := Cdcl.NOlia.smt.

(* Examples from section 2 *)

(* An example completely automatized by the hammer tactic *)
Lemma length_rev_app : forall B (l l' : list B),
length (rev (l ++ l')) = length l + length l'.
Proof. scongruence use: app_length, rev_length. Qed.
 
(* A variant that hammer cannot solve because it lacks arithmetical features *)
Lemma length_rev_app_cons :
forall B (l l' : list B) (b : B),
length (rev (l ++ (b::l'))) =
(length l) + (length l') + 1.
Proof. (* Fail hammer. *) Fail scongruence use: app_length, rev_length. 
Abort.

(* sauto and SMTCoq cannot perform case analysis in general *)
Lemma app_nilI : forall B (l1 l2 : list B),
l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof. Fail sauto. Fail smt_SMTCoq. Fail verit.
Abort.


Lemma eZ : forall (z : Z), (z >= 0 -> z < 1 -> z = 0)%Z.
Proof. smt_SMTCoq. Qed.

Lemma enat : forall (x : nat), ~ (x + 1 = 0)%nat.
Proof. (* Fail smt_SMTCoq. *) Abort. (* TODO : should fail (use SMTCoq 2.0) *)

Import all_ssreflect all_algebra.
Import ssrZ zify_algebra.
Import AlgebraZifyInstances. 

(* SMTCoq cannot reason about the mathcomp's representation of integers *)
Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. Fail smt_SMTCoq. Abort.

Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. lia. Qed.

Lemma congr_int : forall (z : int),
((z + 1) :: nil = (1 + z) :: nil)%R.
Proof. Fail lia. Abort.

(* itauto's smt tactic is able to solve this goal*)

Lemma eintb : forall (z : int), (z + 1 == 1 + z)%R = true.
Proof. smt_itauto. Abort.

(* but it fails on this one because of the uninterpreted function f *)
Lemma eintcb : forall (f : int -> int) (z : int),
(f (z + 1) == f (1 + z))%R = true.
Proof. Fail smt_itauto. Abort.

(* Examples from section 3 *)

(* We add embeddings between Z and int to trakt's database *)


Import ZifyClasses ZifyBool ZifyInst.

Notation Z_to_int := ssrZ.int_of_Z.

Lemma int_Z_gof_id : forall (x : int), x = Z_to_int (Z_of_int x).
Proof.
  intro x. symmetry. exact (Z_of_intK x).
Qed.

Lemma int_Z_fog_id : forall (z : Z), Z_of_int (Z_to_int z) = z.
Proof.
  intro x. exact (ssrZ.int_of_ZK x).
Qed.

Trakt Add Embedding int Z Z_of_int Z_to_int int_Z_gof_id int_Z_fog_id.

Local Delimit Scope Z_scope with Z.

Lemma addz_Zadd_embed_eq : forall (x y : int),
  Z_of_int (intZmod.addz x y) = (Z_of_int x + Z_of_int y)%Z.
Proof.
  apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_addz).
Qed.

Trakt Add Symbol intZmod.addz Z.add addz_Zadd_embed_eq.


(* Example 3.1: trakt's translation from a predicate on int to a predicate on Z *)
Lemma trakt_Z_predicate :  forall (P : int -> Prop) (x : int), P x <-> P x.
Proof. intros. trakt Z Prop. Abort.

Lemma eqint_eqZ_equiv : forall (x y : int), x = y <-> Z_of_int x = Z_of_int y.
Proof.
  apply (@TRInj _ _ _ _ Op_int_eq).
Qed.

Lemma eqint_Zeqb_equiv : forall (x y : int), x = y <-> (Z_of_int x =? Z_of_int y)%Z = true.
Proof.
  intros x y.
  refine (iff_trans (eqint_eqZ_equiv x y) _).
  symmetry.
  apply Z.eqb_eq.
Qed.

Lemma add_embedding_property : forall (x y : int),
Z_of_int (x + y) = (Z_of_int x + Z_of_int y)%Z.
lia. Qed.

(* Example 3.2: trakt's translation can go under uninterpreted functions *)

Trakt Add Conversion GRing.zero.
Trakt Add Conversion GRing.add.

Lemma trakt_int_Z_Prop : forall (f : int -> int -> int) (x y : int),
f x (y + 0)%R = f (x + 0)%R y. 
Proof. trakt Z Prop. Abort. 

Lemma eq_int_equivalence_property : forall (x y : int),
x = y <-> (Z_of_int x =? Z_of_int y)%Z = true.
Proof. lia. Qed.

(* Example 3.3: trakt's translation can target a boolean logic *)
Lemma trakt_int_Z_bool : forall (f : int -> int) (x : int), (f x + 0 = f x)%R.
Proof. trakt Z bool. Abort. 

(* Example 3.4: trakt's translation can deal with partial embeddings *) 
Lemma trakt_nat_Z_Prop : forall (f : nat -> nat) (n : nat), (f n + 0 = f n)%nat.
Proof. trakt Z Prop. Abort.

(* Notation to distinguish the two versions of the tactic *)
Tactic Notation "inst_with_subterms_of_type_type" := inst.
Tactic Notation "inst_with_chosen_parameters" := elimination_polymorphism.

(* Example 3.6: polymorphism *)
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B),
(x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2) ->
forall (x1 x2 : option Z) (y1 y2 : list unit),
(x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof. intro H. inst_with_subterms_of_type_type. (* 25 instances *)
Undo. inst_with_chosen_parameters. verit. (* 1 instance *) 
Qed.

(* Examples from section 4 *)

(* Pre-processing for itauto *)

Trakt Add Conversion GRing.mul.

Lemma mulz_Zmul_embed_eq : forall (x y : int),
  Z_of_int (intRing.mulz x y) = (Z_of_int x * Z_of_int y)%Z.
Proof.
  apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_mulz).
Qed.

Trakt Add Symbol intRing.mulz Z.mul mulz_Zmul_embed_eq.

Lemma Z_of_int_id_embed_eq : forall (x : int), Z_of_int x = Z_of_int x.
Proof. reflexivity. Qed.

Trakt Add Symbol Z_of_int (@id Z) Z_of_int_id_embed_eq.

Lemma Orderle_int_Zleb_equiv : forall (x y : int), (x <= y)%R = (Z_of_int x <=? Z_of_int y)%Z.
Proof.
  apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_int_le).
Qed.

Trakt Add Relation 2
  (@Order.le ring_display int_porderType)
  Z.leb
  Orderle_int_Zleb_equiv.

Trakt Add Conversion GRing.Zmodule.sort.
Trakt Add Conversion Num.NumDomain.porderType.

Goal forall (f : int -> int) (x : int),
(f (2%:Z * x) <= f (x + x))%R = true.
Proof. Fail smt_itauto. trakt Z Prop. smt_itauto. Qed.

(* Overloading *)

Goal forall (f : int -> int) (x : int), (f x + 0)%R = f x. 
Proof. trakt Z Prop. smt_itauto. Qed.  

(* Pre-processing for sauto (hammer) *)

Lemma app_eq_nil (A : Type) (l l' : list A):
l ++ l' = [] -> l = [] /\ l' = [].
Proof.
Fail sauto. 
get_gen_statement_for_variables_in_context; sauto.
Qed.

 Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

Definition memory_chunk_to_Z mc :=
      match mc with
      | Mint8signed => 0%Z
      | Mint8unsigned => 1%Z
      | Mint16signed => 2%Z
      | Mint16unsigned => 3%Z
      | Mint32 => 4%Z
      | Mint64 => 5%Z
      | Mfloat32 => 6%Z
      | Mfloat64 => 7%Z
      | Many32 => 8%Z
      | Many64 => 9%Z
      end.

Lemma memory_chunk_to_Z_eq x y:
x = y <-> memory_chunk_to_Z x = memory_chunk_to_Z y.
Proof. Fail sauto. get_gen_statement_for_variables_in_context; sauto. Qed.

(* Pre-processing for firstorder congruence *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem SSSSev_ev : forall (n : nat),
ev (S (S (S (S n)))) -> ev n.
Proof.
Fail firstorder congruence.
inv_principle_all; firstorder congruence.
Qed.

End small_examples.

Module solution_examples.

(* A working version of problematic examples in section 2: 
We need to add a CompDec hypothesis on the type variable as SMTCoq uses 
classical reasoning (so B should be decidable) *)

Lemma length_rev_app_cons :
forall (B: Type) (HB : CompDec B) (l l' : list B) (b : B),
length (rev (l ++ (b::l'))) =
(length l) + (length l') + 1.
Proof. snipe (app_length, rev_length). Qed.

(* sauto and SMTCoq cannot perform case analysis in general *)
Lemma app_nilI : forall B (HB : CompDec B) (l1 l2 : list B),
l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof. snipe. Qed.

(* trakt translates the goal in Z and the SMT solver verit from the SMTCoq plugin
is then able to prove it *)
Lemma enat : forall (x : nat), ~ (x + 1 = 0)%nat.
Proof. trakt Z bool; verit. Qed.

Import small_examples.

Import all_ssreflect all_algebra.
Import ssrZ zify_algebra.
Import AlgebraZifyInstances. 

(* TODO find the right trakt's lemmas *)

Lemma Orderle_int_Zleb_equiv : forall (x y : int), (x < y)%R = (Z_of_int x <? Z_of_int y)%Z.
Proof.
  apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_int_le).
Qed.

(* SMTCoq can now reason about the mathcomp's representation of integers *)
Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. trakt Z bool. Abort.


Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. lia. Qed.

Lemma congr_int : forall (z : int),
((z + 1) :: nil = (1 + z) :: nil)%R.
Proof. trakt Z Prop. lia. Abort.

(* itauto's smt tactic is able to solve this goal*)

Lemma eintb : forall (z : int), (z + 1 == 1 + z)%R = true.
Proof. smt_itauto. Abort.

(* but it fails on this one because of the uninterpreted function f *)
Lemma eintcb : forall (f : int -> int) (z : int),
(f (z + 1) == f (1 + z))%R = true.
Proof. Fail smt_itauto. Abort.
End solution_examples.



(* For the use cases of section 4: see intervals_list.v and confluence.v in the 
same directory *)




