Require Import Scope.
Require Import List.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

From SMTCoq Require Import SMTCoq.

Section tests_for_decidable_relations.

Variable (A : Type).
Variable (HA : CompDec A).

Fixpoint smaller_dec_bis (l l' : list A) :=
match l with
| nil => true
| cons x xs => false 
end
|| 
match l with
| nil => false
| cons x xs => match l' with
          | nil => false
          | cons x' xs' => smaller_dec_bis xs xs'
end
end.

Goal forall (l l' l'' : list A) (x : A), 
smaller_dec_bis l l' -> l' = [] -> l <> cons x l''.
Proof. scope; verit. Qed.

End tests_for_decidable_relations.

Section tests.

Definition true_hidden := true.
Definition definition_no_variables := if true_hidden then 1=1 else 2=2.

Goal definition_no_variables -> True.
scope.
Abort.


Lemma nth_default_eq :
    forall (A : Type) (HA : CompDec A) n l (d:A), nth_default d l n = nth n l d.
Proof. intros A HA n ; induction n.  
  - intros; scope. verit.
  - intros l ; destruct l.
    * scope; verit.
    * scope. (* get_projs_st option. specialize (gen_option A d). *)
      (* verit does not succed because p and p0 are not Zified by trakt (see "Preprocessing" channel *)
Abort.

(* Test projs, two versions *)
Variable A : Type.
Variable a : A.

Variable HA : CompDec A.

Definition search := 
fix search {A : Type} {H : CompDec A} (x : A) (l : list A) {struct l} : bool :=
  match l with
  | [] => false
  | x0 :: l0 => orb (eqb_of_compdec H x x0) (search x l0)
  end.

Local Open Scope list_scope. 

Lemma search_append_neq : 
forall l1 l2 l3 x, search x (l1 ++ l2) <> search x l3 -> l1 ++ l2 <> l3.
Proof. 
Time scope; verit. Qed.


Open Scope list_scope.

Import ListNotations.
  Variable a_0 : A.

  (** The boolean In *)
  Fixpoint Inb (a:A) (l:list A) : bool :=
    match l with
      | [] => false
      | b :: m => orb (eqb_of_compdec HA a b) (Inb a m)
    end.

  Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof. scope; verit.
  Qed.

  Lemma hd_error_tl_repr : forall l (a:A) r,
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  intros; scope; verit.
 Qed.

 Lemma hd_error_some_nil : forall l (a:A), hd_error l = Some a -> l <> nil.
  Proof. 
  intros; scope; verit.
  Qed.

Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
  intros; scope; verit.
  Qed. 


  Theorem in_eq  : forall (a:A) (l:list A), Inb a (a :: l) = true.
  Proof.
  intros; scope2; verit. (* TODO intros; scope; verit *) 
  Qed.

  Theorem in_cons : forall (a b:A) (l:list A), Inb b l = true -> Inb b (a :: l) = true.
  Proof.
  intros; scope2; verit. (* TODO intros; scope; verit *) 
  Qed.

  Theorem not_in_cons (x b : A) (l : list A):
    ~ Inb x (a::l) = true <-> x<>a /\ ~ Inb x l = true.
  Proof.
  intros; scope2; verit.
  Qed.

  Theorem in_nil : forall a:A, ~ Inb a nil.
  Proof.
  intros; scope2; verit. 
  Qed.

  Lemma in_inv : forall (a b:A) (l:list A), Inb b (a :: l) -> a = b \/ Inb b l.
  Proof.
  intros; scope2; verit.
  Qed.

  Theorem app_cons_not_nil : forall (x y:list A) (a:A), nil <> ((a :: y) ++ x).
  Proof.
  intros; scope2; verit.
  Qed.

  Theorem app_nil_l : forall l:list A, [] ++ l = l.
  Proof.
  intros; scope2; verit. 
  Qed.

  Theorem app_nil_r : forall l:list A, l ++ [] = l.
  Proof.
  induction l ; scope; verit.
  Qed.

  Theorem app_nil_end : forall (l:list A), l = l ++ [].
  Proof. pose proof app_nil_r. scope; verit. Qed.

  Theorem app_assoc : forall l m n:list A, (l ++ m ++ n) = ((l ++ m) ++ n).
  Proof.
    Time intros l ; induction l ; scope; verit. 
  Qed. 

  Theorem app_assoc_reverse : forall l m n:list A, ((l ++ m) ++ n) = (l ++ m ++ n).
  Proof.
     pose proof app_assoc; scope; verit. Qed.

  Theorem app_comm_cons : forall (x y:list A) (a:A), (a :: (x ++ y)) = ((a :: x) ++ y).
  Proof.
  intros ; scope; verit.
  Qed.

  Theorem app_eq_nil' : forall l l':list A, 
(l ++ l') = nil -> l = nil /\ l' = nil.
  Proof. 
  intros ; scope; verit. Qed.

   Theorem app_eq_unit :
    forall (x y:list A) (a:A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.
  Proof.
  intros ; scope; verit. Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), Inb a (l ++ m) -> or (Inb a l) (Inb a m).
  Proof.
    intros l m b. Time induction l; scope; verit. 
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    Time induction l ; scope; verit.  Qed.

End tests.

Section Pairs.
 Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

  Definition fst (p:A * B) := match p with (x, y) => x end.
  Definition snd (p:A * B) := match p with (x, y) => y end.

Lemma surjective_pairing :
  forall (p:A * B), p = (fst p, snd p).
Proof. intros; scope; verit. Qed.

End Pairs.


