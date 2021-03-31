Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import definitions.
Require Import lambda_expand.
Require Import elimination_pattern_matching.


Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.

Definition min1' := min1.

Definition min1'' := min1'.

Definition min1''' := min1''.

Section Examples.

Goal True.
Proof. 
unfold_recursive_subst min1'''.
lambda_expand_fun min1.
eliminate_pattern_matching_hyp H. 
exact I.
Qed.

Goal forall A (a : A), hd a nil = a.
unfold_recursive_subst hd.
lambda_expand_fun hd.
eliminate_pattern_matching_hyp H0.




Print hd.


Goal False.
let x:= hd in run_template_program (tmQuoteRec x) (fun x => pose x).


(* Goal forall (d : bool), hd d nil = d.
intros d.
unfold_recursive_subst hd.
lambda_expand_all H. *)












Lemma list_nat_with_one_element : (forall (A  : Type) (x: A),  length (cons x nil) = 1) ->
                                           (forall (x : nat),
                                              length (cons x nil) = 1).
Proof. intros H. specialize_context; assumption. Qed. 

Lemma app_nil_r_bool : (forall (X:Type), forall l:list X,
  l ++ [] = l) -> forall l : list bool, l ++ [] = l.
Proof.
  intros X. specialize_context. assumption. Qed.


Theorem app_assoc : (forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n) -> (forall (l m n : list (nat×nat)), l ++ m ++ n = (l ++ m) ++ n).
Proof.
  intros H. specialize_context. assumption. Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
intros X l1 l2. induction l1. 
- simpl. easy.
- simpl. rewrite IHl1. easy. Qed.


Lemma app_length_bool : forall (l1 l2 : list bool), length (l1 ++ l2) = length l1 + length l2.
Proof.
instanciate_type app_length. assumption.
Qed.


Local Open Scope Z_scope.

Hypothesis Hnat : CompDec nat.

Hypothesis length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).

Theorem length_app_auto : forall B (HB: CompDec (list B)), forall (l1 l2 l3 : list B), 
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. nat_convert. 
inst_no_parameter. verit length_app_B. Qed.

End Examples.

Section combs.

  Hypothesis append_assoc : forall A (HA:CompDec (list A)), forall (l1 l2 l3 : list A),
        eqb_of_compdec HA (l1 ++ (l2 ++ l3)) ((l1 ++ l2) ++ l3).

  Lemma comb :
    forall B (HB:CompDec (list B)) (l1 l2 l3 l4 : list B),
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof. intros. inst_no_parameter. verit (append_assoc_B HB). Qed.

End combs.
