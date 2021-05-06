Require Import sniper.
Require Import tree.
Require Import Bool.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.


(** Examples on lists *)

(* A simple example *)
Goal forall (l : list Z) (x : Z), hd_error l = Some x -> (l <> []).
Proof. snipe. Qed.


(* The same, on any type who enjoys a decidable equality *)
Section Generic.

  Variable A : Type.
  Variable HA : CompDec A.

  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> []).
  Proof. snipe. Qed.

End Generic.


(* An example with polymorphism *)
Lemma length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).
Proof.
intros A l1 l2.
apply Z.eqb_eq.
induction l1.
- reflexivity.
- simpl length.
  rewrite !Nat2Z.inj_succ.
  rewrite IHl1.
  rewrite Z.add_succ_l.
  reflexivity.
Qed.

Lemma length_app_auto : forall B (HB: CompDec B), forall (l1 l2 l3 : list B),
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. snipe length_app. Qed.


(* Example of search an element in a list *)
Fixpoint search {A : Type} {H: CompDec A} (x : A) l :=
  match l with
  | [] => false
  | x0 :: l0 => @eqb_of_compdec _ H x x0 || search x l0
  end.

Lemma search_app : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
  intros A H x l1 l2. induction l1 as [ | x0 l0 IH].
  - reflexivity.
  - simpl. destruct (@eqb_of_compdec _ H x x0).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* The proof of this lemma, except induction, can be automatized *)
Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A),
    search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof. intros A H x l1 l2. induction l1 as [ | x0 l0 IH]; simpl; snipe. Qed.


(* Manually using this lemma *)
Lemma search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
    search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
  intros A H x l1 l2 l3. rewrite !search_app.
  rewrite Coq.Bool.Bool.orb_comm with (b1 := search x l3).
  rewrite Coq.Bool.Bool.orb_comm  with (b1 := search x l2) (b2 := search x l1 ).
  rewrite  Coq.Bool.Bool.orb_assoc.
  reflexivity.
Qed.


(* It can be fully automatized *)
Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A),
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. intros A H. snipe @search_app. Qed.


(* Another example with an induction *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros A H; induction l; snipe. Qed.


(** Examples on trees *)

Lemma empty_tree_Z2 : forall (t : @tree Z) a t' b,
is_empty t = true -> t <> Node a t' b.
Proof. intros t a t' b; snipe. Qed.




(*  Lemma in_inv : forall (A: Type) (HA : CompDec A) (a b:A) (l:list A), search b (a :: l) -> (eqb_of_compdec HA a b || search b l).
Proof. intros A HA. snipe. *)



(*
Lemma empty_tree_Z : forall (t : @tree Z),
is_empty t = true -> t = Leaf.
Proof.
intro t ; case t.
- snipe.
- scope. revert H. verit.
Qed.
*)

(* Check rev_elements_aux.

Ltac def_fix_and_pattern_matching' :=
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' =>
eliminate_fix_ho H' ltac:(fun H'' => try
(eliminate_pattern_matching H'')))).

Lemma rev_elements_app :
 forall A s acc, tree.rev_elements_aux A acc s = ((tree.rev_elements A s) ++ acc)%list.
Proof. intros A s acc. induction acc.
- def_fix_and_pattern_matching'. inst.




Lemma rev_elements_node c l x r :
 rev_elements c (Node c l x r) = (rev_elements c r ++ x :: rev_elements c l)%list.
Proof. destruct r.
-  verit. *)
