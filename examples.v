Require Import sniper.

Local Open Scope Z_scope.


Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
Proof.
snipe.
Qed.


Section Generic.

  Variable A : Type.
  Variable HA : CompDec A.

  Goal forall (l : list A) (x : A),  hd_error l = Some x -> (l <> []).
  Proof.
    snipe.
  Qed.

End Generic.



Hypothesis length_app : forall A, forall (l1 l2: list A),
       (Z.of_nat #|l1 ++ l2| =? Z.of_nat #|l1| + Z.of_nat #|l2|).

Lemma length_app_auto : forall B (HB: CompDec B), forall (l1 l2 l3 : list B),
((length (l1 ++ l2 ++ l3)) =? (length l1 + length l2 + length l3))%nat.
Proof. intros B HB l1 l2 l3. snipe length_app. Qed.





Definition remove_option {A} (default : A) (o : option A) := match o with 
| Some x => x
| None => default
end.



Fixpoint search {A : Type} {H: CompDec A} (x : A) l := 
  match l with 
  | [] => false
  | x0 :: l0 => if @eqb_of_compdec _ H x x0  then true else search x l0
  end.

Lemma search_app : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A), search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
intros A H x l1 l2. induction l1 as [ | x0 l0 IH]. 
- reflexivity.
- simpl. destruct (@eqb_of_compdec _ H x x0). 
  + reflexivity.
  + rewrite IH. reflexivity. 
Qed.



Lemma search_app_snipe : forall {A: Type} {H : CompDec A} (x: A) (l1 l2: list A), search x (l1 ++ l2) = ((search x l1) || (search x l2))%bool.
Proof.
intros A H x l1 l2. induction l1 as [ | x0 l0 IH]. 
- snipe.
- simpl. destruct (@eqb_of_compdec _ H x x0). 
 + snipe.
 + snipe.
Qed.





Lemma search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A), search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof.
intros A H x l1 l2 l3.  rewrite !search_app.  rewrite Coq.Bool.Bool.orb_comm with (b1 := search x l3). rewrite Coq.Bool.Bool.orb_comm  with (b1 := search x l2) (b2 := search x l1 ). rewrite  Coq.Bool.Bool.orb_assoc. reflexivity.
Qed.


Lemma snipe_search_lemma : forall (A : Type) (H : CompDec A) (x: A) (l1 l2 l3: list A), 
search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
Proof. intros A H. snipe @search_app. Qed.



Lemma option_tree_Z : forall (t : @tree Z), 
is_empty t = true -> t = Leaf.
Proof.
intro t ; case t. 
- snipe. admit. admit. admit.
- scope. 
(* verit. => trop de compdec*)
Abort.

Local Open Scope nat_scope.

Goal forall (x y z : nat), y = S x /\ z = 0 -> max y z = y.
Proof.

Abort.

(*Exemple avec une induction qui passe bien *)
Lemma app_nil_r : forall (A: Type) (H: CompDec A) (l:list A), (l ++ [])%list = l.
Proof. intros A H. induction l.
- snipe.
- snipe. 
Qed. 



(* Lemma rev_app_distr : forall (A : Type) (H : CompDec A) (x y: list A), List.rev (x ++ y)%list = (List.rev y ++ List.rev x)%list.
Proof. intros A. induction x.
- snipe @app_nil_r. *)



(* forall l, (exists x, (hd_error l = Some x)) -> negb (l ====? nil) .
Proof.
intros. destruct H.
apply triple_eq_is_eq in H. 
verit  hd_error_def_nil  some_neq_none cons_neq_nil H   (* cons_neq_nil is necessary *).   
Qed.*)
