From MetaCoq Require Import All.
From MetaCoq Require Import PCUIC.PCUICSize.
Require Import utilities.
Require Import List.
Require Import String.

(** Examples for testing inductive predicates **)

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

Inductive Add {A : Type} (a : A) : list A -> list A -> Prop :=
  | Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').

Derive Inversion Add_inv with (forall n m k, add n m k) Sort Prop.

Print Add_inv.

MetaCoq Quote Recursively Definition add_reif_rec := add.

Definition add0_reif := <% add0 %>.
Definition addS_reif := <% addS %>.

Definition nil_reif := <% @nil %>.
Definition cons_reif := <% @cons %>.


MetaCoq Quote Recursively Definition Add_reif_rec := Add.

(** Transformation: we consider add as a function 
with a codomain in Prop. 
Each constructor is an equation for add.
In order to use an hypothesis of the form add n m k, we also 
generate an inversion principle: **)

Lemma inv_add : forall n m k, (add n m k <-> 
(exists (n' : nat), n = 0 /\ m = n' /\ k = n') \/
(exists (n' m' k' : nat), n = S n' /\ m = m' /\ k = (S k') /\ add n' m' k')).
Proof. 
intros n m k; split.
- intros H. inversion H ; [ left; repeat eexists ; auto | right ; repeat eexists; auto].
- intros H. destruct H as [H1 | H2].
 + destruct H1 as [n' [H11 [H12 H13]]]; subst; auto; constructor.
 + destruct H2 as [n' [m' [k' [H21 [H22 [H23 H24]]]]]]; subst; auto; constructor; assumption. Qed.

Definition ty_inv_add_reif := <% forall n m k, add n m k <->
(exists (n' : nat), n = 0 /\ m = n' /\ k = n') \/
(exists (n' m' k' : nat), n = S n' /\ m = m' /\ k = (S k') /\ add n' m' k') %>.


(** Generation of the equations **)


(* Definition for default value *)
Definition impossible_term_indu := 
{|
    inductive_mind :=
      (MPfile
         ["utilities"%string; "theories"%string; "Sniper"%string],
      "impossible_term"%string);
    inductive_ind := 0
  |}.

Definition get_ind_and_instance (I : term) :=
match I with
| tInd indu inst => (indu, inst)
| _ => (impossible_term_indu, [])
end.

Compute get_constructors_inductive add_reif_rec.2 add_reif_rec.1. (* TODO : make this work for mutuals *)

Ltac assert_list_constructors_aux l I I_reif i n :=
lazymatch l with
| nil => idtac
| cons ?p ?ps => let t := eval cbv in (subst10 I_reif p.1.2) in
               let t' := metacoq_get_value (tmUnquote t) in
               let TyC := eval cbv in t'.(my_projT2) in 
               let c := metacoq_get_value (tmUnquoteTyped TyC (tConstruct I n i)) in
               let H := fresh c in
               pose proof (H := c) ; assert_list_constructors_aux ps I I_reif i (S n)
end.

Ltac assert_list_constructors l I I_reif i := assert_list_constructors_aux l I I_reif i 0.
 
Ltac assert_types_constructors I := 
let I_reif_rec := metacoq_get_value (tmQuoteRec I) in 
let I_reif := eval cbv in I_reif_rec.2 in 
let list_constr_opt := eval cbv in (get_constructors_inductive I_reif I_reif_rec.1) in 
lazymatch list_constr_opt with
| Some ?list_constr =>
let p := eval cbv in (get_ind_and_instance I_reif) in
let indu := eval cbv in p.1 in
let inst := eval cbv in p.2 in
assert_list_constructors list_constr indu I_reif inst
| None => fail "wrong argument"
end.

Goal False.
assert_types_constructors add.
assert_types_constructors @Add.
clear. 
Abort.

Fixpoint currify (t: term) :=
match t with
| tApp (tApp u l1) l2 => let u' := currify u in tApp u' (app l1 l2)
| _ => t
end.

Definition find_args (t: term) (npars : nat) :=
let t' := currify t in
match t' with
| tApp u l => Some (List.skipn npars l)
| _ => None
end.


(* We need to compute the number of existential quantifiers 
that we want to introduce.
Our criterion is to quantify existentially on all the variables which are
binded by a dependent product 
(so used somwhere in the term after their introduction), and stop whenever we 
meet a non-dependent product *)

Ltac infer_nb_vars T := 
let n := fresh "n" in 
epose (n := ?[n_evar] : nat) ;
let Hfalse := fresh "Hfalse" in
assert (Hfalse : False -> T) by 
(let Hf := fresh in intro Hf ; 
let rec tac_rec k := tryif (let H := fresh "H" in intro H ; 
match goal with
| |- context C[H] => idtac end ) 
(* checks if the new variable is used in the goal, otherwise it is a non-dependent product *)
then
(tac_rec (S k)) else (instantiate (n_evar := k)) 
in tac_rec constr:(0) ;  destruct Hf) ; clear Hfalse.

Goal False.
infer_nb_vars (forall n m k, add (S n) m k -> add n m k).
infer_nb_vars (forall n m k, add n m k).
infer_nb_vars (forall n k, 1=1 -> 2=2 -> add n 0 k).
Abort.


(* l2 should be the arguments of the inductive in the conclusion of 
a constructor *)
Fixpoint gen_and_eq (l1 : list term) (l2 : list term) :=
match l1, l2 with
| [x], [y] => tApp <% @eq %> [hole ; x ; y]
| x :: xs, y :: ys => tApp <% @and %> [tApp <% @eq %> [hole ; x ; y] ; gen_and_eq xs ys]
| _, _ => impossible_term_reif (* should not happen *)
end.

Definition inv_under_binders (t : term) (npars : nat) (l1 : list term) :=
match t with
| tApp u l => let l2 := List.skipn npars l in gen_and_eq l1 l2 (* TODO : lift parameters *)
| _ => impossible_term_reif (* the conclusion is necessarily an applied inductive so we should not consider other cases *)
end.

(* Ltac unfold_subst := unfold subst10; unfold subst0.

Lemma subst_a_variable_does_not_change_size (n : nat) (t : term) : 
size (subst10 (tRel n) t) = size t.
Proof.
generalize dependent n ; 
induction t ; intros.
- destruct (PeanoNat.Nat.leb 0 n) eqn:E.
unfold_subst. rewrite E. simpl. destruct n; simpl; auto. 
destruct n; simpl; auto.
unfold_subst. rewrite E. reflexivity.
- unfold_subst; reflexivity.
- Print subst.
Admitted. (* TODO : better induction principles for term *)

Program Fixpoint inv_principle_one_constructor 
(t: term) (npars : nat) (nb_vars : nat) (l1 : list term) {measure (size t)} :=
match t, nb_vars with
| tProd na Ty u, (S n') => tApp <% ex %> [Ty ; tLambda na Ty (inv_principle_one_constructor u npars n' l1)]
| tProd na Ty u, 0 => tApp <% @and %> [Ty ; inv_principle_one_constructor (subst10 (tRel 0) u) npars 0 l1]
| t', 0 => inv_under_binders t' npars l1
| _, _ => impossible_term_reif
end.
Next Obligation.
apply Lt.le_lt_n_Sm. assert (H :  size Ty + size u = size u + size Ty).
apply PeanoNat.Nat.add_comm. rewrite H. eapply PeanoNat.Nat.le_add_r. Defined. 
Next Obligation. rewrite subst_a_variable_does_not_change_size. 
apply Lt.le_lt_n_Sm. assert (H :  size Ty + size u = size u + size Ty).
apply PeanoNat.Nat.add_comm. rewrite H. eapply PeanoNat.Nat.le_add_r. Defined.
Next Obligation. unfold "~"; split. intros na Ty u. intros H1;
destruct H1 as [H2 H3]; discriminate H2.
split. intros t'. intros H1 ; 
destruct H1 as [H2 H3]. discriminate H3.
intros na Ty u n' H1. destruct H1 as [H2 H3]. discriminate H2. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1 ; destruct H1 as [H2 H3]. discriminate H3.
split.
intros t'. intros H1 ; destruct H1 as [H2 H3]. discriminate H3.
intros na Ty u n H1; destruct H1 as [H2 H3]. discriminate H2. Defined.
Next Obligation. 
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2 H3]. discriminate H3.
split.
intros t'. intros H1' ; destruct H1' as [H2 H3]. discriminate H3.
intros na Ty u n H1' ; destruct H1' as [H2 H3]. discriminate H2. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1 ; destruct H1 as [H2 H3]. discriminate H3.
split.
intros t'. intros H1 ; destruct H1 as [H2 H3]. discriminate H3.
intros na Ty u n H1; destruct H1 as [H2 H3]. discriminate H2. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3]. discriminate H3.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3]. discriminate H3.
intros na Ty u n H1' ; destruct H1' as [H2' H3]. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3]. discriminate H3.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3]. discriminate H3.
intros na Ty u n H1' ; destruct H1' as [H2' H3]. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n' H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
unfold "~"; split. intros na Ty u H1' ; destruct H1' as [H2' H3']. discriminate H3'.
split.
intros t'. intros H1' ; destruct H1' as [H2' H3']. discriminate H3'.
intros na Ty u n H1' ; destruct H1' as [H2' H3']. discriminate H2'. Defined.
Next Obligation.
apply Acc_intro. unfold Wf.MR. intros.

 Admitted. *)

Fixpoint inv_principle_one_constructor_fuel
(t: term) (npars : nat) (nb_vars : nat) (l1 : list term) (n : nat) :=
match n with
| 0 => impossible_term_reif
| S n =>
match t, nb_vars with
| tProd na Ty u, (S n') => tApp <% ex %> [Ty ; tLambda na Ty (inv_principle_one_constructor_fuel u npars n' l1 n)]
| tProd na Ty u, 0 => tApp <% @and %> [Ty ; inv_principle_one_constructor_fuel (subst10 (tRel 0) u) npars 0 l1 n]
| t', 0 => inv_under_binders t' npars l1
| _, _ => impossible_term_reif
end
end.

Definition inv_principle_one_constructor t npars nb_vars l1 := 
let fuel := size t in
inv_principle_one_constructor_fuel t npars nb_vars l1 fuel.

Fixpoint mkIff (t : term) (t' : term) :=
match t with
| tProd na Ty u => tProd na Ty (mkIff u t')
| _ => tApp <%iff%> [t ; t']
end. 

Definition inv_principle_all_constructors (l_ty_cstr : list term) (npars : nat) (list_nb_vars : list nat)
(t : term) (* t is forall x1, ..., xm, I x1 ... xm *)
(l1 : list term) (* l1 is [x1 ; ... ; xm] *)  
:= 
let fix aux l_ty_cstr npars list_nb_vars l1 :=
match l_ty_cstr, list_nb_vars with
| [Ty], [nb_vars] => let l1' := (List.map (fun x => lift nb_vars 0 x) l1) in 
                       inv_principle_one_constructor Ty npars nb_vars l1'
| Ty :: Tys, nb_vars:: ln => let l1' := (List.map (fun x => lift nb_vars 0 x) l1) in 
                             tApp <%or%> [inv_principle_one_constructor Ty npars nb_vars l1' ; 
                             aux Tys npars ln l1]
| _, _ => impossible_term_reif 
end
in mkIff t (aux l_ty_cstr npars list_nb_vars l1).

Section test.

Definition c1 := <% forall n, add 0 n n %>.
Definition c2 := <% forall n m k, add n m k -> add (S n) m (S k) %>.

Fixpoint add_prod_nat (n : nat) (t : term) :=
match n with
| 0 => t
| S n' => mkProd <% nat %> (add_prod_nat n' t)
end.

Definition test_add0 := add_prod_nat 3 (inv_principle_one_constructor c1 0 1 [tRel 3 ; tRel 2 ; tRel 1]).
Definition test_addS := add_prod_nat 3 (inv_principle_one_constructor c2 0 3 [tRel 5 ; tRel 4 ; tRel 3]).

MetaCoq Unquote Definition test_add0_unq := test_add0.
MetaCoq Unquote Definition test_addS_unq := test_addS.

End test.













