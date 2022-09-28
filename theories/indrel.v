From MetaCoq Require Import All.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Require Import utilities.
Require Import List.
Require Import String.

(** Examples for testing inductive relations **)

Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

Inductive Add {A : Type} (a : A) : list A -> list A -> Prop :=
  | Add_head : forall l : list A, Add a l (a :: l)
  | Add_cons : forall (x : A) (l l' : list A),
               Add a l l' -> Add a (x :: l) (x :: l').

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

(** Example to understand the transformation *)

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

Definition get_ind_and_instance (I : term) :=
match I with
| tInd indu inst => (indu, inst)
| _ => ({|
           inductive_mind :=
             (MPfile ["utilities"%bs; "theories"%bs; "Sniper"%bs], "default"%bs);
           inductive_ind := 0
         |}, [])
end.

(* Compute get_constructors_inductive add_reif_rec.2 add_reif_rec.1.  *)(* TODO : make this work for mutuals *)

Ltac assert_list_constructors_aux l I I_reif i n :=
lazymatch l with
| nil => idtac
| cons ?cbody ?cbodys => let t := eval cbv in (subst10 I_reif (cstr_type cbody)) in
               let t' := metacoq_get_value (tmUnquote t) in
               let TyC := eval cbv in t'.(my_projT2) in 
               let c := metacoq_get_value (tmUnquoteTyped TyC (tConstruct I n i)) in
               let H := fresh c in
               pose proof (H := c) ; assert_list_constructors_aux cbodys I I_reif i (S n)
end.

Ltac assert_list_constructors l I I_reif i := assert_list_constructors_aux l I I_reif i 0.
 
Ltac assert_types_constructors I := 
let I_reif_rec := metacoq_get_value (tmQuoteRec I) in 
let I_reif := eval cbv in I_reif_rec.2 in 
let list_construct := eval cbv in (info_nonmutual_inductive I_reif_rec.1 I_reif).2 in
let p := eval cbv in (get_ind_and_instance I_reif) in
let indu := eval cbv in p.1 in
let inst := eval cbv in p.2 in
assert_list_constructors list_construct indu I_reif inst.

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

Ltac intros_n n :=
match n with
| 0 => idtac
| S ?n' => let H := fresh in intro H ; intros_n n'
end.

Ltac infer_nb_vars T npars := 
let n := fresh "n" in let _ := match goal with _ => 
epose (?[n] : nat) ;
let Hfalse := fresh "Hfalse" in
assert (Hfalse : False -> T) by (let Hf := fresh in intro Hf ;  intros_n npars ; 
(
let rec tac_rec k := tryif (let H := fresh "H" in intro H ; 
match goal with
| |- context C[H] => idtac end ) 
(* checks if the new variable is used in the goal, otherwise it is a non-dependent product *)
then
(tac_rec (S k)) else (instantiate (n := k))
in tac_rec constr:(0)) ; destruct Hf) ; clear Hfalse end in let u := eval unfold n in n in u.

Goal False.
let x := 
infer_nb_vars (forall n m k, add (S n) m k -> add n m k) 0 in pose x.
let x :=
infer_nb_vars (forall n m k, add n m k) 0 in pose x. 
let x :=
infer_nb_vars (forall n k, 1 = 1 -> 2 = 2 -> add n 0 k) 0 in pose x.
let x :=
infer_nb_vars (forall (A : Type) (a : A) (l :list A), Add a l (a::l)) 2 in pose x.
Abort.


(* l2 should be the arguments of the inductive in the conclusion of 
a constructor *)
Fixpoint gen_and_eq (l1 : list term) (l2 : list term) :=
match l1, l2 with
| [x], [y] => tApp <% @eq %> [hole ; x ; y]
| x :: xs, y :: ys => tApp <% @and %> [tApp <% @eq %> [hole ; x ; y] ; gen_and_eq xs ys]
| _, _ => <%default%> (* should not happen *)
end.

Definition inv_under_binders (t : term) (npars : nat) (l1 : list term) :=
match t with
| tApp u l => let l2 := List.skipn npars l in gen_and_eq l1 l2 
| _ => <% default %> (* the conclusion is necessarily an applied inductive so we should not consider other cases *)
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

Fixpoint skipn_forall (t : term) (n : nat) : term := 
match t, n with
| tProd Na u v, S n => skipn_forall v n 
| _, _ => t
end.

Fixpoint inv_principle_one_constructor_fuel
(t: term) (npars : nat) (nb_vars : nat) (l1 : list term) (n : nat) :=
match n with
| 0 => <%default%>
| S n =>
match t, nb_vars with
| tProd na Ty u, (S n') => tApp <% ex %> [Ty ; tLambda na Ty (inv_principle_one_constructor_fuel u npars n' l1 n)]
| tProd na Ty u, 0 => tApp <% @and %> [Ty ; inv_principle_one_constructor_fuel (subst10 (tRel 0) u) npars 0 l1 n]
| t', 0 => inv_under_binders t' npars l1
| _, _ => <% default %>
end
end.

Definition inv_principle_one_constructor (Σ : PCUICProgram.global_env_map) (t : term) npars nb_vars l1 := 
let fuel := PCUICSize.size (trans Σ t) in
let nb_new_args := Datatypes.length l1 in
let t' := lift nb_new_args 0 (skipn_forall t npars) in
inv_principle_one_constructor_fuel t' npars nb_vars l1 fuel.

Fixpoint mkIff (t : term) (t' : term) :=
match t with
| tProd na Ty u => tProd na Ty (mkIff u t')
| _ => tApp <%iff%> [t ; t']
end. 

Definition inv_principle_all_constructors Σ (l_ty_cstr : list term) (npars : nat) (list_nb_vars : list nat)
(t : term) (* t is forall x1, ..., xm, I x1 ... xm *)
(l1 : list term) (* l1 is [x1 ; ... ; xm] *)  
:= 
let fix aux l_ty_cstr npars list_nb_vars l1 :=
match l_ty_cstr, list_nb_vars with
| [Ty], [nb_vars] => let l1' := (List.map (fun x => lift nb_vars 0 x) l1) in 
                       inv_principle_one_constructor Σ Ty npars nb_vars l1'
| Ty :: Tys, nb_vars:: ln => let l1' := (List.map (fun x => lift nb_vars 0 x) l1) in 
                             tApp <%or%> [inv_principle_one_constructor Σ Ty npars nb_vars l1' ; 
                             aux Tys npars ln l1]
| _, _ => <% default %> 
end
in mkIff t (aux l_ty_cstr npars list_nb_vars l1).

Fixpoint mkProd_list_ty (t : term) (T : term) :=
match T with
| tProd na Ty u  => mkProd hole (mkProd_list_ty t u)
| _ => t
end.

Definition app_to_args (I : term) (n : nat) :=
match n with
| S n' => 
let l := Rel_list n 0 in
tApp I l
| 0 => I
end.

Definition create_applied_term (t: term) (T : term) (nb_args : nat) (npars : nat)
:= 
let l := Rel_list nb_args 0 in
(mkProd_list_ty (tApp t l) T, List.skipn npars l).

Section test.

Definition c1 := <% forall n, add 0 n n %>.
Definition c2 := <% forall n m k, add n m k -> add (S n) m (S k) %>.
Definition add_app := <% forall n m k, add n m k %>.

Definition c1' := <%forall (A : Type) (a : A) (l : list A), Add a l (a :: l) %>.


Fixpoint add_prod_nat (n : nat) (t : term) :=
match n with
| 0 => t
| S n' => mkProd <% nat %> (add_prod_nat n' t)
end.

Fixpoint add_prod_hole (n : nat) (t : term) :=
match n with
| 0 => t
| S n' => mkProd hole (add_prod_hole n' t)
end.

Variable (Σ : PCUICProgram.global_env_map).

Definition test_add0 := add_prod_nat 3 (inv_principle_one_constructor Σ c1 0 1 [tRel 3 ; tRel 2 ; tRel 1]).
Definition test_addS := add_prod_nat 3 (inv_principle_one_constructor Σ c2 0 3 [tRel 5 ; tRel 4 ; tRel 3]).

Definition test_Add0 := mkProd <% Type %> 
(mkProd (tRel 0) 
(mkProd (tApp <%@list%> [tRel 1])
(mkProd (tApp <%@list%> [tRel 2]) (inv_principle_one_constructor Σ c1' 2 1 [tRel 2 ; tRel 1])))).

Unset MetaCoq Strict Unquote Universe Mode.

MetaCoq Unquote Definition test_add0_unq := test_add0.
MetaCoq Unquote Definition test_addS_unq := test_addS.


Definition goal_Add0 := <% forall (A : Type) (a : A) (l : list A)
(l' : list A), exists l'' : list A, l = l'' /\ l' = (a::l'') %>.
MetaCoq Unquote Definition test_Add0_unq := test_Add0. 

Definition test_add := 
(inv_principle_all_constructors Σ [c1 ; c2] 0 [1 ; 3] add_app [tRel 2 ; tRel 1 ; tRel 0]).

MetaCoq Unquote Definition test_add_unq := test_add.

End test.

Ltac compute_nb_vars I_reif l acc npars :=
lazymatch l with
| ?x :: ?xs => let t_unq := metacoq_get_value (tmUnquoteTyped Prop (subst10 I_reif x)) in
let n := ltac:(infer_nb_vars t_unq npars) in compute_nb_vars I_reif xs (n :: acc) npars
| [] => let acc_rev := eval cbv in (List.rev acc) in acc_rev
end.

Fixpoint compute_nb_args_reif T n :=
match T with
| tProd _ _ U => compute_nb_args_reif U (S n)
| _ => n
end.

Ltac compute_nb_args T :=
let T' := metacoq_get_value (tmQuote T) in
let nb_args := eval cbv in (compute_nb_args_reif T' 0) in nb_args. 

Ltac clear_evars n := 
lazymatch n with
| 0 => idtac 
| S ?n' => match goal with
  | [H : nat |- _]  => clear H
           end ; clear_evars n'
end.

Ltac right_or_left_auto :=
first [left ; repeat eexists ; subst ; auto ; reflexivity | 
right ; first [right_or_left_auto | repeat eexists ; subst ; auto ] ].

Ltac destruct_or :=
match goal with
| [H: ?A\/?B |- _] => destruct H
end.

Ltac destruct_exists :=
match goal with
| [H: exists x, ?H' |- _] => destruct H
end.

Ltac destruct_and :=
match goal with
| [H: ?A/\?B |- _] => destruct H
end.


Goal forall H0 H1 H2 : nat,
add H0 H1 H2 <->
(exists n0 : nat, H0 = 0 /\ H1 = n0 /\ H2 = n0) \/
(exists n0 m k : nat,
   add n0 m k /\ H0 = S n0 /\ H1 = m /\ H2 = S k).
Proof.
intros; split ; 
[intro H; inversion H; right_or_left_auto | 
intros; repeat destruct_or; repeat destruct_exists; repeat destruct_and; subst; constructor; try assumption].
Qed.


Ltac prove_inv_principle_auto :=
intros; split ; 
[let H:= fresh in intro H; inversion H; right_or_left_auto | 
intros; repeat destruct_or; repeat destruct_exists; repeat destruct_and; subst; constructor; try assumption].

Ltac inversion_principle I := 
let I_reif_rec := metacoq_get_value (tmQuoteRec I) in 
let I_reif := eval cbv in I_reif_rec.2 in 
let genv := eval cbv in I_reif_rec.1 in
let Σ := eval cbv in (trans_global_env genv) in
let T := type of I in 
let T_reif := metacoq_get_value (tmQuote T) in
let npars := eval cbv in (info_nonmutual_inductive I_reif_rec.1 I_reif).1 in
let nb_args := compute_nb_args T in 
let list_construct := eval cbv in (info_nonmutual_inductive I_reif_rec.1 I_reif).2 in 
let I_reif_app := eval cbv in (app_to_args I_reif npars) in
let list_constr := eval cbv in (get_type_constructors list_construct) in 
let l := ltac:(compute_nb_vars I_reif list_constr (@nil nat) npars) in 
let p := eval cbv in (get_ind_and_instance I_reif) in
let indu := eval cbv in p.1 in
let inst := eval cbv in p.2 in
assert_list_constructors list_construct indu I_reif inst ;
let len := eval cbv in (Datatypes.length l) in 
clear_evars len ;  
let p := eval cbv in (create_applied_term I_reif T_reif nb_args npars) in 
let t := eval cbv in p.1 in 
let l1 := eval cbv in p.2 in
let inv_principle_reif := eval cbv in
(inv_principle_all_constructors Σ (List.map (fun x => subst10 I_reif x) list_constr) npars l t l1) in
let inv_principle := metacoq_get_value (tmUnquoteTyped Prop inv_principle_reif)
in let H := fresh "Hinv" in assert (H : inv_principle) by (prove_inv_principle_auto).

Goal False -> forall (n: nat), False. intros H n.
inversion_principle add.
inversion_principle @Add.
clear.
inversion_principle @Forall.
inversion_principle @Exists.
clear.
inversion_principle le.
Abort.

Ltac first_arg_not_in_prop T :=
let U := type of T in 
lazymatch U with
| forall (x : Prop), _ => fail 
| _ => idtac
end.

Ltac inversion_principle_all_subterms p := 
 match goal with 
| |- context C[?x] => is_not_in_tuple p x ; first_arg_not_in_prop x; 
inversion_principle x ; inversion_principle_all_subterms (p, x) 
| _ : context C[?x] |- _ => is_not_in_tuple p x ; first_arg_not_in_prop x;
inversion_principle x ; inversion_principle_all_subterms (p, x)
| _ => idtac
end.

Goal forall (A: Type) (a : A) (n : nat), add 0 n n -> forall (l l' : list A), Add a l l' -> 
le n n.
Proof.
intros.
inversion_principle_all_subterms default.
Abort.

Ltac inv_principle_all := inversion_principle_all_subterms 
(False, True).

Goal forall (A: Type) (a : A) (n : nat), add 0 n n -> forall (l l' : list A), Add a l l' -> 
le n n.
Proof.
intros.
inv_principle_all.
Abort.
