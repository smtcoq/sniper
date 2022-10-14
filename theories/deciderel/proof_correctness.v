From MetaCoq.PCUIC Require Import PCUICReflect.
From MetaCoq Require Import All. 
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.Template Require Import utils All.
Import MCMonadNotation.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import SMT_classes.
Require Import SMT_classes_instances.
Require Import generate_fix.
From Ltac2 Require Import Ltac2.
Unset MetaCoq Strict Unquote Universe Mode.

(** Automatic generation of the statement
which asserts that I_decidable is sound and complete wrt I :
forall x1 .. xn, I x1 ... xn <-> I_decidable x1 ... xn = true **) 

Definition get_type_nonmutual_inductive (e : global_env) (i : term) :=
let res := info_inductive e i in
match res with
| Some mind => let body := hd default_body mind.(ind_bodies) in 
               ind_type body
| None => default_reif
end.

(* if t is forall (x1 : T1) ... (xn : Tn), ..., 
returns [(name x1, T1); ... ; (name xn, Tn)] *)
Fixpoint get_list_of_args (t : term) :=
match t with
| tProd na Ty t' => (na, Ty) :: get_list_of_args t'
| _ => []
end.


Compute (get_list_of_args (get_type_nonmutual_inductive Add_reif_rec.1 Add_reif_rec.2)).

Definition mkIff (t1 t2 : term) :=
tApp <% iff %> [t1 ; t2].

Definition tmp (t1 t2 : term) :=
tProd mknAnon t1 t2.

Fixpoint build_list_of_vars (n : nat) :=
match n with
| 0 => []
| S n' => tRel n' :: build_list_of_vars n' 
end.

Definition correctness_statement (e: global_env) (I : term) (I_dec : term) :=
let args := get_list_of_args (get_type_nonmutual_inductive e I) in
let nb_args := Datatypes.length args in
let lrel :=  build_list_of_vars nb_args in
let fix aux lrel I I_dec args :=
match args with
| (na, T) :: args' => tProd na T (aux lrel I I_dec args')
| [] => mkIff (tApp I lrel) ((tApp <%@eq%> [<% bool %>; (tApp I_dec lrel) ; <% true %>]))
end in aux lrel I I_dec args. 

(** Tests **)

MetaCoq Unquote Definition correctness_test := 
(correctness_statement even_reif_rec.1 even_reif_rec.2 <%even_decidable%>). Print correctness_test.
MetaCoq Unquote Definition correctness_test' := 
(correctness_statement Add_linear_rec.1 Add_linear_rec.2 <%Add_decidable%>).

Print correctness_test.

Print correctness_test'.

(** Proofs **)


From Ltac2 Require Import Ltac2.

Ltac2 Eval Control.hyps.

Ltac2 Type exn ::= [ Not_an_application ].
Ltac2 Type exn ::= [ Not_a_product ].
Ltac2 Type exn ::= [ Wrong_Ltac1_argument ].
Ltac2 Type exn ::= [ Empty ].

Ltac2 get_head_exn (c : constr) :=
let k := Constr.Unsafe.kind c in 
match k with
| Constr.Unsafe.App c1 carr => c1 
| _ => Control.throw Not_an_application
end.

Ltac2 get_head (c : constr) :=
let k := Constr.Unsafe.kind c in 
match k with
| Constr.Unsafe.App c1 carr => c1 
| _ => c
end.

(* Returns true whenever the term 
considered is an inductive or an 
inductive applied of type Set or Type *) 
Ltac2 is_inductive_or_inductive_applied (t : constr) :=
let ty := Constr.type t in 
if Constr.equal ty 'Prop then false
else
let rec aux t :=
let k := Constr.Unsafe.kind t in
match k with
| Constr.Unsafe.App c' arr => aux c'
| Constr.Unsafe.Ind indu inst => true
| _ => false
end in aux t.

Ltac2 rec list_constr_printer (l : constr list) :=
match l with
| [] => ()
| x :: xs => Message.print (Message.of_constr x) ; list_constr_printer xs
end.

Ltac2 rec list_ident_printer (l : ident list) :=
match l with
| [] => ()
| x :: xs => Message.print (Message.of_ident x) ; list_ident_printer xs
end.

Ltac2 rec hyps_printer (h : (ident * constr option * constr) list) 
:=
match h with
| [] => ()
| x :: xs => match x with
            | (id, opt, cstr) => 
let () := Message.print (Message.concat (Message.of_ident id)
                                        (Message.concat (Message.of_string " : ")
                                                        (Message.of_constr cstr))) 
in hyps_printer xs
end 
end.


(* The tactic takes a term I x1 ... xn, and ignore its k first arguments because they are parameters*)
 
Ltac2 rec find_destructibles (t: constr) (npars: int) :=
let k := Constr.Unsafe.kind t in
match k with
| Constr.Unsafe.App c1 arr => let l := Array.to_list arr in 
let l' := 
List.skipn npars l in (* list_constr_printer l'; *) l'
| _ => []
end.

(* return all the hypothesis which are of type c, forall c in l *)
Ltac2 rec find_corresponding_hyps (h :  (ident * constr option * constr) list) (l : constr list) 
: (ident * constr option * constr) list :=
match h with
| [] => []
| x :: xs =>
    match x with
    | (id, opt, t) => let id' := Control.hyp id in if List.mem Constr.equal id' l then 
x :: find_corresponding_hyps xs l else find_corresponding_hyps xs l
end
end.



(* In a list of hypotheses, this tactic looks at the terms of type Prop :
they are 'rewritable' hypotheses: we will try to rewrite them later *)
Ltac2 rec find_rewritables (h : (ident * constr option * constr) list) :=
match h with
| [] => []
| x :: xs =>
    match x with
    | (id, opt, t) => let ty := Constr.type t in 
if Constr.equal ty 'Prop then id :: find_rewritables xs else find_rewritables xs
end
end.

(* Destructs blindly the first hypothesis in a list of term which 
and returns the list minus this hypothesis *)

Ltac2 blind_destruct (h : (ident * constr option * constr) list) :=
match h with
| [] => ()
| x :: xs =>
    match x with
    | (id, opt, cstr) => let y := Control.hyp id in destruct $y end
end.


Ltac2 rec blind_rewrite (h : ident list) :=
match h with
| [] => ()
| x :: xs => let y := Control.hyp x in try (rewrite $y) ; blind_rewrite xs 
end.


(* we want to prove that f_dec x1 ... xn = true, so when the goal is 
precisely f_dec x1 .. xn ) true, the following function destructs at least one of the xis 
to continue the computation of the function f_dec 
and when it is not possible anymore, it returns unit  *) 
Ltac2 rec destruct_to_continue_computation
(f : constr) (* any constr *)
(npars : int) 
:= 
simpl;
match! goal with
| [|- ?e] => let t := get_head e in if Constr.equal t f then 
                    let h := Control.hyps () in
                    let dstr := find_corresponding_hyps h (find_destructibles e npars) in 
                    match dstr with
                      | [] => ()
                      | x :: xs =>
                      blind_destruct dstr ; Control.enter (fun () => destruct_to_continue_computation f npars) 
                    end 
                    else ()
| [|- _] => ()
end.

(* we want to prove that f_dec x1 ... xn = true, so when the goal is 
precisely f_dec x1 .. xn ) true, the following function destructs at least one of the xis 
to continue the computation of the function f_dec 
and when it is not possible anymore, it tries to rewrite the hypothesis introduced by the induction  *) 
Ltac2 rec destruct_to_continue_computation_rewrite
(f_dec : constr) (* the boolean function f_dec *)
(npars : int)
(hyps_rew : ident list) (* hypothesis to rewrite *)
:= 
simpl;
match! goal with
| [|- ?e = true] => let t := get_head e in if Constr.equal t f_dec then 
                    let h := Control.hyps () in ltac1:(try assumption) ;
                    let dstr := find_corresponding_hyps h (find_destructibles e npars) in
                    blind_destruct dstr ; Control.enter (fun () => destruct_to_continue_computation_rewrite f_dec npars hyps_rew) 
                    else blind_rewrite hyps_rew
| [|- _] => blind_rewrite hyps_rew
end.

(* new_hypothesis h++h' h' returns h' *)
Ltac2 rec new_hypothesis
(h1: (ident * constr option * constr) list) 
(h2 : (ident * constr option * constr) list) := 
match h1 with
| [] => h2
| x :: xs => match h2 with
        | [] => []
        | y :: ys => new_hypothesis xs ys
      end
end.


(* hyps_minus_term returns all the hypothesis except the one which has the ident id *)
Ltac2 hyps_minus_term (h : (ident * constr option * constr) list) (id : ident)
:= 
let t := Control.hyp id in
let rec aux h id := 
match h with
| [] => []
| x :: xs => match x with
      | (id', opt, cstr) => let t' := Control.hyp id' in if Constr.equal t' t then xs 
                           else x :: aux xs t
      end
end in aux h t.

Lemma eqb_of_compdec_reflexive (A : Type) (HA : CompDec A) (a : A) :
eqb_of_compdec HA a a = true. Proof. apply compdec_eq_eqb; reflexivity. Qed.

Ltac elim_reflexive_eqb_compdec :=
repeat (rewrite -> eqb_of_compdec_reflexive).

Ltac2 completeness_auto_npars 
(f_dec : constr)
(npars : int) :=
intros *; intro H_new;
(* let fr := Fresh.fresh (Fresh.of_constr f_dec) in *)
let h := Control.hyps () in
let h1 := hyps_minus_term h @H_new in
induction H_new ;
Control.enter (fun () =>
let h2 := Control.hyps () in 
let h3 := new_hypothesis h1 h2 in
let h4 := find_rewritables h3 in
 destruct_to_continue_computation_rewrite f_dec npars h4 ; ltac1:(elim_reflexive_eqb_compdec ; try lia ; auto)).


Ltac2 rec constr_to_int (t : constr) : int :=
match! t with
| 0 => 0
| S ?t' => (Int.add (constr_to_int t') 1)
end.


(* Ltac2 completeness_auto (t: constr) (n : constr) :=
let n' := constr_to_int n in completeness_auto_npars t n'. *)



Goal forall (A : Type) (HA : CompDec A) (a : A) (x y : list A),
Add_linear A HA a x y -> Add_decidable A HA a x y = true.
Proof. completeness_auto_npars 'Add_decidable 3. Qed. 


Goal forall (n: nat), even n -> even_decidable n = true.
Proof. completeness_auto_npars 'even_decidable 0. Qed.

Ltac elim_is_true :=
repeat match goal with
| H: is_true ?x |- _ => unfold is_true in H
end.


Lemma elim_false_or (A : Prop) : A \/ true = false -> A.
Proof. intros H. destruct H as [H1 | H2]. apply H1.  inversion H2. Qed.

Lemma elim_false_or_sym (A : Prop) : A \/ false = true -> A.
Proof. intros H. destruct H as [H1 | H2]. apply H1. inversion H2. Qed.

Ltac elim_trivial_or:=
repeat match goal with
| H : ?a \/ true = false |- _ => apply elim_false_or in H
| H : ?a \/ false = true |- _ => apply elim_false_or_sym in H
end.

Ltac destruct_hyp H :=
let T := type of H in
match T with
| ?H1 \/ ?H2 => destruct H
| _ => idtac
end.

Ltac elim_and_and_or :=
repeat match goal with
| H : ?a && ?b = true |- _ => apply andb_andI in H ; destruct H
| H : ?a || ?b = true |- _ => apply orb_prop in H ; elim_trivial_or ; destruct_hyp H 
end.


Print compdec_eq_eqb.
Ltac elim_eq :=
repeat match goal with
| H : @eqb_of_compdec ?T ?HT ?x ?y = true |- _ => apply compdec_eq_eqb in H
| |- @eqb_of_compdec ?U ?HT ?x ?y = true => apply @compdec_eq_eqb with (T := U)
end.

Ltac2 rec find_nth_arg (n : int) (t: constr) :=
let k := Constr.Unsafe.kind t in 
match k with
| Constr.Unsafe.Prod bind cstr => if Int.equal n 0 then 
Constr.Binder.name bind else find_nth_arg (Int.sub n 1) cstr
| _ => Control.throw Not_a_product
end.

Ltac2 print_goal () :=
match! goal with
[ |- ?g] => Message.print (Message.of_constr g)
end.

Ltac2 rec intros_until_ident_induction (n: int) (id : ident) :=
if Int.equal n 0 then 
let t := Control.hyp id in
induction $t
else let () := intro in intros_until_ident_induction (Int.sub n 1) id.

 
Ltac2 induction_nth (n : int) :=
match! goal with
[ |- ?g] => let name := find_nth_arg n g in 
            match name with
           | None => ()
           | Some na => intros_until_ident_induction (Int.add n 1) na
          end
end.

Ltac if_contains_match_then_destruct H :=
let T := type of H in 
lazymatch T with
| match ?t with _ => _ end => try destruct t
| _ => idtac
end.

Ltac2 soundness_auto_recarg_npars
(trm : constr) 
(recarg : int)
(npars : int)
:=
induction_nth recarg; (* TODO: may need generalize dependent *) 
Control.enter (fun () => intros *; intro H_new; destruct_to_continue_computation trm npars ; 
 simpl in * ; ltac1:(try (inversion H_new) ; if_contains_match_then_destruct &H_new) ;  ltac1:(elim_is_true; elim_and_and_or; simpl in *;
elim_trivial_or ; elim_is_true ; simpl in * ; elim_eq; subst; constructor ; solve [elim_eq; auto])).

Lemma soundness_auto_Add_linear:
forall (A : Type) (HA : CompDec A) (a: A) (x y : list A),
Add_decidable A HA a x y = true -> Add_linear A HA a x y.
Proof. soundness_auto_recarg_npars 'Add_linear 3 3.
Qed.

Inductive smaller {A : Type} : list A -> list A -> Prop :=
| sm_nil : forall l, smaller nil l
| sm_cons : forall l l' x x', smaller l l' -> smaller (x :: l) (x' :: l').

Fixpoint smaller_dec {A : Type} (l l' : list A) :=
match l with
| nil => true
| cons x xs => false 
end
|| 
match l with
| nil => false
| cons x xs => match l' with
          | nil => false
          | cons x' xs' => smaller_dec xs xs'
end
end.

Lemma completeness_auto_smaller : 
forall A l l', smaller l l' -> @smaller_dec A l l' = true.
Proof. completeness_auto_npars '@smaller 1. Qed.


Lemma soundness_auto_smaller2 : 
forall A l l', smaller_dec l l' = true -> @smaller A l l'.
Proof. 
soundness_auto_recarg_npars '@smaller 1 1. Qed.

Ltac revert_all :=
repeat match goal with
| H : _ |- _ => try revert H
end.

Ltac2 correctness_auto (t: constr) (t': constr) (n : int) (m : int) :=
intros; split > [ltac1:(revert_all) ; completeness_auto_npars t' n | ltac1:(revert_all) ; soundness_auto_recarg_npars t m n].

(* Strong induction for nat *)

Require Import PeanoNat.

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros. 
    ltac1:(lia).
  Qed.

  Local Hint Resolve P0 : core.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Local Hint Resolve le_S_n: core.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    ltac1:(induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto).
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.  Print strong_induction.

Lemma soundness_ev :
forall (n : nat), even_decidable n -> even n.
Proof.
ltac1:(pose proof (H := strong_induction)).
specialize (H (fun (n : nat) => even_decidable n -> even n)).
simpl in H. apply H.
intro m.
intro H1. intro H2.
destruct m.
- constructor.
- destruct m. inversion H2. constructor.
apply H1. ltac1:(lia). inversion H2. unfold is_true. assumption. Qed.

Lemma test : forall (A : Type) (HA: CompDec A) (a : A) (l : list A) (l' : list A),
Add a l l' <-> Add_decidable A HA a l l' = true.
Proof. correctness_auto '@Add '@Add_decidable 3 3. Qed. 

Lemma soundness_auto_ev :
forall (n : nat), even_decidable n -> even n.
Proof. (*  soundness_auto '@even 0. *)

induction_nth 0. 
- intros *. intro H. destruct_to_continue_computation 'even 0. 
simpl in *. inversion H.  ltac1:(elim_is_true ; elim_and_and_or; simpl in *; elim_trivial_or; elim_is_true; simpl in *
; elim_eq; subst; constructor ; solve [elim_eq; auto]).
- 

 intros *. intro H. destruct_to_continue_computation 'even 0. 
simpl in *. inversion H; destruct n eqn:E. 
ltac1:(auto ; elim_is_true ; elim_and_and_or; simpl in *; elim_trivial_or; elim_is_true; simpl in *
; elim_eq; subst; constructor ; solve [elim_eq; auto]).
ltac1:(auto ; elim_is_true ; elim_and_and_or; simpl in *; elim_trivial_or; elim_is_true; simpl in *
; elim_eq; subst; constructor).


Abort. (* FIXME *)

(** Use of the templatemonad **) 

Ltac2 ltac1_to_constr_unsafe (input : Ltac1.t) :=
match (Ltac2.Ltac1.to_constr input) with
| None => Control.throw Wrong_Ltac1_argument 
| Some y => y
end.

(* Need to convert ltac2 tactic within ltac1 for compatibility reasons with MetaCoq *)
Tactic Notation "correctness" constr(t) constr(t') constr(n) constr(n') := 
let tac := 
ltac2:(t1 t2 n n' |- let t1' := ltac1_to_constr_unsafe t1 in
                  let t2' := ltac1_to_constr_unsafe t2 in
                  let n0 := constr_to_int (ltac1_to_constr_unsafe n) in
                  let n0' := constr_to_int (ltac1_to_constr_unsafe n') in correctness_auto t1' t2' n0 n0') in 
timeout 5 (tac t t' n n').


(* Thanks to Yannick Forster's trick, we can run Ltac from the TemplateMonad *)
MetaCoq Run (tmCurrentModPath tt >>= tmDefinition "solve_ltac_mp").

Definition solve_ltac (tac : string) {args  : Type} (a : args)  (Goal : Type) := Goal.
Existing Class solve_ltac.

Definition tmDef name {A} a := @tmDefinitionRed name (Some (unfold (solve_ltac_mp, "solve_ltac"))) A a.

(* Local definition adding a new tactic *)

Local Hint Extern 0 (solve_ltac "correctness_lemma" ?P _) => unfold solve_ltac ;
let x := eval hnf in P.1.1.1 in
let x' := eval hnf in P.1.1.2 in
let n := eval hnf in P.1.2 in
let n' := eval hnf in P.2 in
correctness x x' n n' : typeclass_instances. Print tmDefinition.
 

Definition apply_correctness_lemma {A B : Type}
(t1 : A)
(t2 : B)
(dec_lemma : Prop)
(n1 : nat)
(n2 : nat) :=
oprf <- tmInferInstance None (solve_ltac "correctness_lemma" (t1, t2, n1, n2) 
(dec_lemma)) ;;
             match oprf with
             | my_Some prf => name <- tmFreshName "decidable_proof" ;; tmDefinition name prf ;; tmMsg "Automation succeed : you can use 
the following proof term for your equivalence proof :" ;; tmPrint name
             | my_None => tmPrint "no proof found, you should prove the equivalence manually"
             end. 

MetaCoq Run (apply_correctness_lemma (@Add_linear) (@Add_decidable) 
(forall (A : Type) (HA : CompDec A) (a : A) (x y : list A),
Add_linear A HA a x y <-> Add_decidable A HA a x y = true) 3 3). 

Inductive is_integer : nat -> Prop :=
| isi0 : is_integer 0
| isiS : forall n, is_integer n -> is_integer (S n).

Definition decided_term {A: Type} 
(t : A) 
(l : list (term*term*term)) :=
res <- linearize_and_fixpoint_auto t [] ;; 
let (ty_id_fix_recarg_npars_fix_qu, initial_genv) := res : (((((A × ident) × nat) × nat) × term)
   × program) in
let (ty_id_fix_recarg_npars, fix_qu) := ty_id_fix_recarg_npars_fix_qu in
let (ty_id_fix_recarg, npars) := ty_id_fix_recarg_npars in
let (ty_id_fix, recarg) := ty_id_fix_recarg in
let (ty, id_fix) := ty_id_fix in
current <- tmCurrentModPath tt ;; 
let trm := (tConst (current, id_fix ) []) in 
tquote <- tmQuote t ;; 
fixpoint_unq_term <- tmUnquote trm ;; 
let st := correctness_statement initial_genv.1 tquote trm in 
st_unq <- tmUnquoteTyped Prop st ;; 
_ <- (@apply_correctness_lemma _ (my_projT1 fixpoint_unq_term) t (my_projT2 fixpoint_unq_term) st_unq npars recarg)
;; name_fresh <-tmFreshName "decidable_lemma" ;; 
tmLemma name_fresh st_unq ;; tmWait.

MetaCoq Run (decided_term (is_integer) []).
Next Obligation.
 exact (decidable_proof0 H). Qed.


MetaCoq Run (decided_term (member2) []). (* FIXME *) 
Next Obligation.
exact (decidable_proof1 H H0).
Qed.



