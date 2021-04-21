Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.
From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import List String.  
Require Import elimination_polymorphism.
Require Import ZArith.
Require Import definitions.


Open Scope string_scope.  (* pour que ça ne buggue pas avec les fonctions sur les strings, mais du coup, ++ plus interprété pour les listes *)

Import ListNotations MonadNotation. 

(* in newTacs.v, a lot of remarks about Ltac !!!!*)

(* Playing with inductive types *)

(* ci-dessous, vient de add_constructor.v dans depot-metacoq. \Q Comment faire pour importer directement ? *)

(* \todo avoir des fonctions permettant de définir plus robustement les variables terminant en indu, mind, oind *)

(* \todo des tactiques qui permettent d'extraire les indu, les mind, les oind ... *) 

(*** Pour quote_term ***)

(* src/quoter *)

Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).

Goal False.
  pose_quote_term nat nat_reif.
Abort.  

Print term.




Ltac unquote_type t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e t.

Ltac unquote_type0 t idn := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) .

Ltac unquote_type1 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e idn . (* même effet que unquote_type *)

Ltac unquote_type2 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e . (* idem que unquote_type *)

Ltac cbv1 t := eval cbv in t.

Ltac unquote_type_cbv' t idn :=  unquote_type t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv t idn :=  unquote_type t idn cbv1. 

Ltac unquote_type_cbv1 t idn := unquote_type1 t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv2 t idn := unquote_type2 t idn ltac:(cbn in idn).
 
Goal 2 + 2 = 4.
Proof.
  pose_quote_term 42 qdreif. unquote_type0 qdreif qtype0.
  Time unquote_type_cbv' qdreif qdtype'. (* takes times *)
  Fail unquote_type_cbv qdreif qdtype. (* Error: Expression does not evaluate to a tactic. *)
  unquote_type_cbv1 qdreif qdtype1.
  unquote_type_cbv2 qdreif qdtype2. 
  unquote_type2 qdreif qdtype2' ltac:(cbv in qdtype2').
  reflexivity. Qed.

Definition MonProjT1 t := ret (my_projT1 t).

Print TemplateMonad.

Print typed_term.
Print Monad.
(* Record Monad (m : Type -> Type) : Type := Build_Monad
  { ret : forall t : Type, t -> m t;  bind : forall t u : Type, m t -> (t -> m u) -> m u } *)
Print ret.
(* ret@{d c} = 
fun (m : Type -> Type) (Monad0 : Monad m) => let (ret, _) := Monad0 in ret
     : forall m : Type -> Type, Monad m -> forall t : Type, t -> m t *)



Ltac mpT2ltac0 t :=  constr:(my_projT2 t).
Ltac mpT2ltac1 t :=  pose (my_projT2 t) as kik1.
Ltac mpT2ltac2 t :=  pose (my_projT2 t) as kik ; pose ((?kik * ?kik)%nat) as sq.
(* remarque: enlever %nat ne change rien à l'erreur ci-dessous *)
 


Definition tmqnat := tmQuote nat.
Definition ttz : typed_term  := {| my_projT1 := nat ; my_projT2 := 0|}.

Ltac preqt t idn := (run_template_program (tmUnquote t ) (fun x => pose x as idn)). 
Ltac unquote_type3 t idn := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT1 x) as idn))); cbv in idn.


Goal 2+2 = 4.
Proof.
Fail mpT2ltac0 ttz. (* Expression does not evaluate to a tactic. *)
mpT2ltac1 ttz. (* marche *)
Fail mpT2ltac2 tt2. (* Error: Variable t should be bound to a term but is bound to a intropattern. *)
pose_quote_term nat nat_reif.
preqt nat_reif try_preqt'.
unquote_type3  nat_reif sdjkl.
pose_quote_term 0 zero_reif.
unquote_type3 zero_reif nat_hopefully. (* yes *)
reflexivity.
Qed.

Print tmQuoteRec.

Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t ) ltac:(fun x =>  (pose  x as idn))).



Fixpoint get_decl (I : term) (e : global_env) :=
  match e with
  | [] => None 
  | (na,d) :: e' => 
      (match d with
        | InductiveDecl mind =>  let loind := ind_bodies mind in Some loind
        | _ => get_decl I e'
      end)    
    end.

    Print ind_bodies.
    Print one_inductive_body.
    Print mutual_inductive_body.

(* Definition list_ctors_mind I :=
  let fix list_ctors_aux l :=
  match l with
  | [] => []
  | oind :: l' =>
  end
  in list_ctors_aux I.(ind_bodies). *)


Ltac list_ctors_and_types I :=
  (* inachevé: get_ctors_and_types fait le travail, en utilisant MetaCoq *)
  let Ier := fresh "Ier" in rec_quote_term I Ier
  ; let bod := constr:(fst Ier)  in let Iq := constr:(snd Ier)
  in let blut := constr:(get_decl Iq bod) in let res := fresh "res" in pose blut as res; hnf in res.

(*   Print global_env.
Print inductive_decl.
*)
Print InductiveDecl.
Print global_env.

Goal 2+2 = 4.
Proof.
  list_ctors_and_types nat.
  rec_quote_term nat truc.
  pose (fst truc) as truc'.
  Eval cbn in truc'.
  reflexivity.
  Qed.




Ltac unquote_term t idn e := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); e idn.




Ltac pose_unquote_term_hnf t idn  := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); cbv in idn.

Ltac unquote_term_cbv' t idn  := unquote_term t idn ltac:(fun x => cbv in x).
(*Ltac unquote_term_cbv'' t idn  := unquote_term t idn (fun x => cbv in x). *)
(* \ltac Error:
Syntax error: ';' or ',' or ')' expected after [constr:operconstr level 200] (in [constr:operconstr]).
 -> spécifie que 3ème arg interprété comme un constr: *)


Goal 2 + 2 = 4.
Proof.
pose_quote_term 0 zero_reif.
pose_unquote_term_hnf zero_reif zero_hopefully.
unquote_term_cbv' zero_reif zero_hopefully'.
reflexivity.
Qed.


(* Ltac uqt t idn := (run_template_program (tmUnquote t ) (fun x => pose  x as blut)); 
 pose (mpT2ltac blut) as idn. *)


Ltac blutblut t := let blut := 3 in pose ?blut as kikoo.

Goal 2 + 2 = 4.
Proof.
pose_quote_term 2 nat_reif.  (* uqt nat_reif kik. *)

  (* blutblut 3. *)
  reflexivity.
  Qed.

  
Ltac uqt t idn ty := (run_template_program (r <- tmUnquote t  ;; @ret TemplateMonad ty (my_projT1 r)) (fun x => pose  x as idn)).

 Goal 2+ 2 = 4.
  pose_quote_term 0 zero_reif. unquote_type_cbv' zero_reif nat_type.
 (* unquote_term zero_reif blutblut.  *)
  reflexivity.
  Qed.








(*** Things to use in examples ***)

(* Coq *)
Definition cons_nat := @cons nat.


(* MetaCoq *)

MetaCoq Quote Definition zero_reif := 0.
MetaCoq Quote Definition one_reif := 1.
MetaCoq Quote Definition two_reif := 2.
MetaCoq Quote Definition three_reif := 3.

MetaCoq Quote Definition nil_nat_reif := Eval cbn in (@nil nat).
MetaCoq Quote Definition list_one_two_reif := Eval cbn in [1 ; 2].
MetaCoq Quote Definition list_one_three_reif := Eval cbn in [1 ; 2 ; 3].

MetaCoq Quote Definition list_one_three_reif' := (List.app [1] [2 ; 3]).



  

(** Reified functions *)

MetaCoq Quote Definition length_reif := @List.length.
MetaCoq Quote Definition le_reif := le.
MetaCoq Quote Definition S_reif := Eval cbn in S.
MetaCoq Quote Recursively Definition S_env_reif := S.
Print S_env_reif.
Print S_reif.
MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition add_reif := Eval cbn in Nat.add.
MetaCoq Quote Definition nil_reif := nil.
MetaCoq Quote Recursively Definition nil_env_reif := nil.
MetaCoq Quote Definition cons_reif := cons.
MetaCoq Quote Recursively Definition cons_env_reif := cons.
MetaCoq Quote Recursively Definition cons_nat_env_reif := cons_nat.
MetaCoq Quote Definition cons_nat_reif := cons_nat.


(** Reified types **) 

MetaCoq Quote Definition nat_reif := nat.
MetaCoq Unquote Definition nat_unreif := nat_reif.
Print nat_unreif.
MetaCoq Quote Recursively Definition nat_env_reif := nat.
Print nat_env_reif. 

Definition nat_oind := {|
ind_name := "nat"%string;
ind_type := tSort (Universe.of_levels (inr Level.lSet));
ind_kelim := IntoAny;
ind_ctors := [("O"%string, tRel 0, 0);
             ("S"%string,
             tProd
               {|
               binder_name := nAnon;
               binder_relevance := Relevant |} 
               (tRel 0) (tRel 1), 1)];
ind_projs := [];
ind_relevance := Relevant |}.



                   

  MetaCoq Quote Definition list_reif_generic := list.
MetaCoq Quote Definition list_reif := @list.
Print list_reif_generic.
Print list_reif. (* idem *)
MetaCoq Quote Recursively Definition list_env_reif := @list.
Print list_env_reif.



Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat. 
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).


Print "=".

Definition eq_nat := @eq nat.
Print eq_nat.

MetaCoq Quote Definition Type_reif := Eval cbn in Type.
MetaCoq Quote Definition Prop_reif := Eval cbn in Prop. 
MetaCoq Quote Definition Set_reif := Eval cbn in Set. 

MetaCoq Quote Definition eq_reif := Eval cbn in @eq. 
Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].
Print eq_reif. 


(*\evar MetaCoq Quote Definition eq_reif_generic := Eval cbn in eq.  *)
(*\evar Print eq_reif_generic. *) (* \Q comment se débarrasser du tEvar ? *)

MetaCoq Quote Definition eq_nat_reif := Eval cbn in (@eq nat).
Print eq_nat_reif.

MetaCoq Quote Definition eq_term_reif := Eval cbn in (@eq term).
Print eq_term_reif.

MetaCoq Quote Definition eq_reif_generic' := Eval cbn in @eq. 
Print eq_reif_generic'.

MetaCoq Quote Definition True_reif := Eval cbn in True.
MetaCoq Quote Definition False_reif := Eval cbn in False.
(* MetaCoq Quote Definition and_reif := Eval cbn in "/\".*) (* \! ambiguïté *) 
(* Quote the *string* "/\" *)
MetaCoq Quote Definition and_reif := Eval cbn in and.
MetaCoq Quote Definition or_reif := Eval cbn in or.

 
MetaCoq Unquote Definition two_unreif := two_reif.
Print two_unreif.

MetaCoq Unquote Definition list_nat_unreif := list_nat_reif.
Print list_nat_unreif.

MetaCoq Quote Definition and_reif_blut := (and (1 = 1) (0 = 1)).
MetaCoq Unquote Definition and_unreif_blut := and_reif_blut.
Print and_unreif_blut.

(** reified equalities **)

MetaCoq Quote Definition zero_equal_zero_reif := Eval cbn in (eq 0 0).
Print zero_equal_zero_reif.                                                      
MetaCoq Quote Definition zero_equal_zero_reif' := Eval cbn in (@eq nat 0 0).
Print zero_equal_zero_reif'.                                                      
MetaCoq Quote Definition zero_equal_zero_reif'' := Eval cbn in (eq_nat 0 0).
Print zero_equal_zero_reif''.                                                      


(** list in Set **)
Inductive listS (A : Set) :=
| nilS : listS A
| consS : A -> listS A -> listS A
.
Print listS.
MetaCoq Quote Definition listS_reif := listS.
MetaCoq Quote Definition nilS_reif := nilS.
MetaCoq Quote Definition consS_reif := consS.
MetaCoq Quote Recursively Definition listS_env_reif := listS.
Print listS_env_reif.
Print Set_reif.
Print consS_reif.

Print tProd.
Print aname.
Print name.
MetaCoq Quote Definition lam_true_reif := (forall (A: Type), True).
Print lam_true_reif.
MetaCoq Quote Definition T_imp_T_reif :=  (True -> True).
Print T_imp_T_reif.



Definition mkNamed s := ({| binder_name := nNamed (s%string); binder_relevance := Relevant |} : aname).
Definition mkNAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

Definition truc := mkNamed (("B"%string) : ident).


Definition consS_typ := tProd (mkNamed "A") (tSort (Universe.from_kernel_repr (Level.lSet, false) []))
                                  (tProd mkNAnon (tRel 0)
                                     (tProd mkNAnon (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))).






(** reified connectives **)


Print ex.


MetaCoq Quote Definition ex_reif := Eval cbn in @ex.
MetaCoq Quote Definition ex_intro_reif := Eval cbn in @ex_intro.



Inductive Ntree : Set := Nnode : nat -> Nforest -> Ntree
with Nforest : Set :=
    Nleaf : nat -> Nforest
  | Ncons : Ntree -> Nforest -> Nforest.

MetaCoq Quote Definition Ntree_reif := Ntree.
MetaCoq Quote Definition Nforest_reif := Nforest.
MetaCoq Quote Definition Ncons_reif := Ncons.
MetaCoq Quote Definition Nleaf_reif := Nleaf.
MetaCoq Quote Definition Nnode_reif := Nnode.
MetaCoq Quote Recursively Definition Ncons_env_reif := Ncons.


(* Mutual inductive with parameter : tree/forest *)

Inductive Atree (A : Set) : Set :=
  Anode : A  -> Aforest A -> Atree A
   with Aforest (A : Set) : Set :=
      Aleaf : A -> Aforest A
  | Acons : Atree A  -> Aforest A -> Aforest A.


MetaCoq Quote Definition Atree_reif := Atree.
MetaCoq Quote Definition Aforest_reif := Aforest.
MetaCoq Quote Definition Acons_reif := Acons.
MetaCoq Quote Definition Aleaf_reif := Aleaf.
MetaCoq Quote Definition Anode_reif := Anode.
MetaCoq Quote Recursively Definition Acons_env_reif := Acons.




(* Mutual inductive with indices: even/odd  *)

Inductive odd : nat -> Prop := oddS : forall n:nat, even n -> odd (S n)
with even : nat -> Prop :=
  | evenO : even 0
  | evenS : forall n:nat, odd n -> even (S n).


MetaCoq Quote Definition odd_reif := odd.
MetaCoq Quote Recursively  Definition odd_env_reif := odd.
MetaCoq Quote Definition even_reif := even.
MetaCoq Quote Recursively  Definition even_env_reif :=even.
MetaCoq Quote Definition oddS_reif := oddS.
MetaCoq Quote Recursively  Definition oddS_env_reif := oddS.
MetaCoq Quote Definition evenO_reif := evenO.
MetaCoq Quote Recursively  Definition evenO_env_reif := evenO.
MetaCoq Quote Definition evenS_reif := evenS.
MetaCoq Quote Recursively  Definition evenS_env_reif := evenS.


(*** Useful operators ***)


Definition mkImpl A B := tProd mkNAnon A (lift0 1 B). (*vérifier si lift ok *)




(* write examples to check specif *)

Definition mkNot (A :term) := mkImpl A False_reif.


Definition mkAnd (A B : term) := tApp and_reif [A ; B]. 

Fixpoint and_nary_reif (l : list term):=
  match l with
  | t :: [] => t
  | [] => False_reif               
  | t :: tll => mkAnd t (and_nary_reif tll)                
  end.

Example anr1 := and_nary_reif [True_reif; False_reif ; zero_equal_zero_reif ].
MetaCoq Unquote Definition anr_u1 := anr1.
Print anr_u1.


Fixpoint or_nary_reif (l : list term):=
  match l with
  | [] => False_reif           
  | t :: [] => t
  | t :: tll => tApp or_reif [t ; or_nary_reif tll ]                
  end.

Example onr1 := or_nary_reif [True_reif; False_reif ; zero_equal_zero_reif ].
MetaCoq Unquote Definition onr_u1 := onr1.
Print onr_u1.

Fixpoint build_prod (B : term) (lA : list term) :=
  match lA with
  | [] => B
  | A1 :: tllA  => tProd mkNAnon A1 (build_prod B tllA )
  end.

Example bprod1 := build_prod zero_equal_zero_reif [True_reif; False_reif ; zero_equal_zero_reif ].
MetaCoq Unquote Definition bprodu1 := bprod1.
Print bprodu1.



Goal 2 + 2 = 4.
Proof.
idtac "kikoo". Search Nat.add. idtac  "blut". Search kername. Print kername_eq_dec. Search kername_eq_dec.
reflexivity.
Qed.

Definition get_kn_term (t: term) :=
  (* gets the kername of a reified inductive *)
  (* dummy kn in all other cases *)
  (* should probably extended *)
  match t with 
   |  tInd indu _ => inductive_mind indu
   |  _ => ( MPfile ([] : list ident), "dummy")
  end. 




Definition dom_list_f ( B  :  term) (n : nat)  :=
  (* takes a type B := Prod A1 ... An . B'  and outputs [A1; ... ; An], at least if no dependencies *)
  (* does not handle debruijn indices *)
  let fix dlaux B n acc :=
  match n with
  | 0 => acc 
  | S n => match B with
          | tProd na A f' =>  dlaux f' n (A :: acc)
          | _ => [] (* this case shouldn't happen *)
          end            
  end
  in List.rev (dlaux B n []).


Example dlf1 := Eval cbn in dom_list_f cons_nat_type_reif 2.
Print dlf1. 





(* dom_and_codom_sim is limited because it does not handle an output type that is morally a product *)
(* the 1st element of the output is the list of domains of C and the 2nd element is its codomain *)
Definition dom_and_codom_sim (C : term) := 
  let fix aux C accl  :=
      match C with        
      | tProd _ A B => aux B (A :: accl)
      | _ => (accl , C)
      end
        in let ( lA , B) := aux C [] in (List.rev lA, B).



Example dcodsim1 := Eval cbn in dom_and_codom_sim cons_nat_type_reif.
Print dcodsim1.
    


(***  Marks impossible cases ***)

Inductive impossible_type : Type  := .

MetaCoq Quote Definition imposs_mark :=  impossible_type  .




(*** Sur le typage ***)


Existing Instance config.default_checker_flags. (* pour les defs ci-dessous *)
 

Definition is_typable (t: term) := { Sigma & { Gamma & { B &  Sigma  ;;; Gamma |- t : B}}}.

Definition is_type (A : term) := {Sigma & {Gamma & { s &  Sigma ;;; Gamma |- A : tSort s}}}.

Definition has_type (t A:  term) := { Sigma & { Gamma & { B &  Sigma  ;;; Gamma |- t : B}}}.



(** ** Auxiliary functions *)


Class TslIdent := { tsl_ident : ident -> ident }.

Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => (id ++ "'")%string |}.

Fixpoint try_remove_n_lambdas (n : nat) (t : term) {struct n} : term :=
  match n, t with
  | 0, _ => t
  | S n, tLambda _ _ t => try_remove_n_lambdas n t
  | S n, _ => t
  end.


(** * Plugin *)


Definition ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.

(*** Ltac: récupérer une liste de termes réifiés dans Ltac à partir de leurs noms***)


(*** extracting parameters ****)

(* \todo écrire pose_inductive, qui nous extrait indu *)

Ltac get_ind_param t idn := 
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with (* voir si hnf marche !!!! *)
     | tApp ?iu ?lA =>  
       (lazymatch eval hnf in iu with
       | tInd ?indu ?u => pose (indu,lA) as idn ; clear rqt
       end )
     | tInd ?indu ?u => pose (indu,([]: list term)) as idn ; clear rqt
     end
     end.

Ltac get_env_ind_param t idn := 
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with (* voir si hnf marche !!!! *)
     | tApp ?iu ?lA =>  
       (lazymatch eval hnf in iu with
       | tInd ?indu ?u => pose (Sigma,(indu,lA)) as idn ; clear rqt
       end )
     | tInd ?indu ?u => pose (Sigma,(indu,([]: list term))) as idn ; clear rqt
     end
     end.

Goal False.
Proof.
let s1 := fresh "s1" in get_env_ind_param (list nat) s1.
Print list_reif.
let s2 := fresh "s2" in get_ind_param (nat) s2.
Print nat_reif.
Print even_reif.
Abort.



Ltac pose_mind_tac t idn :=   (* factoriser code !*)
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with (* voir si hnf marche !!!! *)
     | tApp ?iu ?lA =>  
       lazymatch eval hnf in iu with
       | tInd ?indu ?u => 
     let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
       lazymatch eval cbv in lkup  with
       | Some ?d =>   
         match d with
         |  InductiveDecl ?mind =>  pose mind as idn ; simpl in idn ; clear rqt
         end       
       end
       end  
       |   tInd ?indu ?u => 
       let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
         lazymatch eval cbv in lkup  with
         | Some ?d =>   idtac "Some d";(* *) 
           match d with
           |  InductiveDecl ?mind =>  pose mind as idn ; simpl in idn ; clear rqt
           end       
         end     
     end
     end
    .


    Ltac get_mind_tac t  :=  
      let rqt := fresh "rqt" in rec_quote_term t rqt ; 
      lazymatch eval hnf in rqt with
       | (?Sigma,?ind) => idtac "Sigma ind"; lazymatch eval hnf in ind with (* voir si hnf marche !!!! *)
       | tApp ?iu ?lA => idtac "tApp iu lA" ; 
         lazymatch eval hnf in iu with
         | tInd ?indu ?u => 
       let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
         lazymatch eval cbv in lkup  with
         | Some ?d =>   idtac "Some d";(* *) 
           match d with
           |  InductiveDecl ?mind =>   clear rqt ;constr:(mind) 
           end       
         end
         end         
       end
       end
      .

      
 

Ltac pose_oind_tac t i idn := let s := fresh "s" in pose_mind_tac t s ; pose (nth i s.(ind_bodies)  nat_oind) as idn; simpl in idn ; clear s.

Goal False.
Proof. let blut := fresh "blut" in pose_oind_tac (list nat) 0 blut.
Abort.



(*** Propriétés des inductifs ***)

Fixpoint forall_nary lx lA B:=
  match (lx,lA) with
  | (hx :: tx, hA :: tA) => tProd hx hA (forall_nary tx tA B)
  | _ => B
end.



Polymorphic Fixpoint and_iter_try (n : nat) :=
  match n with
  | 0 => True_reif
  | 1 => zero_equal_zero_reif
  | S n =>  tApp and_reif [zero_equal_zero_reif ;  and_iter_try n ]
  end. 


MetaCoq Unquote Definition and_iter_try1:= (and_iter_try 1).
Print and_iter_try1.        
MetaCoq Unquote Definition and_iter_try2:= (and_iter_try 2).
Print and_iter_try2.        

Polymorphic Fixpoint and_eq_combine_reif (lA l1 l2 : list term) :=
(* if l1=[t1,...,tn], l2=[u1,...,un], lA=[A1,...An] and ti,ui: have type Ai, outputs the reification of   t1^ = u1^ /\ ... /\ tn^ /\ un^ ]. One must specify, the type of the terms *)
  (* \todo améliorer si possible de trouver conjonction /\ n-aire efficace *)
        match (lA , l1, l2) with
  | (A::[], x1 :: [], x2 :: []) =>  tApp eq_reif [A; x1; x2] 
  | (A1 :: tlA, x1 :: tl1, x2 :: tl2) =>  tApp and_reif ((tApp eq_reif [A1; x1 ; x2]) ::  [and_eq_combine_reif tlA tl1 tl2] )
  | (_, [] , [] ) => True_reif                                         
  | (_ ,_ ,_) => False_reif (* return False if length l1 neq l2 *)
end.



(* why only two arguments to eq, including type? *)




Fail MetaCoq Unquote Definition blut0 :=  (tApp eq_reif_generic [nat_reif; two_reif ; one_reif ]). 
(* problem with tEvar in eq_reif_generic *)

(* MetaCoq Unquote Definition blut0' :=  (tApp eq_nat_reif [two_reif ; one_reif ]). *)
(* non-functional construction *)
MetaCoq Unquote Definition blut1 :=  (tApp eq_nat_reif [two_reif]). 



Example test_eq_combine3 := Eval cbn in let '(lA, l1, l2) := ([nat_reif; list_nat_reif],  [zero_reif ;  list_one_three_reif] , [one_reif ; list_one_three_reif' ]) in and_eq_combine_reif lA l1 l2 .


MetaCoq Unquote Definition test_eq_combine_unquote3 :=  test_eq_combine3.
Print test_eq_combine_unquote3.


(*Section Inductives_to_FO. *)




(* \!  dependency not taken into account *)


(*** Injectivité ***)

(* is_inj commenté : f est juste fonctionnelle ! *)
  (* 
Fixpoint is_inj_aux (B f1 f2: term) (lA : list term) :=
  match lA with
  | [] => mkEq B f1 f2  
  | A1 :: tllA => tProd (mkNamed "x") A1 (tProd (mkNamed "y") A1 
(mkImpl (tApp eq_reif [A1 ; tRel 1 ; tRel 0 ]) ( is_inj_aux B (tApp (lift0 2 f1) [tRel 1]) (tApp (lift0 2 f2) [tRel 0]) tllA)))  
  end.


Definition is_inj (B f: term) (lA : list term) := is_inj_aux B f f lA. *)

(* MetaCoq Unquote Definition S_inj_reif := (is_inj nat_reif S_reif [nat_reif]).
Print S_inj_reif.
MetaCoq Unquote Definition cons_nat_inj_reif := (is_inj list_nat_reif cons_nat_reif  [nat_reif; list_nat_reif]).
Print cons_nat_inj_reif. *)
 

Fixpoint is_inj (B f: term) (lA : list term) :=
let fix inj_aux (B f1 f2: term) (lA : list term) (n: nat) := 
  match lA with
  | [] => (fun (t : term) => t, f1 , f2 , True_reif )  
  | A1 :: tllA => let blut := inj_aux B (tApp (lift0 2 f1) [tRel 1]) (tApp (lift0 2 f2) [tRel 0]) tllA (n-1) in
                (fun (t: term) => (tProd (mkNamed "x") A1 (tProd (mkNamed "y") (lift0 1 A1) (blut.1.1.1 t)  )), blut.1.1.2, blut.1.2,  mkAnd (lift0 (2*(n-1)) (mkEq A1 (tRel 0) (tRel 1)))  blut.2 )
  end in 
   let kik := inj_aux B f f  lA (List.length lA)  in kik.1.1.1 (mkImpl  (mkEq B kik.1.1.2 kik.1.2) kik.2   ) .
(* \Q comment éviter de lire la longueur de la liste en entrée de inj_aux *) 

MetaCoq Unquote Definition really_S_inj_reif := (is_inj nat_reif S_reif [nat_reif]).
Print really_S_inj_reif.

(* Definition inj_aux_test := Eval cbn in (inj_aux list_nat_reif cons_nat_reif cons_nat_reif [nat_reif; list_nat_reif]) 2.
Print inj_aux_test. *)
MetaCoq Unquote Definition really_cons_nat_inj_reif := (is_inj list_nat_reif cons_nat_reif  [nat_reif; list_nat_reif]).
Print really_cons_nat_inj_reif.




(* \! dans ctor_is_inj, i devrait être un entier de Ltac, pas de Coq *)



Ltac just_cbv t := cbv in t.

Goal 2 + 2 = 4.
Proof.  pose ( String.append "kikoo" "lol") as H. just_cbv H.
reflexivity. Qed.


Ltac sdf B f A := assert (k := 5);  (match goal with
| h : _ = _ |- _ => inversion h
end ).

Ltac ctor_is_inj_tac B f lA  :=
let toto := fresh "H" in  (pose_unquote_term_hnf (is_inj B f lA) toto );  assert toto   ; unfold toto; intros ; [match goal with
                                                                                                            | h : _ = _ |- _ => inversion h                                                                     end  ; repeat split | .. ]; subst toto.  (* repeat split . *) 
  (* ; assert Hinj ; (injection in Hinj). *)
(* \! qqch de très important à comprendre: pq sans [ | ..], tactique appliquée à tous les sous-buts, même ceux qui ne sont pas créés par la 1ère partie.  *)



MetaCoq Unquote Definition is_inj_cons_nat := (is_inj list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif]).
Goal 2 + 2 = 4.
Proof. 
  ctor_is_inj_tac list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif]. reflexivity. Qed.

(*   lazymatch goal with
| h : _ = _ |- _ =>  inversion h
end. *)
 (*  inversion H0. repeat split. 
  unfold H in H0. clear H. *)
  
  
Goal (2 + 2 = 4) -> (1 + 1 = 2) -> ( 2 + 2 = 4 /\ 1 +1 = 2).
Proof. 
intros. split. split. split.
Qed.
                                                                                                


(* \Q mettre le lift dans le premier élément du quadruplet ?*)


Definition nilterm := @nil term.

Ltac ctors_are_inj_tac B lf lA :=  
  match constr:((lf , lA)) with
  | ( nil , nil ) => idtac "nothing happens. Improve this message"
  | ( ?f1 :: ?tlf , ?A1 :: ?tlA) => ctor_is_inj_tac B f1 A1; ctors_are_inj_tac B tlf tlA
  end.
  

Goal 2 + 2 = 4.
Proof. 
ctors_are_inj_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]]. 
reflexivity. Qed.
                                                                                                      
Fixpoint are_inj (B : term) (lf : list term) (lA : list (list term)):=
  match (lf , lA) with
  | ([], []) => True_reif
  | (f1 :: tllf , A1 :: tllA ) => mkAnd (is_inj B f1 A1) (are_inj B tllf tllA)
  | _ => False_reif
  end.
(* \rmk : this function may be improved by skipping function of arity 0 *)

MetaCoq Unquote Definition nat_inj_reif := (are_inj nat_reif [zero_reif ; S_reif] [[] ; [nat_reif]]).
Print nat_inj_reif.

MetaCoq Unquote Definition list_nat_inj_reif := (are_inj list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]]).
Print list_nat_inj_reif.

Example test_are_inj_cons_nat : 2 + 2 = 4.
(ctors_are_inj_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]]).
reflexivity.
Qed.
  
Definition is_inj' (A t: term) (lA l1 l2 : list term) :=
 mkImpl ( tApp eq_reif  [A; tApp t l1; tApp t l2]) ( and_eq_combine_reif lA l1 l2).
(* t^u is a function of type lA^u -> A^u *)



MetaCoq Unquote Definition is_inj'_test1 := ( is_inj' list_nat_reif cons_nat_reif [nat_reif; list_nat_reif] [zero_reif ; nil_nat_reif] [one_reif ; nil_nat_reif ]).
Print is_inj'_test1. (* cons_nat 0 [] = cons_nat 1 [] -> 0 = 1 /\ [] = []  *)




(*** Constructeurs disjoints : fail ***)

Definition same_dom_Set (B Af Ag f g: term)  (l1 l2: list term) :=
  (* of course, we cannot specify that f and g are definitionally equal *)
  (* B: common return type of g and g *)
  (* right now, specifies that f and g have the same type  instead of the having the same dom*)
mkImpl (tApp eq_reif [B ; tApp f l1 ; tApp g l2 ])  (tApp eq_reif [Set_reif; Af ; Ag] ) .
(* \! stupide: il suffirait de dire que  l1 = l2 *)





Example same_dom_Set_1 := same_dom_Set list_nat_reif cons_nat_type_reif list_nat_reif cons_nat_reif nil_nat_reif [zero_reif ; nil_nat_reif ] [].
MetaCoq Unquote Definition sds_unreif1 := same_dom_Set_1.
Print sds_unreif1.

Example same_dom_Set_2 := same_dom_Set list_nat_reif cons_nat_type_reif list_nat_reif cons_nat_reif nil_nat_reif [zero_reif ; nil_nat_reif ] [nil_nat_reif (*!*) ].
Fail MetaCoq Unquote Definition sds_unreif2 := same_dom_Set_2.
(* Erreur s'aperçoit que @nil nat ne peut être appliqué à qqch *)


(* \pb : intuitivement, il faut matcher l'égalité de Af et Ag avant de calculer f = g *)




Definition codom_disj_sort_fail (B s f g: term)  (lAf lAg l1 l2 : list term) :=
(* f^u : lAf^u -> B, g^u : lAg^u -> B of sort s^u. If f l1 = g l2 then lAf lAg, f = g and l1 = l2 *)
 let pABf := build_prod B lAf  in let pABg := build_prod B lAg in    
  mkImpl (tApp eq_reif [B ; tApp f l1 ; tApp g l2 ])
   (and_eq_combine_reif [s ; pABf ]   [pABf ; f ][ pABg ; g] )
. (* \rmk computation may be optimized *) 

     



Example codom_disj_sort1 := (* Eval cbn in *) codom_disj_sort_fail list_nat_reif Set_reif cons_nat_reif nil_nat_reif [nat_reif ; list_nat_reif ] [] [zero_reif ; nil_nat_reif] [].
Fail MetaCoq Unquote Definition cds_u1 := codom_disj_sort1.

     (* \ Q ne faut-il pas gérer les sortes de B et de chaque lAf et lAg différemment, genre avoir des listes de sortes en argument ? *)
  (* \todo comprendre comment récupérer les informations sur les sortes dans les environnements *)

(** \Pb Problème **)
(* codom_disj_sort_fail ne peut marcher car dès que les domaines de f et g sont distincts, on ne peut plus dire que f et g sont égaux *)
(* il faut probablement utiliser des sigma types/records. Voir si faisable bien *)
(* ou alors, on suppose qu'on pourra appliquer uniquement la fonction à des constructeurs distincts (on peut extraire la liste des constructeurs d'un inductif ce qui donne codom_disj ci-dessous *)

Print list.

Fixpoint blut0 (l1 l2 : list nat) : list nat:=
  match l1 with
  | x1 :: tl1 => blut0  tl1 l2
  | [] => (fix blut0_aux l2 := match l2 with
       | [] => []
       | t2 :: tl2 => blut0_aux tl2
         end) l2
  end.

Fail Fixpoint blut0 (l1 l2 : list nat) : list nat:=
  match l1 with
  | x1 :: tl1 => blut0  tl1 l2
  | [] => match l2 with
       | [] => []
       | t2 :: tl2 => blut0  [] tl2
         end                                 
  end.





Fail Fixpoint blut2 (B f g: nat) (l1 l2 : list nat) : list nat:=
  match l1 with
  | nil => match l2 with
         | [] => []
         | t2 :: tl2 => blut2 B f g [] tl2
         end
  | x1 :: tl2 => blut2 B f g tl2 l2
  end.


Fail Fixpoint blut3 (B f g: term) (l1 l2 : list term) :=
  match l1 with
  | [] => match l2 with
         | [] => []
         | t2 :: tl2 => blut3 B f g [] tl2
         end
  | x1 :: tl2 => blut3 B f g tl2 l2
  end.

  

(* Fixpoint codom_disj (B f g: term)  (lAf lAg : list term)  : term :=
  match lAf  with
  | [] => (fix codom_disj_aux lAG := match lAg with
         | [] => mkNot (tApp eq_reif [B ; f ;  g])
         | A1 :: tllAg  =>  codom_disj B f g [] tllAg  
         end ) lAg          
  |  A1 :: tllAf =>  codom_disj B f g tllAf lAg 
  end. *)


Fail Fixpoint codom_disj' (B f g: term)  (lAf lAg : list term)  : term :=
  match (lAf , lAg) with
  | ( [] , [] ) => mkNot (tApp eq_reif [B ; f ;  g])
  |  ([], A1 :: tllAg ) =>  tProd mkNAnon A1 (codom_disj' B f (tApp 1 g [tRel 1]) [] tllAg  )           
  | ( A1 :: tllAf , _ ) => tProd mkNAnon A1 (codom_disj' B (tApp f [tRel 1] ) g tllAf lAg  ) 
  end.


(*** codomaines disjoints ***)




Fixpoint codom_disj (B f g: term)  (lAf lAg : list term)  : term :=
  match lAf  with
  | [] => (fix codom_disj_aux B f g lAg  := match lAg with
         | [] => mkNot (tApp eq_reif [B ; f ;  g])
         | A1 :: tllAg  =>  tProd mkNAnon A1 (codom_disj_aux B  (lift0 1 f) (tApp  (lift0 1 g) [tRel 0]) tllAg  )
         end ) B f g lAg          
  | A1 :: tllAf => tProd mkNAnon A1 (codom_disj B (tApp (lift0 1 f) [tRel 0] )   (lift0 1 g) tllAf lAg  ) 
  end.
(* on lifte tlm dès qu'on fait une abstraction
 *) 


Ltac codom_disj_discr B f g lAf lAg :=
  let toto := fresh "H" in (pose_unquote_term_hnf (codom_disj B f g lAf lAg) toto);
assert toto; unfold toto ; intros ;
                           [ try discriminate | .. ] ; subst toto. 
(* \todo : refolder not ? *)


Goal 2 + 2 = 4.
Proof.
  codom_disj_discr list_nat_reif nil_nat_reif  cons_nat_reif  (@nil term) [ nat_reif ; list_nat_reif ].
reflexivity. Qed.

Example disj_codom1 := codom_disj list_nat_reif nil_nat_reif nil_nat_reif [ ] [].
MetaCoq Unquote Definition d_cod_u1 := disj_codom1.
(* Set Printing All. *)
Print d_cod_u1.

Example disj_codom2 := Eval cbn in codom_disj list_nat_reif cons_nat_reif cons_nat_reif [nat_reif ; list_nat_reif ] [nat_reif ; list_nat_reif ].
MetaCoq Unquote Definition d_cod_u2 := disj_codom2. 
Print d_cod_u2.


Example disj_codom3 := codom_disj list_nat_reif nil_nat_reif  cons_nat_reif  [] [ nat_reif ; list_nat_reif ].
MetaCoq Unquote Definition d_cod_u3 := disj_codom3.
Print d_cod_u3.

Fixpoint pairw_disj_codom ( B : term) (lf : list term) (lA : list (list term)) :=
  let fix pairw_aux (B f : term) (lAf lf : list term)  (lA : list (list term)) :=
      match (lf , lA) with
        | ([] , []) => True_reif
        | (f1 :: tllf , A1 :: tllA ) => mkAnd (codom_disj B f f1 lAf A1) (pairw_aux B f lAf tllf tllA)
        | _ => False_reif                                                    
      end        
      in 
  match (lf , lA)  with
  | ([] , [] ) => True_reif
  | (f1 :: tllf  , A1 :: tllA ) => mkAnd (pairw_aux B f1 A1 tllf tllA) (pairw_disj_codom B tllf tllA)
  | _ => False_reif                                     
  end.


Ltac pairw_aux B f lAf lf lA :=
     lazymatch constr:((lf , lA)) with
        | ([] , []) => idtac "" (* \Q tactique qui ne fait rien ? *)
        | (?f1 :: ?tllf , ?A1 :: ?tllA ) => codom_disj_discr B f f1 lAf A1 ; pairw_aux B f lAf tllf tllA
        | _ => idtac "wrong branch pairw_aux"  ; fail                                             
      end.

Goal 2 + 2 = 4.
  Proof.
      pairw_aux list_nat_reif nil_nat_reif  (@nil term) [cons_nat_reif]  [ [nat_reif; list_nat_reif]].
      reflexivity. Qed. 
 
    
Ltac pairw_disj_codom_tac B  lf  lA  :=
  match constr:((lf , lA))  with
  | ([] , [] ) => idtac ""
  | (?f1 :: ?tllf  , ?A1 :: ?tllA ) => ltac:(pairw_aux B f1 A1 tllf tllA) ; ltac:(pairw_disj_codom_tac B tllf tllA)
  | _ => idtac "wrong branch pair_disj_codom_tac"                                
  end.

Goal 2 + 2 = 4.
Proof.
 pairw_disj_codom_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]].  
reflexivity. Qed.

Example pwdc1 := pairw_disj_codom list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]].
MetaCoq Unquote Definition pwdcu1 := pwdc1.
Print pwdcu1.

(* test avec 3 constructeurs pas fait*)



(*** Constructeurs totaux ***)






Ltac intros_exist_aux n e := (* merci Theo *)
  lazymatch n with
  | 0 => e
  | S ?n =>
    let h := fresh "x" in
    intro h ;
    let e' := e  ; exists h in
    intros_exist_aux n e'
  end.

 Goal forall (n m k: nat), exists (x y z: nat), x = n /\ y = m /\ z = k .
 Proof. intros_exist_aux  3 ltac:(idtac "").  let x := fresh "x" in let x:= fresh "x" in idtac "hello world". repeat split.
Qed.
        


(*\evar MetaCoq Quote Definition ex_ex_reif1 := Eval cbn in (exists n, True ). *)
Fail Print ex_ex_reif1. (* un tEvar *)
MetaCoq Quote Definition ex_ex_reif2 := Eval cbn in (@ex nat (fun n => True) ).  
Print ex_ex_reif2. (* pas de tEvar *)

Print ex. (* Inductive ex (A : Type) (P : A -> Prop) : Prop :=  ex_intro : forall x : A, P x -> exists y, P y *)


(* inclut de la currif avec l'appli partielle de le*)
Print tLetIn.


MetaCoq Quote Definition double_ex_reif1 := Eval cbn in (exists (n m: nat ), n + m = 2).
Print double_ex_reif1.
(* ex_reif puis tLambda n puis  ex_reif puis tLambda m *)

Print ex. (* \Q ??????*)




Fixpoint is_in_codom (B t f: term ) (lA : list term) :=
  (* if t : A and f : Pi lx lA . A, tells when t is in the codomain of f: returns exist vecx : lA, f vecx = t  *)
  match lA with
  | [] => tApp eq_reif [B ; t ; f]
  | A :: tllA => tApp ex_reif [A ;  tLambda (mkNamed "x") A   (is_in_codom B (lift0 1 t) (tApp (lift0 1 f) [tRel 0] )   tllA  )]
  end.
(* base case : f is 0-ary and  t is just f *)

Print ex_reif.
Print ex.




Example in_codom1 := is_in_codom nat_reif  one_reif add_reif [nat_reif ; nat_reif ].
MetaCoq Unquote Definition in_codom_unreif1 := in_codom1.
Print in_codom_unreif1.

Example in_codom'1 := tProd (mkNamed "y") nat_reif (is_in_codom nat_reif  (tRel 0) add_reif [nat_reif ; nat_reif ]).
MetaCoq Unquote Definition in_codom_unreif'1 := in_codom'1.
Print in_codom_unreif'1. (* ça marche  ! *)


Example in_codom2 := is_in_codom nat_reif  two_reif S_reif [nat_reif ].
MetaCoq Unquote Definition in_codom_unreif2 := in_codom2.
Print in_codom_unreif2.


Example in_codom'2 := tProd (mkNamed "x") nat_reif  (is_in_codom nat_reif  (tRel 0) S_reif [nat_reif ]) .
MetaCoq Unquote Definition in_codom_unreif'2 := in_codom'2.
Print in_codom_unreif'2.  (* marche *)


Example in_codom3 := Eval cbn in is_in_codom list_nat_reif nil_nat_reif cons_nat_reif [nat_reif ; list_nat_reif].
MetaCoq Unquote Definition in_codom_unreif3 := in_codom3.
Print in_codom_unreif3.

Example in_codom4 := Eval cbn in (tProd (mkNamed "y") list_nat_reif ( is_in_codom list_nat_reif (tRel 0) cons_nat_reif [nat_reif ; list_nat_reif])).
MetaCoq Unquote Definition in_codom_unreif4 := in_codom4.
Print in_codom_unreif4.
(*  list nat -> exists (x : nat) (x0 : list nat), x0 = cons_nat x x0 *)
(* pas bien : list N->  + x0 deux fois *)

Example in_codom'4 := Eval cbn in (tProd (mkNamed "y") list_nat_reif ( is_in_codom list_nat_reif (tRel 0) cons_nat_reif [nat_reif ; list_nat_reif])).
MetaCoq Unquote Definition in_codom_unreif'4 := in_codom'4.
Print in_codom_unreif'4.

(* \rmk le x de forall x est lifté à chaque quantif existentiel *)


Fixpoint codom_union_total (B : term) (lf : list term) (lA : list (list term)) :=
(* lf is a list of function [f1;...;fn] whose return type is B, lA = [lA1 ; ...; lAn] is the list of the list of the types of the fi, e.g. lA1 is the list of argument types of lA *)
  let fix arg_org (B  t : term) (lf : list term) (lA: list (list term)) :=
      match (lf , lA)  with
      | (f1 :: tllf, lA1 :: tllA)  => (is_in_codom B t f1 lA1) :: (arg_org B t tllf tllA )
      | ([], []) => []
      | _ => [False_reif]               
      end
  in tProd (mkNamed "x") B  (or_nary_reif (arg_org B (tRel 0)  lf lA)).



Example cdu1 := codom_union_total list_nat_reif  [nil_nat_reif ; nil_nat_reif ] [ [] ; [] ].
MetaCoq Unquote Definition cdu_u1 := cdu1.
Print cdu_u1.


Example cdu2 := codom_union_total nat_reif [ O_reif; S_reif ] [ []; [nat_reif ]].
MetaCoq Unquote Definition cdu_u2 := cdu2.
Print cdu_u2. (*  nat -> exists x0 : nat, x0 = S x0  ??? d'où bien le N-> et pq doublon variable ?*)

Example cdu3 := codom_union_total list_nat_reif [cons_nat_reif ] [ [nat_reif ; list_nat_reif ] ].
MetaCoq Unquote Definition cdu_u3 := cdu3.
Print cdu_u3.


Example cdu_4 := codom_union_total Prop_reif [evenS_reif] [[nat_reif (* ; reif de even n*)  ]].
(* should tell that what ???? *) 
Fail MetaCoq Unquote Definition cdu_u4 := cdu_4.


Example cdu'1 := codom_union_total nat_reif [zero_reif ; S_reif ] [ [] ; [nat_reif]].
MetaCoq Unquote Definition cdu_u'1 := cdu'1.
Print cdu_u'1.




Example cdu'2 := codom_union_total list_nat_reif [nil_nat_reif ; cons_nat_reif ] [ [] ; [nat_reif; list_nat_reif]].
MetaCoq Unquote Definition cdu_u'2 := cdu'2.
Print cdu_u'2.


  


Print intros_exist_aux.



Ltac revert_intro_ex_tac_aux e :=
    match goal with
        | H : _ |- _ =>  first [ revert H ;  let e':= (intro H; e)  in revert_intro_ex_tac_aux  e'  ; exists H   | e]
end.

Ltac revert_intro_ex_tac  := revert_intro_ex_tac_aux ltac:(idtac "").

Ltac n_right n :=
  match n with
  | O => idtac ""
  | S ?n => right; n_right n             
  end.
    
Ltac right_k_n k n :=
  match n with
  | O => idtac ""
  | S ?n
    => match k with
      | O => idtac ""
      | S ?k => right ;  right_k_n k n
      end
  end.

Ltac righter_tac1 t n :=
  n_right n ; idtac "blut" ; first [left ; t  ; righter_tac1 t constr:(S n) | t ].

                         
Ltac blut := let e := revert_intro_ex_tac; reflexivity in 
  righter_tac1 e 0.

(* Ltac incr_subg t  := let i:= 0 in destruct t ;    *)


From Coq Require Import List Utf8.
Import ListNotations.

Ltac bar :=
  match goal with
  | |- _ \/ _ => left ; bar
  | |- _ \/ _ => right ; bar
  | |- exists x, _ => eexists ; bar
  | |- _ => reflexivity
  end.

Lemma foo :
  ∀ (x : list nat),
 (1 = 0)  \/   x = [] ∨
    (∃ (x0 : nat) (lx1 : list nat), x = x0 :: lx1).
Proof.
  intro x. destruct x; bar. 
  (* destruct x. left. reflexivity. right. eexists. eexists.  *)
Qed.


Ltac ctor_ex_case := 
  match goal with
  | |- _ \/ _ => left ; ctor_ex_case
  | |- _ \/ _ => right ; ctor_ex_case
  | _ =>  revert_intro_ex_tac ; reflexivity
  end.
(* to much backtracking *)



Ltac codom_union_total_tac B lf lA :=
  let toto := fresh "H" in pose_unquote_term_hnf (codom_union_total B lf lA) toto ; assert toto; unfold toto ;[ (let x := fresh "x" in intro x ; destruct x ; ctor_ex_case ) | ..] ; subst toto. (* \Q pq ctor_ex_case ; subst toto n'élimine-t-il pas toto ? *)


(*    let h := fresh "x" in revert h  ; (let e' := intro h ; e ; exists h in revert_intro_ex_tac_aux n e')
  end.           
 *) 
Goal 2 + 2 = 4.
Proof.   
  codom_union_total_tac list_nat_reif [nil_nat_reif ; cons_nat_reif ] [ [] ; [nat_reif; list_nat_reif]].
  reflexivity. 
Qed.

  


Goal (1 = 1 ) \/ (2 = 2 ) \/ (3 = 3) \/ (4 = 4).
Proof.
  left. reflexivity.
Qed.

  

Fail  Ltac ctor_is_inj_tac B f lA  :=
let toto := fresh "H" in  (pose_unquote_term_hnf (is_inj B f lA) toto );  assert toto   ; unfold toto; intros ; [match goal with
                                                                                                            | h : _ = _ |- _ => inversion h                                                                     end  ; repeat split | .. ]; subst toto.

Fail Fixpoint codom_union_total (B : term) (lf : list term) (lA : list (list term)) :=
(* lf is a list of function [f1;...;fn] whose return type is B, lA = [lA1 ; ...; lAn] is the list of the list of the types of the fi, e.g. lA1 is the list of argument types of lA *)
  let fix arg_org (B  t : term) (lf : list term) (lA: list (list term)) :=
      match (lf , lA)  with
      | (f1 :: tllf, lA1 :: tllA)  => (is_in_codom B t f1 lA1) :: (arg_org B t tllf tllA )
      | ([], []) => []
      | _ => [False_reif]               
      end
  in tProd (mkNamed "x") B  (or_nary_reif (arg_org B (tRel 0)  lf lA)).

     
Definition is_in_reif_simple (B t: term) (l : list term) :=
  fold_left ( fun u p => tApp or_reif [ tApp eq_reif [B; t ; u] ;  p ] ) l True_reif .
(* if l1 := [t1,...,tn], returns the reification of (t^u = t1^u) \/ ... \/ (t^u = tn^u) ] *)
(* works when t and the ti have the same type B *)


(*** Propriétés globales des constructeurs ***)

(* \todo  gérer le nom des métavariables produites pas les énoncés, incl. la possibilité de ne pas les nommer *) 




Definition inj_total_disj (B : term) (lf : list term) (lA : list (list term)) := and_nary_reif [are_inj B lf lA ; pairw_disj_codom B lf lA  ; codom_union_total B lf lA ].



                                                                                                           


Ltac inj_total_disj_tac B lf lA   :=
  ctors_are_inj_tac B lf lA  ; pairw_disj_codom_tac B lf lA ; codom_union_total_tac B lf lA.

Ltac inj_disj_tac B lf lA   :=
    ctors_are_inj_tac B lf lA  ; pairw_disj_codom_tac B lf lA .


Ltac inj_ctor_tac f :=
  let idf := fresh "qt" in pose_quote_term f idf ;
  let ty := (type of f) in
  let idty := fresh "qty" in
  pose_quote_term ty idty ;
  let lAB := constr:(dom_and_codom_sim idty)
  in lazymatch eval hnf in lAB with
     | (?x, ?y) => let lA := (eval cbv in x) in  let B := eval cbv in y in ctor_is_inj_tac B idf lA ; clear idf ; clear idty
  end.
 


Goal 2 + 2 = 4.
Proof.
inj_ctor_tac cons_nat.
reflexivity. Qed.

Print list_nat_reif.
Print list_nat_env_reif.

Ltac goal_inj_total_tac :=
  match goal with
    | [ _ : _ |- _ : ?B] => fail                    
end.     


MetaCoq Unquote Definition itd_nat := (inj_total_disj nat_reif [zero_reif ; S_reif] [ [] ; [nat_reif]] ).
Print itd_nat.

Goal 2+ 2 = 4.
Proof.
inj_total_disj_tac nat_reif [zero_reif ; S_reif] [ [] ; [nat_reif]].
reflexivity.
Qed.

Print typed_term.



MetaCoq Unquote Definition itd_list_nat := (inj_total_disj list_nat_reif [nil_nat_reif ; cons_nat_reif] [ [] ; [nat_reif ; list_nat_reif ]] ).
Print itd_nat.

Goal 2 + 2 = 4.
Proof.
inj_total_disj_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [ [] ; [nat_reif ; list_nat_reif ]].
  reflexivity.
Qed.

Goal 2 + 2 = 4.
Proof.
  inj_total_disj_tac Nforest_reif [Nleaf_reif ; Ncons_reif] [[nat_reif] ; [Ntree_reif ; Nforest_reif]].
reflexivity.
Qed.

Print Nforest.
MetaCoq Unquote Definition itd_Nforest := (inj_total_disj Nforest_reif [Nleaf_reif ; Ncons_reif] [[nat_reif] ; [Ntree_reif ; Nforest_reif]]).
Print itd_Nforest.


Fail MetaCoq Unquote Definition itd_even := (inj_total_disj even_reif [evenS_reif] [ [odd_reif] ] ). (* \! *)
Fail Print itd_even.



Definition dummy_consl := (False_reif , [False_reif] , [[False_reif]] ).

Print InductiveDecl. (* InductiveDecl : mutual_inductive_body -> global_decl *)
Print mutual_inductive_body.  (* ind_bodies : list one_inductive_body; *)
Print one_inductive_body.  (* ind_ctors : list ((ident × term) × nat); *)



Definition list_ctor_oind ( oind : one_inductive_body ) : list term :=
  let fix list_lctor ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => []
  | ((idc , ty) , n ) :: tlctor => list_lctor  tlctor  (ty :: acc) 
  end in  List.rev (list_lctor oind.(ind_ctors) []).
  
Definition dom_list_oind ( oind : one_inductive_body ) := (* unused, delete *)
  let fix dllaux ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => acc
  | ((_ ,tc), n) :: tlctor => let dom_ctor := dom_list_f tc n in dllaux tlctor (dom_ctor :: acc)
  end
  in List.rev (dllaux oind.(ind_ctors) []) . 

 

Print cons_nat_env_reif.

Definition list_nat_oind := ltac:(let s := fresh "s" in pose_mind_tac (list nat) s ; exact s). (*** !!! à mettre dans chlitac *)

(** Definition list_nat_oind := ltac:(let s:= get_mind_tac (list_nat) in exact s). \chli !!! ***)


Print even_env_reif.
Print inj_total_disj.

Print nat_reif.
Print S_reif.
Print tConstruct. 
Print Instance.t.
(* \Q rapport entre ident et termes ? A quoi appliquer prédicats sur constructeurs ? *)
(* tConstruct ind i u *)
(* \ Q tCons ind numéro liste d'univers ? *)

Print inductive. (* inductive_ind : nat champ d'inductif *)
(* \Q où est spécifié le nombre d'inductifs ? *)
Print mutual_inductive_body. (* \Q ind_npars = nombre d'ijnductifs ? ou doit-on lire le nombre de oind ? *)
Print one_inductive_body. (* \Q doit-on lire le nombre de constructeurs ? *) 
Print lookup_env.
Print global_env. (* global_env = list (kername × global_decl) : Type *)
Print kername. (* modpath x ident *)
Print one_inductive_body.
Print tConstruct. (*  tConstruct : inductive -> nat -> Instance.t -> term *)
Print tInd.  (* tInd : inductive -> Instance.t -> term *)
Print inductive. (* Record inductive : Set := mkInd { inductive_mind : kername;  inductive_ind : nat } *)
(* \Q comment fait-on l'induction e.g. sur un record dont un champ est inductif à part ac un let in ? *)

Print map.
Print cons_env_reif.



Inductive tutu : nat -> Type :=
| Tutu : tutu (let fix toto (n:nat) := match n with O => O | S p => p end in toto 17).

Print evenS_env_reif.
Print mkInd.

Print nat_reif. 
Definition nat_indu := 
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}.

Print nat_env_reif.
Definition nat_oind' := 
  ltac:(let s := fresh "s" in pose_mind_tac (nat) s ; exact s).  



Print even_reif.
Definition even_indu := {| inductive_mind := (MPfile ["tinkeringwithReifiedInductives"], "odd"); inductive_ind := 1 |}.

Print even_env_reif.
Definition even_oind := ltac:(let s :=  fresh "s" in pose_oind_tac even 0 s; exact s).

  


Definition switch_inductive ( indu : inductive) (i : nat) :=
  match indu with 
  | {| inductive_mind := kn ; inductive_ind := k |} => {| inductive_mind := kn ; inductive_ind := i |}
end.
 

Print list_env_reif.

Print subst0.


Print list_env_reif.
(* type de cons: tProd 
(mkNamed "A")
 (tSort _  (tProd mkNAnon (tRel 0) (tProd mkNAnon 
   (tApp (tRel 2) [tRel 1])
   (tApp (tRel 3) [tRel 2]))) *)



Fixpoint remove_binding_param (T: term) (p : nat ) := 0.



(* 
Fixpoint apply_param (T : term) (lA: list term) :=
  match T with 
  | tProd _ tRel i => 
    match lA with
    | A :: tlA => [] (* subst *)  
    | [] => []  (* this case should  not occur *)
    end
  | _ => []  (* this case should  not occur *)
  end.
*)


Fixpoint debruijn_mess_aux (indu : inductive ) (p: nat) (sp: nat) (n : nat) (u : Instance.t)  (k: nat) (lA : list term) (B: term):=
  (* not (yet?) tail-recursive *)
  (* indu: un inductive , p: nombre de paramètres n nombre de types inductifs dans indu,
   sp : nombre de binders supprimés (optimiser cette partie du code)
  k : profondeur de dB , lA: liste des p types des paramètres, B : type d'un constructeur, qui comporte des tReli correspondant aux constructeurs de i*)
  match B with  (* cas crucial *)
    | tRel j  =>
    match (Nat.leb (j + 1) (k - p), Nat.leb (j+1) k)  with
    | (true , _ ) => tRel j
    | (false,true) => nth (k - j - 1) lA imposs_mark
    | _ => tInd (switch_inductive indu (n +k - 1 - j) ) u  (* in practice, j >= k + n impossible *)
    end
      (* \Q utiliser lift0 1 pour la suite ? probablement pas, parce que comportement trop différent *)
  | tProd na ty body  => if Nat.eqb sp 0 then 
  tProd na (debruijn_mess_aux indu p sp n u  k lA ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body) 
  else  (debruijn_mess_aux indu p (sp - 1) n u  (k+1) lA body) 
  | tLambda na ty body => tLambda na (debruijn_mess_aux indu p sp n u  k lA ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body) 
  | tLetIn na def def_ty body => tLetIn na (debruijn_mess_aux indu p sp n  u  k lA def  ) (debruijn_mess_aux indu p sp n u  k lA def_ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body ) 
  | tApp f lg => tApp (debruijn_mess_aux indu p sp n u  k lA f ) (map (debruijn_mess_aux indu p sp n u k lA) lg)                      
  | _ => B  (* tVar, tEvar, tCast, tSort, tFix, tCofix,tCase  *) 
  end.



  Check debruijn_mess_aux.

Example dbmaO :=  Eval cbn in (debruijn_mess_aux nat_indu 0 0 1 []  0 [] (tRel 0)).
(* tRel 0 : décla de O dans nat_oind *)
Print dbmaO.

Print nat_indu.
Print nat_oind.
Example dbmaS :=  Eval cbn in (debruijn_mess_aux nat_indu 0 0 1 []  0 [] (tProd mkNAnon (tRel 0) (tRel 1))).
(* (tProd mkNAnon (tRel 0) (tRel 1)) : décla de S dans nat_oind *)
Print dbmaS.
MetaCoq Unquote Definition typ_S := dbmaS.
Print typ_S.
Print listS_env_reif.
Print listS_reif.
Definition listS_indu := {| inductive_mind := (MPfile ["tinkeringwithReifiedInductives"], "listS"); inductive_ind := 0 |}.
Print consS_typ.

Example dbmaconsS := Eval cbn in (debruijn_mess_aux listS_indu 0 0 1 [] 0 [] consS_typ).
Print dbmaconsS.
(* tProd "A" Set_reif. tProd mkNAnon (tRel 0). tProd (listS_reif (Rel 1) ). listS_reif (Rel 2)  *)
Example dlist_consS := Eval cbn in dom_list_f dbmaconsS 3. (*\! \Q cbn et cbv évaluent Set_reif très différemment *)
Print dlist_consS.
(* [ Set_reif ; Rel 0 ; (listS_reif (Rel 1))] *)

Example dbmaevenS := Eval cbn in (debruijn_mess_aux even_indu 0 0 2 [] 0 
[]                                  (tProd (mkNamed "n")
                                 (tInd
                                    {|
                                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                    inductive_ind := 0 |} [])
                                 (tProd mkNAnon (tApp (tRel 2) [tRel 0])
                                    (tApp (tRel 2)
                                       [tApp
                                          (tConstruct
                                             {|
                                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                             inductive_ind := 0 |} 1 []) [tRel 1]])))).
Print dbmaevenS. (* tProd nat_reif tProd (odd_reif (Rel 0)) . (even_reif (S_reif (Rel 1)))  *)
Print evenS. (* evenS forall n : nat, odd n -> even (S n) *) 


Print list_env_reif.
Print nil_env_reif.
Print InductiveDecl.
Print list_reif.
Definition list_indu := {|
inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
inductive_ind := 0 |}.

Example nil_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 1 1 [] 0  [nat_reif]
(tProd (mkNamed "A") (tSort  (Universe.from_kernel_repr
   (Level.Level "Coq.Init.Datatypes.60", false) [])) 
     (tApp (tRel 1) [tRel 0])).
     
MetaCoq Unquote Definition nil_dbm_unquote := nil_dbm_try.
Print nil_dbm_unquote.

Example cons_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 1 1 [] 0  [nat_reif]
(tProd (mkNamed "A")
                                  (tSort
                                     (Universe.from_kernel_repr
                                        (Level.Level "Coq.Init.Datatypes.60",
                                        false) []))
                                  (tProd mkNAnon (tRel 0)
                                     (tProd mkNAnon 
                                        (tApp (tRel 2) [tRel 1])
                                        (tApp (tRel 3) [tRel 2]))))
.
MetaCoq Unquote Definition cons_dbm_unquote := cons_dbm_try.
Print cons_dbm_unquote.



(* \anomaly 
MetaCoq Unquote Definition typ_evensS := dbmaevenS. *)
(* Print typ_evenS. *)


Print nat_reif.



Definition get_ctors_and_types_i (indu : inductive) (p: nat) (n: nat) (i : nat) (u : Instance.t) (lA : list term) (oind : one_inductive_body ) :=
              (* n: nombre de oind *)
              (* i: est le numéro de oind dans le mutual inductive block *)
              (* quelle est la fonction de oind ? sans doute un membre de indu *)
let indui := switch_inductive indu i in 
  let fix treat_ctor_oind_aux (indu : inductive) (n : nat) (j: nat)   (l : list ((ident * term) * nat  ))  :=
    match l with
      | [] => ( [] , [])
      | ctor :: tll => let '((idc , typc) , nc ) := ctor in 
      let (tll1,tll2) := (treat_ctor_oind_aux indu  n (j+1)  tll) in
      ( (tApp  (tConstruct indui j u) lA )   :: tll1 , (dom_list_f (debruijn_mess_aux indui p p n u 0 lA typc) nc) :: tll2 ) 
    end in let oind_split := treat_ctor_oind_aux indu n 0  oind.(ind_ctors)  in (oind_split.1 , oind_split.2).

(*get_ctors_and_types_i:
  1ère proj: tous les constructeurs du i-ème bloc
  2ème proj: la liste de domaines (chaque domaine est une liste) de ces constructeurs *)


  (* voir si les constructeurs sont bien appliqués *)
Print inj_total_disj.
Print get_ctors_and_types_i.

Goal forall (l : list_nat), (l = [] ) \/ (exists n l0, l = n :: l0).
Proof.  
  intros. destruct l.
  - (* congruence fails *) left. reflexivity.
  - right. (* congruence fails *) exists n. exists l. reflexivity. 
Qed.


Print Ltac reflexivity.




(* MetaCoq Unquote Definition tclo_nat1' := (Eval cbn in (2+4)). *)

Definition bid := (3,4).
Definition bid' := let (a,_) := bid in a.
Eval cbv in bid'.
Print bid'.

Definition hd' := hd imposs_mark.
Definition hd'' := hd [imposs_mark].


Definition tructruc := (let (a,b) := (get_ctors_and_types_i  nat_indu 0 1 0 [] [] nat_oind)  in  hd' (hd'' (tl b))). 
Eval cbn in tructruc.
Print tructruc.

MetaCoq Unquote Definition tclo_nat1' := tructruc.
Print tclo_nat1'.

Definition list_oind := ltac:(let s := fresh "s" in pose_oind_tac list 0 s ; exact s).
  


Print list_env_reif. Print InductiveDecl.

Definition list_mind :=  ltac:(let s := fresh "s" in pose_mind_tac list s ; simpl in s; exact s).


Example list_get_ctors_types1 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' (tl (hd'' (tl b))).
MetaCoq Unquote Definition gct_list_unquote1 := list_get_ctors_types1.
Eval cbn in gct_list_unquote1.
Print gct_list_unquote1. 


Example list_get_ctors_types2 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' (tl a).
MetaCoq Unquote Definition gct_list_unquote2 := list_get_ctors_types2.
Eval cbn in gct_list_unquote2.
Print gct_list_unquote2. (* cons nat as expected*)

Example list_get_ctors_types3 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' a.
MetaCoq Unquote Definition gct_list_unquote3 := list_get_ctors_types3.
Eval cbn in gct_list_unquote3.
Print gct_list_unquote3. (* nil nat as expected*)



Print Nforest_reif.
Definition Ntree_indu := {| inductive_mind := (MPfile ["pxtp_pierre"], "Ntree"); inductive_ind := 1 |}.
Print Ncons_env_reif.

Definition Ntree_mind :=  ltac:(let s:= fresh "s" in pose_mind_tac Ntree s ; exact s ).
  

  
Print Ntree_mind.
      
Definition Ntree_oind := 
   ltac:(let s:= fresh "s" in pose_oind_tac Ntree 0 s ; exact s ).
      

Definition Nforest_oind :=
  ltac:(let s:= fresh "s" in pose_oind_tac Ntree 1 s ; exact s ).




Ltac match_let_in l :=
  match l with
  | [] => constr:((4,5))
  | ?c  :: ?tll => match c with 
   | (?a,?b) => a 
  end end.

Ltac nested_fun x := let gag := fresh "gaga" in let g y z := (pose y as z) in g x gag.


Goal 2+ 2 = 4.
Proof.
ltac:(let idgo := fresh "gogo" in let gogo := match_let_in constr:([(2,3);(4,9); (7,8)]) in (pose gogo as idgo)).
nested_fun  49.
reflexivity. Qed.

Print get_ctors_and_types_i.

Ltac treat_ctor_list_oind_tac_i_gen statement indu p n i  u lA oind  :=
  (* n: nombre de oind *)
  (* i: est le numéro de oind dans le mutual inductive block *)
 let indui := constr:(switch_inductive indu i)
 in let B := constr:(tApp (tInd indui u) lA)
 in  let gct :=
  constr:(get_ctors_and_types_i indu  p n i u lA oind) 
  in lazymatch eval cbv in gct with 
  | (?lf,?lA) =>
  statement B lf lA
  end.

Ltac treat_ctor_list_oind_tac_i :=  treat_ctor_list_oind_tac_i_gen inj_total_disj_tac.

Ltac interpretation_alg_types_oind_i :=  treat_ctor_list_oind_tac_i_gen inj_disj_tac.

Print Ltac inj_total_disj_tac.
  
  Goal 2+ 2 = 4.
  Proof.
    treat_ctor_list_oind_tac_i  nat_indu 0 1 0 ([] : Instance.t) ([] : list term) nat_oind.
  reflexivity.
  Qed.
  

Goal False.
Proof.
  treat_ctor_list_oind_tac_i  list_indu 1 1 0 ([] : Instance.t) [nat_reif] list_oind.
Abort.



(* appelle treat_ctor_list_oind *)



Print List.length.
Check List.length.

Ltac treat_ctor_mind_aux_tac_gen statement indu p n  u  mind  i lA loind :=
 lazymatch eval cbv in loind with
| nil => idtac ""
| ?oind :: ?tlloind => treat_ctor_list_oind_tac_i_gen statement indu p n i u lA oind ; 
treat_ctor_mind_aux_tac_gen statement indu p n u mind constr:(S i) lA tlloind
end.
    (* nombre de oind *)
    (* i est le numéro de oind dans le mutual inductive block *)
(* mind est-il vraiment nécessaire ?*)


Ltac treat_ctor_mind_tac_gen statement indu p n u lA mind  
:=  let loind := constr:(mind.(ind_bodies)) in 
treat_ctor_mind_aux_tac_gen statement indu p n u mind 0  lA loind. 
   
Ltac treat_ctor_mind_tac := treat_ctor_mind_tac_gen inj_total_disj_tac.

Ltac interpretation_alg_types_mind_tac := treat_ctor_mind_tac_gen inj_disj_tac.


Goal False.
Proof.
  (* treat_ctor_mind_tac Ntree_indu 0 2 ([] : Instance.t)  ([] : list term) Ntree_mind. *)
Abort.

Goal False.
Proof.
  treat_ctor_mind_tac list_indu 1 1 ([] : Instance.t)  [nat_reif] list_mind.
Abort.

Print mutual_inductive_body.
Print nat_reif.

(* \Q u ne doit il pas être un param d'un global_env_ext ? *)


Print inductive_mind.

Print InductiveDecl.

Ltac fo_prop_of_cons_tac_gen statement t := (* reste à traiter quand inductive *sans* paramètre *)
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) => lazymatch eval hnf in ind with (* voir si hnf marche !!!! *)
     | tApp ?iu ?lA =>
       lazymatch eval hnf in iu with
       | tInd ?indu ?u => 
     let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
       lazymatch eval cbv in lkup  with
       | Some ?d =>   idtac "Some d";(* *) 
         match d with
         |  InductiveDecl ?mind => let indu_p := constr:(mind.(ind_npars)) in 
            let n := constr:(List.length mind.(ind_bodies)) in treat_ctor_mind_tac_gen statement indu indu_p n u lA mind ; clear rqt
         end       
       end
       end         
     end
     end
    .

Ltac fo_prop_of_cons_tac := fo_prop_of_cons_tac_gen inj_total_disj_tac.

Ltac interpretation_alg_types_tac := fo_prop_of_cons_tac_gen inj_disj_tac.

Ltac is_not_in_tuple p z := 
lazymatch constr:(p) with
| (?x, ?y) => constr_neq y z ; idtac "1" z ; is_not_in_tuple constr:(x) z ; idtac "2" p
| I => idtac "3"
end.

Ltac interp_alg_types_goal_aux p :=
match goal with 
| |- context C[?y] => is_not_in_tuple p y ; let Y := type of y in let Y' := eval hnf in 
Y in is_type_quote Y' ; interpretation_alg_types_tac y ; idtac "foo" ; try (interp_alg_types_goal_aux (p, y))
end.

Ltac interp_alg_types_goal := interp_alg_types_goal_aux (I, Z, bool).

Goal forall (x : nat) (l : list nat) (u : Z), x = x /\ l =l /\ u=u.
interp_alg_types_goal.
Abort.

(*TODO : affiner la liste des types à ne pas interpréter *)

Goal 2+2 = 4.
Proof.
fo_prop_of_cons_tac (list nat).
clear. interpretation_alg_types_tac (list nat).
Fail fo_prop_of_cons_tac nat. (* parce qu'on ne matche que des tApp *)
Fail fo_prop_of_cons_tac Ntree.  
reflexivity.
Qed.


(*End Inductives_to_FO.*)
