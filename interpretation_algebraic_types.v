From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import List String.  
(* Require Import utilities. *)
Require Import ZArith.


Open Scope string_scope.  

Import ListNotations MonadNotation. 



Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).

Goal False.
  pose_quote_term nat nat_reif.
Abort.  






Ltac unquote_type t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e t.

Ltac unquote_type0 t idn := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) .

Ltac unquote_type1 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e idn . 

Ltac unquote_type2 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e . 
Ltac cbv1 t := eval cbv in t.

Ltac unquote_type_cbv' t idn :=  unquote_type t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv t idn :=  unquote_type t idn cbv1. 

Ltac unquote_type_cbv1 t idn := unquote_type1 t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv2 t idn := unquote_type2 t idn ltac:(cbn in idn).
 


Definition MonProjT1 t := ret (my_projT1 t).

(* Print TemplateMonad.
Print typed_term.
Print Monad. *)
(* Record Monad (m : Type -> Type) : Type := Build_Monad
  { ret : forall t : Type, t -> m t;  bind : forall t u : Type, m t -> (t -> m u) -> m u } *)
(* Print ret. *)
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



Goal 2+2 = 4.
Proof.
  list_ctors_and_types nat.
  rec_quote_term nat truc.
  pose (fst truc) as truc'.
  Eval cbn in truc'.
  reflexivity.
  Abort.




Ltac unquote_term t idn e := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); e idn.




Ltac pose_unquote_term_hnf t idn  := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); cbv in idn.

Ltac unquote_term_cbv' t idn  := unquote_term t idn ltac:(fun x => cbv in x).



Goal 2 + 2 = 4.
Proof.
pose_quote_term 0 zero_reif.
pose_unquote_term_hnf zero_reif zero_hopefully.
unquote_term_cbv' zero_reif zero_hopefully'.
reflexivity.
Qed.


(* Ltac uqt t idn := (run_template_program (tmUnquote t ) (fun x => pose  x as blut)); 
 pose (mpT2ltac blut) as idn. *)


Goal 2 + 2 = 4.
Proof.
pose_quote_term 2 nat_reif.  

  reflexivity.
  Qed.

  
Ltac uqt t idn ty := (run_template_program (r <- tmUnquote t  ;; @ret TemplateMonad ty (my_projT1 r)) (fun x => pose  x as idn)).

 Goal 2+ 2 = 4.
  pose_quote_term 0 zero_reif. unquote_type_cbv' zero_reif nat_type.
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
(* Print S_env_reif.
Print S_reif. *)
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
MetaCoq Quote Recursively Definition nat_env_reif := nat.


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
(* Print list_reif_generic.
Print list_reif.  *)
(* idem *)
MetaCoq Quote Recursively Definition list_env_reif := @list.


Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat. 
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).



Definition eq_nat := @eq nat.
(* Print eq_nat. *)

MetaCoq Quote Definition Type_reif := Eval cbn in Type.
MetaCoq Quote Definition Prop_reif := Eval cbn in Prop. 
MetaCoq Quote Definition Set_reif := Eval cbn in Set. 

MetaCoq Quote Definition eq_reif := Eval cbn in @eq. 
Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].
 


(*\evar MetaCoq Quote Definition eq_reif_generic := Eval cbn in eq.  *)
(*\evar Print eq_reif_generic. *) (* \Q comment se débarrasser du tEvar ? *)

MetaCoq Quote Definition eq_nat_reif := Eval cbn in (@eq nat).
(* Print eq_nat_reif. *)

MetaCoq Quote Definition eq_term_reif := Eval cbn in (@eq term).
(* Print eq_term_reif.*)



MetaCoq Quote Definition True_reif := Eval cbn in True.
MetaCoq Quote Definition False_reif := Eval cbn in False.
(* MetaCoq Quote Definition and_reif := Eval cbn in "/\".*) (* \! ambiguïté *) 
(* Quote the *string* "/\" *)
MetaCoq Quote Definition and_reif := Eval cbn in and.
MetaCoq Quote Definition or_reif := Eval cbn in or.

 
MetaCoq Unquote Definition two_unreif := two_reif.


MetaCoq Unquote Definition list_nat_unreif := list_nat_reif.


MetaCoq Quote Definition and_reif_ex1 := (and (1 = 1) (0 = 1)).
MetaCoq Unquote Definition and_unreif_ex1 := and_reif_ex1.

(** reified equalities **)

MetaCoq Quote Definition zero_equal_zero_reif := Eval cbn in (eq 0 0).                                                    
MetaCoq Quote Definition zero_equal_zero_reif' := Eval cbn in (@eq nat 0 0).                                                    
MetaCoq Quote Definition zero_equal_zero_reif'' := Eval cbn in (eq_nat 0 0).
(* Print zero_equal_zero_reif'. 
Print zero_equal_zero_reif.
Print zero_equal_zero_reif''.                                                      *) 


(** list in Set **)
Inductive listS (A : Set) :=
| nilS : listS A
| consS : A -> listS A -> listS A
.
MetaCoq Quote Definition listS_reif := listS.
MetaCoq Quote Definition nilS_reif := nilS.
MetaCoq Quote Definition consS_reif := consS.
MetaCoq Quote Recursively Definition listS_env_reif := listS.

MetaCoq Quote Definition lam_true_reif := (forall (A: Type), True).
(* Print lam_true_reif. *)
MetaCoq Quote Definition T_imp_T_reif :=  (True -> True).
(* Print T_imp_T_reif. *)



Definition mkNamed s := ({| binder_name := nNamed (s%string); binder_relevance := Relevant |} : aname).
Definition mkNAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

Definition mkNamedtry := mkNamed (("B"%string) : ident).


Definition consS_typ := tProd (mkNamed "A") (tSort (Universe.from_kernel_repr (Level.lSet, false) []))
                                  (tProd mkNAnon (tRel 0)
                                     (tProd mkNAnon (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))).






(** reified connectives **)




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

Definition mkOr (A B : term) := tApp or_reif [A ; B].

Fixpoint and_nary_reif (l : list term):=
  match l with
  | [] => False_reif      
  | t :: [] => t         
  | t :: tll => mkAnd t (and_nary_reif tll)                
  end.



Fixpoint or_nary_reif (l : list term):=
  match l with
  | [] => False_reif           
  | t :: [] => t
  | t :: tll => tApp or_reif [t ; or_nary_reif tll ]                
  end.


Fixpoint build_prod (B : term) (lA : list term) :=
  match lA with
  | [] => B
  | A1 :: tllA  => tProd mkNAnon A1 (build_prod B tllA )
  end.


Definition get_kn_term (t: term) :=
  (* gets the kername of a reified inductive *)
  (* dummy kn in all other cases *)
  (* should probably extended *)
  match t with 
   |  tInd indu _ => inductive_mind indu
   |  _ => ( MPfile ([] : list ident), "dummy")
  end. 

Definition dom_list_f ( B  :  term) (n : nat)  :=
  (* takes a type B := Prod A1 ... An . B'  and outputs (B,[A1; ... ; An]), at least if no dependencies *)
  (* does not handle debruijn indices *)
  let fix dlaux B n acc :=
  match n with
  | 0 => (B,List.rev acc) 
  | S n => match B with
          | tProd na A B' =>  dlaux B' n (A :: acc)
          | _ => (B,[]) (* this case shouldn't happen *)
          end            
  end
  in dlaux B n [].


Example dlf1 := Eval cbn in dom_list_f cons_nat_type_reif 2.

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

    
(***  Marks impossible cases ***)

Inductive impossible_type : Type  := .

MetaCoq Quote Definition imposs_mark :=  impossible_type  .






(** ** Auxiliary functions *)






Definition ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.



(*** extracting parameters ****)



Ltac get_ind_param t idn := 
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
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
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
     | tApp ?iu ?lA =>  
       (lazymatch eval hnf in iu with
       | tInd ?indu ?u => pose (Sigma,((indu,u),lA)) as idn ; clear rqt
       end )
     | tInd ?indu ?u => pose (Sigma,((indu,u),([]: list term))) as idn ; clear rqt
     end
     end.

Goal False.
Proof.
let s1 := fresh "s1" in get_env_ind_param (list nat) s1.
get_env_ind_param list foo.
let s2 := fresh "s2" in get_ind_param (nat) s2.
Abort.



Ltac pose_mind_tac t idn :=   (* factoriser code !*)
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
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
         | Some ?d =>    
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
       | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
       | tApp ?iu ?lA =>   
         lazymatch eval hnf in iu with
         | tInd ?indu ?u => 
       let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
         lazymatch eval cbv in lkup  with
         | Some ?d =>   
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



(*** Properties of inductives ***)

Fixpoint forall_nary lx lA B:=
  match (lx,lA) with
  | (hx :: tx, hA :: tA) => tProd hx hA (forall_nary tx tA B)
  | _ => B
end.


 

Polymorphic Fixpoint and_eq_combine_reif (lA l1 l2 : list term) :=
(* if l1=[t1,...,tn], l2=[u1,...,un], lA=[A1,...An] and ti,ui: have type Ai, outputs the reification of   t1^ = u1^ /\ ... /\ tn^ /\ un^ ]. One must specify, the type of the terms *)
        match (lA , l1, l2) with
  | (A::[], x1 :: [], x2 :: []) =>  tApp eq_reif [A; x1; x2] 
  | (A1 :: tlA, x1 :: tl1, x2 :: tl2) =>  tApp and_reif ((tApp eq_reif [A1; x1 ; x2]) ::  [and_eq_combine_reif tlA tl1 tl2] )
  | (_, [] , [] ) => True_reif                                         
  | (_ ,_ ,_) => False_reif (* return False if length l1 neq l2 *)
end.


(*** Injectivity ***)


Fixpoint splitList {A : Type} (l : list A) (p : nat) :=
  match (l,p) with  (* à écrire en récursif terminal*)
  | ( _ , 0) => ([],l)
  | ([] , _ ) => ([],[])
  | (x :: l , S p ) => let (l1,l2) := splitList l p in ( x :: l1, l2)
  end.

Fixpoint listDB (d : nat) (p : nat) := 
  match p with
  | 0 => []
  | S p => (tRel  (d + p + 1)) :: listDB d   p
  end.

(* tests subst*)

Definition t1 := tApp (tRel 0) [tRel 1 ; tRel 2].
Definition t2 := Eval cbv in subst0 [True_reif] t1.
Print t2.
(* descend les dB*)

Print lift0.

Definition cutEvar (t: term) :=
  (* perhaps a bit naive *)
  match t with 
  | tApp t' ((tEvar _ _ ) :: u) =>  t'
  | _ => t
  end.


    
   
Fixpoint new_inj_aux (B f : term ) (lA : list term) (p : nat) (l1 l2 : list term ) :=
  let n := List.length lA in 
  let d := n - p in let f' := cutEvar f in 
  let fix aux1 (lA : list term) (p i j : nat) (l1 l2 : list term) :=
    match (lA , p ) with 
    | ([], _) =>   (l1 , l2)  
    | (A :: lA, 0) => let A' := lift0 i A in let A'' := lift0 j A' in 
    aux1 lA 0 (i+1) (j-2) (((lift0 1 A') :: A' :: l1) ) (A'' :: l2) 
    | (A :: lA, S p) =>   aux1 lA  p i j (A :: l1) l2
    end in let (l1, l2) := aux1 lA p 0 (S(2 * d)) [] [] in let d' := 2 * d - 2 in 
  let fix aux2 (k i  : nat) (l2 dB1 dB2 : list term) (andeq : term) :=
    match (k , l2) with 
    | (0, _) =>  (dB1 , dB2 , andeq )  
    | (S k, []) => aux2 k (i+1) [] ((tRel i) :: dB1 ) ((tRel i) :: dB2) andeq
    | (S k, A' :: l2) =>  aux2 k (i + 2)  l2 ( (tRel (i+1)) :: dB1 ) ((tRel i) :: dB2 ) (mkAnd (mkEq  A' (tRel (S (S i))) (tRel (S i) )) andeq) (* manque cas où l2' singleton pour éliminer True_reif *)
    end in let '((dB1 , dB2), andeq) := aux2 n 0 l2 [] [] True_reif in 
    let fix aux3 l1 t :=
      match l1 with 
      | [] => t
      |  A :: l1 => aux3 l1 (tProd (mkNamed "x") A t)
      end in (* mkEq (lift0 d B) (tApp (cutEvar f) dB1) (tApp (cutEvar f) dB2) *)   aux3 l1 (tProd mkNAnon (mkEq (lift0 d B) (tApp f' dB1) (tApp f' dB2)) andeq)   
    .
   

Definition truc := Eval compute in (new_inj_aux  (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]   1 [] []).
MetaCoq Unquote Definition trucu := truc. 
Print trucu.

Definition new_is_inj B f lA  p := new_inj_aux B f lA  p [] [].
Check new_is_inj.

Print truc.
Print cons_reif.
Check cons.

Inductive list' (A : Type) : Type :=
 | nil' : list' A 
 | cons' : A -> list' A -> list' A
.

MetaCoq Quote Definition cons_reif' := cons'.
Check cons'.
Print list.
Print cons_reif.
Print cons_reif'.



Definition truc' := Eval cbv in forall (A: Type) (x1 x2 : A) (x3 x4: list A), True.
MetaCoq Quote Definition trucu' := (forall (A: Type) (x1 x2 : A) (x3 x4: list A), True).
Print trucu'.

MetaCoq Quote Definition cons_inj_reif :=
  (forall (A: Set) (x1 x2: A) (l1 l2: list A), x1 :: l1 = x2 :: l2 -> ((x1 = x2) /\ (l1 = l2))).
  Check cons.
MetaCoq Quote Definition cons_typ_reif := (forall (A : Type), A -> list A -> list A).
Print cons_typ_reif.
(* tProd A Type_reif tProd _ O tProd _ (tApp list_reif 1) (tApp list_reif 2)*) 
Print cons_inj_reif.
(* 
(tProd A Set_reif 
  (tProd x1 0 
    (tProd x2 1 
      (tProd l1 (tApp list_reif [2]))
        (tProd l2 (tApp list_reif [3])) 
           tProd nAnon (eq_reif [list_reif [4] ]
              (cons_reif [4, 3, 1]  )
              (cons_reif) [4, 2 , 0]
             ))))
             and_reif [eq_reif [5, 4 , 3]] ] [eq_reif [tApp list_reif 5, 2 1]]


*)



Fixpoint is_inj (B f: term) (lA : list term)   :=
let fix inj_aux (B f1 f2: term) (lA : list term) (n: nat)  :=
  match lA with
  | []  => (fun (t : term) => t, f1 , f2 , True_reif )
  | [A]  => 
   (fun (t: term) => (tProd (mkNamed "x") A (tProd (mkNamed  "y") (lift0 1 A) t  )),  (tApp (lift0 2 f1) [tRel 1]) , (tApp (lift0 2 f2) [tRel 0]), mkEq A (tRel 0) (tRel 1))
  | A1 :: tllA => let blut := inj_aux B (tApp (lift0 2 f1) [tRel 1]) (tApp (lift0 2 f2) [tRel 0]) tllA (n-1)   in
                (fun (t: term) => (tProd (mkNamed "x") A1 (tProd (mkNamed "y") (lift0 1 A1) (blut.1.1.1 t)  )), blut.1.1.2, blut.1.2,  mkAnd (lift0 (2*(n-1)) (mkEq A1 (tRel 0) (tRel 1)))  blut.2 )
  end in 
   let kik := inj_aux B f f  lA (List.length lA)  in kik.1.1.1 (mkImpl  (mkEq B kik.1.1.2 kik.1.2) kik.2   ) . 



Definition S_inj_reif :=  (is_inj nat_reif S_reif [nat_reif]).

MetaCoq Unquote Definition really_S_inj_reif := S_inj_reif.
Print really_S_inj_reif.

MetaCoq Unquote Definition O_inj := (is_inj nat_reif O_reif []).
Print O_inj.


MetaCoq Unquote Definition really_cons_nat_inj_reif := (is_inj list_nat_reif cons_nat_reif  [nat_reif; list_nat_reif]).
Print really_cons_nat_inj_reif. 



Ltac just_cbv t := cbv in t.

Goal 2 + 2 = 4.
Proof.  pose ( String.append "hello " "world") as H. just_cbv H.
reflexivity. Qed.



Ltac ctor_is_inj_tac B f lA  :=
  lazymatch eval hnf in lA with
  | [] => idtac 
  | ?x :: ?tlA =>
let toto := fresh "H" in  (pose_unquote_term_hnf (is_inj B f lA) toto );  assert toto   ; [ unfold toto; intros ;
 match goal with  
 | h : _ = _ |- _ => inversion h    
 end  ; 
 repeat split | .. ]; 
 subst toto                                             
 end.  

 Ltac new_ctor_is_inj_tac B f lA  p  :=
  lazymatch eval hnf in lA with
  | [] => idtac 
  | ?x :: ?tlA =>
let toto := fresh "H" in  (pose_unquote_term_hnf (new_is_inj B f lA  p) toto );  assert toto   ; [ unfold toto; intros ;
 match goal with  
 | h : _ = _ |- _ => inversion h    
 end  ; 
 repeat split | .. ]; 
 subst toto                                             
 end.  

 Print list_reif.

MetaCoq Unquote Definition is_inj_cons :=
(new_is_inj (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]  1).
Print is_inj_cons.

Goal False.
Proof.  new_ctor_is_inj_tac (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]  1.
Abort.

MetaCoq Unquote Definition is_inj_cons_nat := (is_inj list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif]).

Goal forall (n: nat), 2 + 2 = 4.
Proof.
  ctor_is_inj_tac list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif].  reflexivity. Abort.


Goal forall (n: nat), 2 + 2 = 4.
Proof.
  new_ctor_is_inj_tac list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif] 0.
  new_ctor_is_inj_tac nat_reif O_reif (@nil term) 0.
  ctor_is_inj_tac nat_reif O_reif (@nil term).
  reflexivity. Abort.
                                                                                                


Definition nilterm := @nil term.

Check nil.
MetaCoq Quote Definition nil_type_reif := (forall (A : Set), list A).
Print nil_type_reif.

Ltac ctors_are_inj_tac lB lf lA p :=  
  match lA with
  |  nil  => idtac 
  | ?A1 :: ?tlA => match lf with 
    | nil => idtac  
    | ?f1 :: ?tlf => match lB with
      | nil => idtac 
      | ?B1 :: ?tlB => 
  new_ctor_is_inj_tac B1 f1 A1  p; ctors_are_inj_tac tlB tlf tlA p
    end
  end
  end.
  

Goal 2 + 2 = 4.
Proof. 
ctors_are_inj_tac [list_nat_reif ; list_nat_reif] [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] 0. 
 (ctors_are_inj_tac [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [ nil_reif ; cons_reif] [ [Set_reif] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]] 1). 
reflexivity. Abort.
                                                                
(*** Constructeurs disjoints : fail ***)

Definition same_dom_Set (B Af Ag f g: term)  (l1 l2: list term) :=
  (* of course, we cannot specify that f and g are definitionally equal *)
  (* B: common return type of g and g *)
  (* right now, specifies that f and g have the same type  instead of the having the same dom*)
mkImpl (tApp eq_reif [B ; tApp f l1 ; tApp g l2 ])  (tApp eq_reif [Set_reif; Af ; Ag] ) .
(* \! stupide: il suffirait de dire que  l1 = l2 *)



Example same_dom_Set_1 := same_dom_Set list_nat_reif cons_nat_type_reif list_nat_reif cons_nat_reif nil_nat_reif [zero_reif ; nil_nat_reif ] [].
MetaCoq Unquote Definition sds_unreif1 := same_dom_Set_1.
(* Print sds_unreif1. *)

   
  
  
(*** Disjoints codomains ***)




Fixpoint codom_disj (B f g: term)  (lAf lAg : list term)  : term :=
  match lAf  with
  | [] => (fix codom_disj_aux B f g lAg  := match lAg with
         | [] => mkNot (tApp eq_reif [B ; f ;  g])
         | A1 :: tllAg  =>  tProd mkNAnon A1 (codom_disj_aux B  (lift0 1 f) (tApp  (lift0 1 g) [tRel 0]) tllAg  )
         end ) B f g lAg          
  | A1 :: tllAf => tProd mkNAnon A1 (codom_disj B (tApp (lift0 1 f) [tRel 0] )   (lift0 1 g) tllAf lAg  ) 
  end.

  Fixpoint new_codom_disj (B f g: term)  (lAf lAg : list term) (p : nat)  :=
    let (n,n') := (List.length lAf , List.length lAg) in 
    let (d,d') := ( n - p, n' - p) in 
    let fix removeandlift p l :=
      match (p, l)  with
      | (0 , _) => List.rev (lAf ++ List.map (lift0 d) l) 
      | ( S p , x :: l) => removeandlift p l 
      | ( S _, []) => [] (* this case doesn't happen *)
      end 
    in let lQ := removeandlift p lAg 
    in let fix aux2 p i dB  :=
      match p with 
      | 0 => dB
      | S p => aux2  p (S i)  ((tRel i) :: dB)
      end 
     in let (dB1,dB2) := (aux2 d d'  [], aux2 d' 0 []) 
     in let fix aux3 p i l1 l2 :=
       match p with
       | 0 => (l1,l2)
       | S p => aux3 p (S i)  (tRel i :: l1) (tRel i :: l2)
       end 
      in let (l1,l2) := aux3 p (d + d') dB1 dB2 in
      let fix aux3  l t := match l with
      | [] => t 
      | A' :: l => aux3 l (tProd (mkNamed "x") A' t)
      end in   aux3 lQ (mkNot (mkEq (lift0 d' B) (tApp (cutEvar f) l1) (tApp (cutEvar g) l2))).  
     

  Example disj_codom1 := new_codom_disj list_nat_reif nil_nat_reif nil_nat_reif [ ] [] 0.
  (* MetaCoq Unquote Definition dcodu1 := disj_codom1. 
  Print dcodu1. *)

MetaCoq Quote Definition disj_cons_cons := (forall (A : Set) (x1 : A) (l1 : list A) (x2 : A) (l2 : list A), x1 :: l1 <> x2 :: l2) .  
Print disj_cons_cons.

Example disj_cons_cons2 := Eval compute in new_codom_disj (tApp list_reif [tRel 2]) cons_reif cons_reif  [Set_reif; tRel 0 ; tApp list_reif [tRel 1] ]    [Set_reif; tRel 0 ; tApp list_reif [tRel 1] ] 1.
Print disj_cons_cons2. 
MetaCoq Unquote Definition dccu2 := disj_cons_cons2. 
Print dccu2. 

MetaCoq Quote Definition disj_nil_cons := (forall (A : Set) x l, @nil A <> x :: l ).
Print disj_nil_cons.

Example disj_codom2 := Eval compute in new_codom_disj (tApp list_reif [tRel 0]) nil_reif cons_reif   [Set_reif ] [Set_reif; tRel 0 ; tApp list_reif [tRel 1] ] 1.
Print disj_codom2.
MetaCoq Unquote Definition dcodu2 := (new_codom_disj (tApp list_reif [tRel 0]) nil_reif cons_reif   [Set_reif ] [Set_reif; tRel 0 ; tApp list_reif [tRel 1] ] 1).
Print dcodu2.

Example disj_codom2' := Eval compute in new_codom_disj (tApp list_reif [tRel 2])  cons_reif nil_reif   [Set_reif; tRel 0 ; tApp list_reif [tRel 1] ] [Set_reif ] 1.
Print disj_codom2'.
MetaCoq Unquote Definition dcodu2' := disj_codom2'.
Print dcodu2'.


Example disj_codom3_no_param := Eval compute in (new_codom_disj list_nat_reif nil_nat_reif  cons_nat_reif   (@nil term) [ nat_reif ; list_nat_reif ] 0).
Print disj_codom3_no_param.
MetaCoq Unquote Definition dcodu3 := disj_codom3_no_param.
Print disj_codom3_no_param.  



Ltac codom_disj_discr B f g lAf lAg p:=
  let toto := fresh "H" in (pose_unquote_term_hnf (new_codom_disj B f g lAf lAg p) toto);
  assert toto; [unfold toto ; intros ;
  try discriminate | .. ] ; subst toto. 

      
                            

Goal 2 + 2 = 4.
Proof.
  codom_disj_discr list_nat_reif nil_nat_reif  cons_nat_reif  (@nil term) [ nat_reif ; list_nat_reif ] 0. 
reflexivity. Abort.


Goal 2 + 2 = 4.
Proof. 
  codom_disj_discr list_nat_reif nil_nat_reif  cons_nat_reif  (@nil term) [ nat_reif ; list_nat_reif ] 0. 
Abort. 


Example disj_codom4 := Eval cbn in new_codom_disj list_nat_reif cons_nat_reif cons_nat_reif [nat_reif ; list_nat_reif ] [nat_reif ; list_nat_reif ] 0.
MetaCoq Unquote Definition d_cod_u4 := disj_codom4. 
(* Print d_cod_u2. *)



Fixpoint pairw_disj_codom ( B : term) (lf : list term) (lA : list (list term)) (p : nat) :=
  let fix pairw_aux (B f : term) (lAf lf : list term)  (lA : list (list term)) :=
      match (lf , lA) with
        | ([] , []) => True_reif
        | (f1 :: tllf , A1 :: tllA ) => mkAnd (new_codom_disj B f f1 lAf A1 p) (pairw_aux B f lAf tllf tllA)
        | _ => False_reif   
      end        
      in 
  match (lf , lA)  with
  | ([] , [] ) => True_reif
  | (f1 :: tllf  , A1 :: tllA ) => mkAnd (pairw_aux B f1 A1 tllf tllA) (pairw_disj_codom B tllf tllA p)
  | _ => False_reif                                     
  end.


Ltac pairw_aux B f lAf lf lA p :=
     lazymatch constr:((lf , lA)) with
        | ([] , []) => idtac 
        | (?f1 :: ?tllf , ?A1 :: ?tllA ) => codom_disj_discr B f f1 lAf A1 p  ; pairw_aux B f lAf tllf tllA p
        | _ => idtac "wrong branch pairw_aux"  ; fail                                             
      end.

Goal 2 + 2 = 4.
  Proof.
      pairw_aux list_nat_reif nil_nat_reif  (@nil term) [cons_nat_reif]  [ [nat_reif; list_nat_reif]] 0.
      reflexivity. Abort. 
 
    
Ltac pairw_disj_codom_tac B  lf  lA p :=
  match constr:((lf , lA))  with
  | ([] , [] ) => idtac 
  | (?f1 :: ?tllf  , ?A1 :: ?tllA ) => ltac:(pairw_aux B f1 A1 tllf tllA p) ; ltac:(pairw_disj_codom_tac B tllf tllA p)
  | _ => idtac "wrong branch pair_disj_codom_tac"                                
  end.

Goal nat -> 2 + 2 = 4.
Proof.
 pairw_disj_codom_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] 0.  
reflexivity. Abort.

Goal nat -> 2 + 2 = 4.
Proof.
  pairw_disj_codom_tac (tApp list_reif [tRel 0])  [nil_reif ;  cons_reif]   [[Set_reif ]  ;[Set_reif; tRel 0 ; tApp list_reif [tRel 1] ]] 1.
Abort. 

Example pwdc1 := pairw_disj_codom list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] 0.
MetaCoq Unquote Definition pwdcu1 := pwdc1.
(* Print pwdcu1. *)




(*** Constructeurs totaux ***)






Ltac intros_exist_aux n e := 
  lazymatch n with
  | 0 => e
  | S ?n =>
    let h := fresh "x" in
    intro h ;
    let e' := e  ; exists h in
    intros_exist_aux n e'
  end.

 Goal forall (n m k: nat), exists (x y z: nat), x = n /\ y = m /\ z = k .
 Proof. intros_exist_aux  3 ltac:(idtac).  let x := fresh "x" in let x:= fresh "x" in idtac. repeat split.
Abort.
        


MetaCoq Quote Definition ex_ex_reif2 := Eval cbn in (@ex nat (fun n => True) ).  
(* Print ex_ex_reif2. (* pas de tEvar *)
Print ex. *) 
(* Inductive ex (A : Type) (P : A -> Prop) : Prop :=  ex_intro : forall x : A, P x -> exists y, P y *)







Fixpoint is_in_codom (B t f: term ) (lA : list term) :=
  (* if t : A and f : Pi lx lA . A, tells when t is in the codomain of f: returns exist vecx : lA, f vecx = t  *)
  match lA with
  | [] => tApp eq_reif [B ; t ; f]
  | A :: tllA => tApp ex_reif [A ;  tLambda (mkNamed "x") A   (is_in_codom B (lift0 1 t) (tApp (lift0 1 f) [tRel 0] )   tllA  )]
  end.
(* base case : f is 0-ary and  t is just f *)



Definition union_direct_total (lB : list term ) (lf : list term) (lD : list (list term) ) (p : nat) :=
  let lD' := List.map (fun l => (@List.skipn term p l)) lD in 
  let lLen := List.map  (fun l => (@List.length term l) ) lD' in 
  let fix aux0 k i l  :=
    (* outputs [tRel (i+k) ; ... ; tRel i ] ++ l *)
    match k with
    | 0 => l
    | S k => aux0 k (i + 1) (tRel i :: l)
    end
  in
  let fix aux1 lArev t :=
    match lArev with
    | [] => t 
    | A :: lArev => aux1 lArev (tApp ex_reif [(lift0 1 A) ; tLambda (mkNamed "x") (lift0 1 A) t])
    end 
  in 
  let aux2 B f lA k := aux1 (List.rev lA) (mkEq (lift0 1 B) (tRel k) (tApp f (aux0 p (k+1) (aux0 k 0 [])))) in 
  let fix aux3 lB lf lD lLen t := 
    match (((lB, lf) , lD), lLen )  with
    | ((([], []),[]),[]) => t
   (* | ([f], [lA],[d]) => aux2  lA f d  ??? *)
    | (((B :: lB, f:: lf), lA :: lD), d :: lLen) => aux3 lB lf lD lLen (mkOr (aux2 B (cutEvar f) lA d) t)
    | _ => True_reif (* this case should not happen *)
    end in 
    let lExist := 
      aux3 lB lf lD' lLen False_reif in 
    let fix aux4 l p  l':= 
      match (l,p) with
      (* taks [A_1,...,A_n], outputs [A_p,...,A_1]*)
      | (_, 0 ) => l' 
      | ( [], _) => l'
      | (A :: l,S p ) => aux4 l p (A :: l')
      end in 
      let lAforall :=
      match lB with
      | [] => []
      | B :: lB => match lD with
      | [] => []
      | lA :: lD => B :: (aux4 lA p [])
      end
      end
      in 
      let fix aux5 lA t := 
        match lA with
        | [] => t
        | A :: lA => aux5 lA (tProd (mkNamed "x") A t)
        end
        in aux5 lAforall lExist.



MetaCoq Quote Definition nut1_check := (forall (A : Set) (l : list A), l = nil \/ (exists x l0, l = x :: l0)).
Print nut1_check.


Example nut1 := Eval compute in union_direct_total [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [(cutEvar nil_reif) ; (cutEvar cons_reif) ] [ [Set_reif ] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1] ]] 1.
Print nut1.
Print ex.


MetaCoq Unquote Definition nut1u := nut1.
Print nut1u.








(* p (forall)  1 (forall) d_1 (exist) (d_2) 
                           +1          1+ d_1 etc
*)

Print list_env_reif.

Example in_codom1 := is_in_codom nat_reif  one_reif add_reif [nat_reif ; nat_reif ].
MetaCoq Unquote Definition in_codom_unreif1 := in_codom1.
(* Print in_codom_unreif1. *)

Example in_codom'1 := tProd (mkNamed "y") nat_reif (is_in_codom nat_reif  (tRel 0) add_reif [nat_reif ; nat_reif ]).
MetaCoq Unquote Definition in_codom_unreif'1 := in_codom'1.
(* Print in_codom_unreif'1. *)


Example in_codom2 := is_in_codom nat_reif  two_reif S_reif [nat_reif ].
MetaCoq Unquote Definition in_codom_unreif2 := in_codom2.
(* Print in_codom_unreif2. *)


Example in_codom'2 := tProd (mkNamed "x") nat_reif  (is_in_codom nat_reif  (tRel 0) S_reif [nat_reif ]) .
MetaCoq Unquote Definition in_codom_unreif'2 := in_codom'2.
(* Print in_codom_unreif'2.*)


Example in_codom3 := Eval cbn in is_in_codom list_nat_reif nil_nat_reif cons_nat_reif [nat_reif ; list_nat_reif].
MetaCoq Unquote Definition in_codom_unreif3 := in_codom3.
(* Print in_codom_unreif3. *)

Example in_codom4 := Eval cbn in (tProd (mkNamed "y") list_nat_reif ( is_in_codom list_nat_reif (tRel 0) cons_nat_reif [nat_reif ; list_nat_reif])).
MetaCoq Unquote Definition in_codom_unreif4 := in_codom4.
(* Print in_codom_unreif4. *)


Example in_codom'4 := Eval cbn in (tProd (mkNamed "y") list_nat_reif ( is_in_codom list_nat_reif (tRel 0) cons_nat_reif [nat_reif ; list_nat_reif])).
MetaCoq Unquote Definition in_codom_unreif'4 := in_codom'4.
(* Print in_codom_unreif'4. *)



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
(* Print cdu_u1. *)


Example cdu2 := codom_union_total nat_reif [ O_reif; S_reif ] [ []; [nat_reif ]].
MetaCoq Unquote Definition cdu_u2 := cdu2.
(* Print cdu_u2. *)

Example cdu3 := codom_union_total list_nat_reif [cons_nat_reif ] [ [nat_reif ; list_nat_reif ] ].
MetaCoq Unquote Definition cdu_u3 := cdu3.
(* Print cdu_u3. *)


Example cdu_4 := codom_union_total Prop_reif [evenS_reif] [[nat_reif (* ; reif de even n*)  ]].
(* should tell that what ???? *) 
Fail MetaCoq Unquote Definition cdu_u4 := cdu_4.


Example cdu'1 := codom_union_total nat_reif [zero_reif ; S_reif ] [ [] ; [nat_reif]].
MetaCoq Unquote Definition cdu_u'1 := cdu'1.
(* Print cdu_u'1. *)




Example cdu'2 := codom_union_total list_nat_reif [nil_nat_reif ; cons_nat_reif ] [ [] ; [nat_reif; list_nat_reif]].
MetaCoq Unquote Definition cdu_u'2 := cdu'2.
(* Print cdu_u'2. *)



Ltac revert_intro_ex_tac_aux e :=
    match goal with
        | H : _ |- _ =>  first [ revert H ;  let e':= (intro H; e)  in revert_intro_ex_tac_aux  e'  ; exists H   | e]
end.

Ltac revert_intro_ex_tac  := revert_intro_ex_tac_aux ltac:(idtac).

Ltac n_right n :=
  match n with
  | O => idtac 
  | S ?n => right; n_right n             
  end.
    
Ltac right_k_n k n :=
  match n with
  | O => idtac 
  | S ?n
    => match k with
      | O => idtac 
      | S ?k => right ;  right_k_n k n
      end
  end.

Ltac righter_tac1 t n :=
  n_right n ; idtac ; first [left ; t  ; righter_tac1 t constr:(S n) | t ].

                         
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
(* too much backtracking *)

(*
Ltac codom_union_total_tac B lf lA :=
  let toto := fresh "H" in pose_unquote_term_hnf (codom_union_total B lf lA) toto ; assert toto; unfold toto ;[ (let x := fresh "x" in intro x ; destruct x ; ctor_ex_case ) | ..] ; subst toto. *) 
  (* \Q pq ctor_ex_case ; subst toto n'élimine-t-il pas toto ? *)


Ltac dotac n t :=
  match constr:(n) with
  | 0 => idtac
  | S ?k => t ; dotac k t
  end.



Ltac codom_union_total_tac lB lf lD p :=
  let toto := fresh "H" in pose_unquote_term_hnf (union_direct_total lB lf lD p) toto ; assert toto; unfold toto ;[ dotac p intro ; (let x := fresh "x" in intro x ; destruct x ; ctor_ex_case ) | ..] ; subst toto. 

(*    let h := fresh "x" in revert h  ; (let e' := intro h ; e ; exists h in revert_intro_ex_tac_aux n e')
  end.           
 *) 
Goal 2 + 2 = 4.
Proof.   
  codom_union_total_tac [list_nat_reif ; list_nat_reif ] [nil_nat_reif ; cons_nat_reif ] [ [] ; [nat_reif; list_nat_reif]] 0.
  codom_union_total_tac  [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [(cutEvar nil_reif) ; (cutEvar cons_reif) ] [ [Set_reif ] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1] ]] 1.
  reflexivity. 
Qed.

  

  
    

(*** Global properties of constructors ***)


                                                                                                           
Ltac inj_total_disj_tac B lf lA   :=
  ctors_are_inj_tac B lf lA  ; pairw_disj_codom_tac B lf lA ; codom_union_total_tac B lf lA.

Ltac inj_disj_tac lB lf lA p  :=
  lazymatch eval hnf in lB with
   | ?B :: ?tlB =>
    ctors_are_inj_tac lB lf lA p  ; idtac "kikoo2"   ;pairw_disj_codom_tac B lf lA p ;  idtac "kikoo3"  
    end ; idtac "kikoo4".


Ltac goal_inj_total_tac :=
  match goal with
    | [ _ : _ |- _ : ?B] => fail                    
end.     


Goal 2+ 2 = 4.
Proof.
  inj_disj_tac [list_nat_reif ; list_nat_reif] [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] 0.
  (inj_disj_tac  [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [ nil_reif ; cons_reif] [ [Set_reif] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]] 1). (* \todo : probleme, le fait qu'il y ait un paramètre fait que l'injectivité de nil est affirmée et prouvée, contrairement à nil_nat *)
  inj_disj_tac  [nat_reif  ; nat_reif] [O_reif  ; S_reif] [  [] ; [nat_reif]] 0.  
reflexivity.

Abort.

Goal 2 + 2 = 4.
Proof.
Fail inj_total_disj_tac [list_nat_reif] [nil_nat_reif ; cons_nat_reif] [ [] ; [nat_reif ; list_nat_reif ]].
  reflexivity.
Abort.

Goal 2 + 2 = 4.
Proof.
  Fail inj_total_disj_tac Nforest_reif [Nleaf_reif ; Ncons_reif] [[nat_reif] ; [Ntree_reif ; Nforest_reif]].
reflexivity.
Abort.






Definition list_ctor_oind ( oind : one_inductive_body ) : list term :=
  let fix list_lctor ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => []
  | ((idc , ty) , n ) :: tlctor => list_lctor  tlctor  (ty :: acc) 
  end in  List.rev (list_lctor oind.(ind_ctors) []).
  
(* Definition dom_list_oind ( oind : one_inductive_body ) := (* unused, delete *)
  let fix dllaux ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => acc
  | ((_ ,tc), n) :: tlctor => let dom_ctor := dom_list_f tc n in dllaux tlctor (dom_ctor :: acc)
  end
  in List.rev (dllaux oind.(ind_ctors) []) .  *)

(* Check dom_list_oind. *)
  
Definition ctor_info_oind ( oind : one_inductive_body ) :=
    0. (* \todo : censé faire quoi ?*)


Definition list_nat_mind := ltac:(let s := fresh "s" in pose_mind_tac (list nat) s ; exact s). 


Inductive tutu : nat -> Type :=
| Tutu : tutu (let fix toto (n:nat) := match n with O => O | S p => p end in toto 17).


Definition nat_indu := 
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}.


Definition nat_oind' := 
  ltac:(let s := fresh "s" in pose_mind_tac (nat) s ; exact s).  


Definition even_indu := {| inductive_mind := (MPfile ["tinkeringwithReifiedInductives"], "odd"); inductive_ind := 1 |}.

Definition even_oind := ltac:(let s :=  fresh "s" in pose_oind_tac even 0 s; exact s). 


Definition switch_inductive ( indu : inductive) (i : nat) :=
  match indu with 
  | {| inductive_mind := kn ; inductive_ind := k |} => {| inductive_mind := kn ; inductive_ind := i |}
end.

 

(* Print list_env_reif. *)
(* type de cons: tProd 
(mkNamed "A")
 (tSort _  (tProd mkNAnon (tRel 0) (tProd mkNAnon 
   (tApp (tRel 2) [tRel 1])
   (tApp (tRel 3) [tRel 2]))) *)





Fixpoint debruijn_mess_aux (indu : inductive ) (p: nat) (sp: nat) (n : nat) (u : Instance.t)  (k: nat) (lA : list term) (B: term):=

  match B with 
    | tRel j  =>
    match (Nat.leb (j + 1) (k - p), Nat.leb (j+1) k)  with
    | (true , _ ) => tRel j
    | (false,true) => nth (k - j - 1) lA imposs_mark
    | _ => tInd (switch_inductive indu (n +k - 1 - j) ) u  (* in practice, j >= k + n impossible *)
    end

  | tProd na ty body  => if Nat.eqb sp 0 then 
  tProd na (debruijn_mess_aux indu p sp n u  k lA ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body) 
  else  (debruijn_mess_aux indu p (sp - 1) n u  (k+1) lA body) 
  | tLambda na ty body => tLambda na (debruijn_mess_aux indu p sp n u  k lA ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body) 
  | tLetIn na def def_ty body => tLetIn na (debruijn_mess_aux indu p sp n  u  k lA def  ) (debruijn_mess_aux indu p sp n u  k lA def_ty) (debruijn_mess_aux indu p sp n u  (k+1) lA body ) 
  | tApp f lg => tApp (debruijn_mess_aux indu p sp n u  k lA f ) (map (debruijn_mess_aux indu p sp n u k lA) lg)                      
  | _ => B  (* tVar, tEvar, tCast, tSort, tFix, tCofix,tCase  *) 
  end.



(* Check debruijn_mess_aux. *)

Example dbmaO :=  Eval cbn in (debruijn_mess_aux nat_indu 0 0 1 []  0 [] (tRel 0)).
(* tRel 0 : décla de O dans nat_oind *)
(* Print dbmaO. *)

(* Print nat_indu.
Print nat_oind. *)
Example dbmaS :=  Eval cbn in (debruijn_mess_aux nat_indu 0 0 1 []  0 [] (tProd mkNAnon (tRel 0) (tRel 1))).
(* (tProd mkNAnon (tRel 0) (tRel 1)) : décla de S dans nat_oind *)
(* Print dbmaS. *)
MetaCoq Unquote Definition typ_S := dbmaS.
(* Print typ_S.
Print listS_env_reif.
Print listS_reif. *)
Definition listS_indu := {| inductive_mind := (MPfile ["tinkeringwithReifiedInductives"], "listS"); inductive_ind := 0 |}.
(* Print consS_typ. *)

Example dbmaconsS := Eval cbn in (debruijn_mess_aux listS_indu 0 0 1 [] 0 [] consS_typ).
(* Print dbmaconsS. *)
(* tProd "A" Set_reif. tProd mkNAnon (tRel 0). tProd (listS_reif (Rel 1) ). listS_reif (Rel 2)  *)
Example dlist_consS := Eval cbn in dom_list_f dbmaconsS 3. 
(* Print dlist_consS. *)
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
(* Print dbmaevenS. *)
(* tProd nat_reif tProd (odd_reif (Rel 0)) . (even_reif (S_reif (Rel 1)))  *)
(* Print evenS. *)
(* evenS forall n : nat, odd n -> even (S n) *) 



Definition list_indu := {|
inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
inductive_ind := 0 |}.

Example nil_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 1 1 [] 0  [nat_reif]
(tProd (mkNamed "A") (tSort  (Universe.from_kernel_repr
   (Level.Level "Coq.Init.Datatypes.60", false) [])) 
     (tApp (tRel 1) [tRel 0])).
     
MetaCoq Unquote Definition nil_dbm_unquote := nil_dbm_try.
(* Print nil_dbm_unquote. *)

Example cons_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 1 1 [] 0  [nat_reif]
(tProd (mkNamed "A")
                                  (tSort
                                     (Universe.from_kernel_repr
                                        (Level.Level "Coq.Init.Datatypes.60",
                                        false) []))
                                  (tProd mkNAnon  (tRel 0)
                                     (tProd mkNAnon 
                                        (tApp (tRel 2) [tRel 1])
                                        (tApp (tRel 3) [tRel 2]))))
.
MetaCoq Unquote Definition cons_dbm_unquote := cons_dbm_try.
(* Print cons_dbm_unquote. *)



Definition get_ctors_and_types_i (indu : inductive) (p: nat) (n: nat) (i : nat) (u : Instance.t) (lA : list term) (oind : one_inductive_body ) :=
              (* n: nb of oind *)
              (* i: indice of oind in the mutual inductive block *)
let indui := switch_inductive indu i in 
  let fix treat_ctor_oind_aux (indu : inductive) (n : nat) (j: nat)   (l : list ((ident * term) * nat  ))  :=
    match l with
      | [] => ([], [] , [])
      | ctor :: tll => let '((_ , typc) , nc ) := ctor in 
      let '((tll1,tll2),tll3) := (treat_ctor_oind_aux indu  n (j+1)  tll) in let (B_ctor, lA_ctor) :=  dom_list_f (debruijn_mess_aux indui p p n u 0 lA typc) nc in
      (B_ctor :: tll1, (tApp  (tConstruct indui j u) lA )   :: tll2 , lA_ctor :: tll3 ) 
    end in let oind_split := treat_ctor_oind_aux indu n 0  oind.(ind_ctors)  in (oind_split.1 , oind_split.2).

Check get_ctors_and_types_i.


Goal forall (l : list_nat), (l = [] ) \/ (exists n l0, l = n :: l0).

Proof.  
  intros. destruct l.
  - (* congruence fails *) left. reflexivity.
  - right. (* congruence fails *) exists n. exists l. reflexivity. 
Abort.


(* Print Ltac reflexivity.*)




(* MetaCoq Unquote Definition tclo_nat1' := (Eval cbn in (2+4)). *)



Definition hd' := hd imposs_mark.
Definition hd'' := hd [imposs_mark].
(* il faut un hd en plus pour les B *)

Definition gctt_ex1 := (let '((c,a),b) := (get_ctors_and_types_i  nat_indu 0 1 0 [] [] nat_oind)  in  hd' (hd'' (tl b))). 
Eval cbn in gctt_ex1.
Print gctt_ex1. 

MetaCoq Unquote Definition tclo_nat1' := gctt_ex1.
Print tclo_nat1'. 

Definition list_oind := ltac:(let s := fresh "s" in pose_oind_tac list 0 s ; exact s).
  

Definition list_mind :=  ltac:(let s := fresh "s" in pose_mind_tac list s ; simpl in s; exact s).


Example list_get_ctors_types1 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' (tl (hd'' (tl b))).
MetaCoq Unquote Definition gct_list_unquote1 := list_get_ctors_types1.
Eval cbn in gct_list_unquote1.
(* Print gct_list_unquote1.  *)

(*
Example list_get_ctors_types2 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' (tl a).
MetaCoq Unquote Definition gct_list_unquote2 := list_get_ctors_types2.
Eval cbn in gct_list_unquote2.
Print gct_list_unquote2.  *)
(* cons nat as expected*)

(* 
Example list_get_ctors_types3 := let (a,b) := get_ctors_and_types_i list_indu 1 1 0 [] [nat_reif] list_oind in hd' a.
MetaCoq Unquote Definition gct_list_unquote3 := list_get_ctors_types3.
Eval cbn in gct_list_unquote3. *)
(* Print gct_list_unquote3.  *)
(* nil nat as expected*)

(* Example list_get_ctors_types_4 := let (a,b) := get_cotrs_and_types_i  *)

Definition Ntree_indu := {| inductive_mind := (MPfile ["pxtp_pierre"], "Ntree"); inductive_ind := 1 |}.
(* Print Ncons_env_reif. *)

Definition Ntree_mind :=  ltac:(let s:= fresh "s" in pose_mind_tac Ntree s ; exact s ).

      
Definition Ntree_oind := 
   ltac:(let s:= fresh "s" in pose_oind_tac Ntree 0 s ; exact s ).
      

Definition Nforest_oind :=
  ltac:(let s:= fresh "s" in pose_oind_tac Ntree 1 s ; exact s ).


(* problème: lB singleton et probablement mal calculé quand paramètres *)
Ltac treat_ctor_list_oind_tac_i_gen statement indu p n i  u lA oind  :=
  (* n: number of oind *)
  (* i: is the rank oind in the mutual inductive block *)
 let indui := constr:(switch_inductive indu i)
 in  idtac "kikoo6" ; let gct :=
  constr:(get_ctors_and_types_i indu p n i u lA oind) 
 in idtac "kikoo7" ; lazymatch eval cbv in gct with 
  | (?lBf,?lA) =>  idtac "kikoo8" ; lazymatch eval cbv in lBf with
  | (?lB,?lf) => idtac "kikoo9bis" ; statement lB lf lA p 
  end end .

Ltac treat_ctor_list_oind_tac_i indu p n i u lA oind :=  idtac "kikoo9" ; treat_ctor_list_oind_tac_i_gen inj_disj_tac indu p n i u lA oind.

Ltac interpretation_alg_types_oind_i :=   treat_ctor_list_oind_tac_i_gen inj_disj_tac.


  
  Goal 2+ 2 = 4.
  Proof.
    treat_ctor_list_oind_tac_i nat_indu 0 1 0 ([] : Instance.t) ([] : list term) nat_oind.
  reflexivity.
  Abort.
  

Goal False.
Proof.
  treat_ctor_list_oind_tac_i  list_indu 1 1 0 ([] : Instance.t) [[Set_reif];[Set_reif ; tRel 0 ;tApp list_reif [tRel 1]] ] list_oind.
  (* problème: pas disj_cons pour list. Sans doute un pb de param ?*)
Abort.



Ltac treat_ctor_mind_aux_tac_gen statement indu p n  u  mind  i lA loind :=
 lazymatch eval cbv in loind with
| nil => idtac 
| ?oind :: ?tlloind => treat_ctor_list_oind_tac_i_gen statement indu p n i u lA oind ; 
treat_ctor_mind_aux_tac_gen statement indu p n u mind constr:(S i) lA tlloind
end.



Ltac treat_ctor_mind_tac_gen statement indu p n u lA mind  
:=  let loind := constr:(mind.(ind_bodies)) in 
treat_ctor_mind_aux_tac_gen statement indu p n u mind 0  lA loind. 
   
Ltac treat_ctor_mind_tac indu p n u lA mind := treat_ctor_mind_tac_gen inj_total_disj_tac p n u la mind p.

Ltac interpretation_alg_types_mind_tac := treat_ctor_mind_tac_gen inj_disj_tac.


Goal False.
Proof.
  (* treat_ctor_mind_tac Ntree_indu 0 2 ([] : Instance.t)  ([] : list term) Ntree_mind. *)
Abort.

Goal False.
Proof.
  treat_ctor_mind_tac list_indu 1 1 ([] : Instance.t)  [nat_reif] list_mind.
Abort.

Ltac fo_prop_of_cons_tac_gen statement t := 
    let geip := fresh "geip" in get_env_ind_param t geip ; 
    lazymatch eval hnf in geip with
    | (?Sigma,?t_reif) => lazymatch eval hnf in t_reif with
      | (?induu,?lA) => lazymatch eval hnf in induu with
      | (?indu,?u) =>      let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
       lazymatch eval cbv in lkup  with
       | Some ?d =>    
         match d with
         |  InductiveDecl ?mind => let indu_p := constr:(mind.(ind_npars)) in 
            let n := constr:(List.length mind.(ind_bodies)) in treat_ctor_mind_tac_gen statement indu indu_p n u lA mind ; clear geip
         end       
       end
       end         
     end
     end
    .

  



Ltac fo_prop_of_cons_tac := fo_prop_of_cons_tac_gen inj_total_disj_tac.

Ltac interp_alg_types := fo_prop_of_cons_tac_gen inj_disj_tac.

Goal False.
interp_alg_types nat.
interp_alg_types (list nat).
Fail interp_alg_types true.
Abort.



(* Check is a MetaCoq term is a sort *)
Definition is_sort (t : term) := match t with
                                 | tSort _ => true
                                 |_ => false
                                  end.
Ltac is_sort_quote t := let t' := eval hnf in t in
quote_term t' ltac:(fun T => if_else_ltac idtac fail ltac:(eval compute in (is_sort T))).




Ltac interp_alg_types_goal_aux p :=
match goal with 
| |- context C[?y] => let Y := type of y in is_not_in_tuple p Y ; 
 interp_alg_types y ;
 try (interp_alg_types_goal_aux (p, Y))
end.

Ltac interp_alg_types_context_aux p :=
match goal with 
| |- context C[?y] => let Y := type of y in
tryif (
is_not_in_tuple p Y ;
interp_alg_types Y) then 
(
interp_alg_types_context_aux (p, Y)) else 
(is_not_in_tuple p y ; 
interp_alg_types y ; 
interp_alg_types_context_aux (p, y))
| _ : context C[?y] |- _ => let Y := type of y in
tryif (
is_not_in_tuple p Y ;
interp_alg_types Y) then 
(
interp_alg_types_context_aux (p, Y)) else 
(is_not_in_tuple p y ; 
interp_alg_types y ; 
interp_alg_types_context_aux (p, y))
| _ => idtac
end.


Definition prod_types := (Z, bool, True, False, and, or).

Ltac interp_alg_types_goal := let p := eval unfold prod_types in prod_types in
interp_alg_types_goal_aux p.
Ltac interp_alg_types_context_goal := 
let p := eval unfold prod_types in prod_types in
(interp_alg_types_context_aux p).


Goal forall (x : option bool) (l : list nat) (u : Z), x = x -> l =l -> u = u.
(* interp_alg_types_goal. *)

interp_alg_types_context_goal.
Abort.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
intros.
interp_alg_types_context_goal.

Abort.



Goal 2+2 = 4.
Proof.
fo_prop_of_cons_tac (list nat).
clear. interp_alg_types (list nat).
fo_prop_of_cons_tac nat. 
fo_prop_of_cons_tac Ntree.  
reflexivity.
Qed.


