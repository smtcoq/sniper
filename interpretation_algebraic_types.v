(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import List String.  
Require Import utilities. 
Require Import ZArith.


Open Scope string_scope.  

Import ListNotations MonadNotation. 



Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).


(*
Goal False.
  pose_quote_term nat nat_reif.
Abort.  
*)

Ltac unquote_type t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e t.

Ltac unquote_type0 t idn := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) .

Ltac unquote_type1 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e idn . 

Ltac unquote_type2 t idn e := (run_template_program (r <- tmUnquote t ;; ret (my_projT1 r)) (fun x => pose  x as idn)) ; e . 
Ltac cbv1 t := eval cbv in t.

Ltac unquote_type_cbv' t idn :=  unquote_type t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv t idn :=  unquote_type t idn cbv1. 

Ltac unquote_type_cbv1 t idn := unquote_type1 t idn ltac:(fun t => hnf in idn).
Ltac unquote_type_cbv2 t idn := unquote_type2 t idn ltac:(cbn in idn).
 



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




Ltac unquote_term t idn e := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); e idn.




Ltac pose_unquote_term_hnf t idn  := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); cbv in idn.

Ltac assert_unquote_term_hnf t  idn := (run_template_program (tmUnquote t ) ltac:(fun x =>  (assert (idn : my_projT2 x)))).


Ltac unquote_term_cbv' t idn  := unquote_term t idn ltac:(fun x => cbv in x).










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

MetaCoq Quote Definition Type_reif := Eval hnf in Type.
MetaCoq Quote Definition Prop_reif := Eval hnf in Prop. 
MetaCoq Quote Definition Set_reif := Eval hnf in Set. 

MetaCoq Quote Definition eq_reif := Eval hnf in @eq. 
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


Definition mkImpl A B := tProd mkNAnon A (lift0 1 B). 

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


(* dom_and_codom_sim is limited because it does not handle an output type that is morally a product *)
(* the 1st element of the output is the list of domains of C and the 2nd element is its codomain *)
Definition dom_and_codom_sim (C : term) := 
  let fix aux C accl  :=
      match C with        
      | tProd _ A B => aux B (A :: accl)
      | _ => (accl , C)
      end
        in let ( lA , B) := aux C [] in (List.rev lA, B).

    
(***  Marks impossible cases ***)

Inductive impossible_type : Type  := .

MetaCoq Quote Definition imposs_mark :=  impossible_type  .


(*** Extracting parameters ****)

Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.

(* 
Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tApp ?iu ?lA =>  
       (lazymatch eval hnf in iu with
       | tInd ?indu ?u => pose (indu,lA) as idn ; clear tq
       end )
     | tInd ?indu ?u =>  pose (indu,([]: list term)) as idn  ; clear tq
     end.
*) 

Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tInd ?indu ?u =>  pose (indu,u) as idn  ; clear tq
     end.



Ltac pose_inductive_tac t idn := let s := fresh "s" in get_ind_param t s ; pose (fst s) as idn ;  simpl in idn ; clear s.

(* 
Goal False.
Proof. let blut := fresh "blut" in pose_inductive_tac (list nat)  blut. Check blut.
Abort.
*)

Ltac get_env_ind_param t idn := 
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
     | tInd ?indu ?u => pose (Sigma,(indu,u)) as idn ; clear rqt
     end
     end.

(*
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
*) 

(* 
Goal False.
Proof.
let s1 := fresh "s1" in get_env_ind_param (list nat) s1.
get_env_ind_param list foo.
let s2 := fresh "s2" in get_ind_param nat s2.
Abort.
*)



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
(*  the tactic uses nat_oind as the defaut value for nth *)

(*
Goal False.
Proof. let blut := fresh "blut" in pose_oind_tac (list nat) 0 blut.
Abort.
*)



(*** Properties of inductives ***)
 


(*** Injectivity ***)



(* tests subst*)

(*
Definition t1 := tApp (tRel 0) [tRel 1 ; tRel 2].
Definition t2 := Eval cbv in subst0 [True_reif] t1.
Print t2.
*)
(* subst makes the dB indice decrease *)


Definition cutEvar (t: term) :=
  (* perhaps a bit naive *)
  match t with 
  | tApp t' ((tEvar _ _ ) :: u) =>  t'
  | _ => t
  end.

(* save 20 sept. 2021

efinition is_inj (B f : term ) (lA : list term) (p : nat)  :=
  let n := List.length lA in 
  let d := n - p in let f' := cutEvar f in 
  let fix aux1 (lA : list term) (p i j : nat) (l1 l2 : list term) :=
    match (lA , p ) with 
    | ([], _) =>   (l1 , l2)  
    | (A :: lA, 0) => let A' := lift0 i A in
     let A'' := lift0 j A' in 
     aux1 lA 0 (i+1) (j - 2) (((lift0 1 A') :: A' :: l1) ) (A'' :: l2) 
    | (A :: lA, S p) =>   aux1 lA  p i j (A :: l1) l2
    end 
  in let (l1, l2) := aux1 lA p 0 (S(2 * d)) [] [] in 
  let d' := 2 * d - 2 in 
  let fix aux2 (k i  : nat) (l2 dB1 dB2 : list term) (andeq : term) :=
    match (k , l2) with 
    | (0, _) =>  (dB1 , dB2 , andeq )  
    | (S k, []) => aux2 k (i+1) [] ((tRel i) :: dB1 ) ((tRel i) :: dB2) andeq
    | (S k, [A'] ) => aux2 k (i + 2) [] (tRel (i+1) :: dB1)  ((tRel i) :: dB2)  (mkEq  A' (tRel (S (S i))) (tRel (S i) )) 
    | (S k, A' :: l2) =>  aux2 k (i + 2)  l2 ( (tRel (i+1)) :: dB1 ) ((tRel i) :: dB2 ) (mkAnd (mkEq  A' (tRel (S (S i))) (tRel (S i) )) andeq) 
    end in let '((dB1 , dB2), andeq) := aux2 n 0 l2 [] [] True_reif in 
    let fix aux3 l1 t :=
      match l1 with 
      | [] => t
      |  A :: l1 => aux3 l1 (tProd (mkNamed "x") A t)
      end in aux3 l1 (tProd mkNAnon (mkEq (lift0 d B) (tApp f' dB1) (tApp f' dB2)) andeq)   
    . 


*)



Definition is_inj (B f : term ) (lA : list term) (p : nat)  :=
  let n := List.length lA in 
  let d := n - p in let f' := cutEvar f in 
  let fix aux1 (lA : list term) (p i j : nat) (l1 l2 : list term) :=
    match (lA , p ) with 
    | ([], _) =>   (l1 , l2)  
    | (A :: lA, 0) => let A' := lift0 i A in
     let A'' := lift0 j A' in 
     aux1 lA 0 (i+1) (j - 2) (((lift0 1 A') :: A' :: l1) ) (A'' :: l2) 
    | (A :: lA, S p) =>   aux1 lA  p i j (A :: l1) l2
    end 
  in let (l1, l2) := aux1 lA p 0 (S(2 * d)) [] [] in 
  let d' := 2 * d - 2 in 
  let fix aux2 (k i  : nat) (l2 dB1 dB2 : list term) (andeq : term) :=
    match (k , l2) with 
    | (0, _) =>  (dB1 , dB2 , andeq )  
    | (S k, []) => aux2 k (i+1) [] ((tRel i) :: dB1 ) ((tRel i) :: dB2) andeq
   (* | (S k, [A'] ) => aux2 k (i + 2) [] (tRel (i+1) :: dB1)  ((tRel i) :: dB2)  (mkEq  A' (tRel (S (S i))) (tRel (S i) )) *) 
    | (S k, A' :: l2) =>  aux2 k (i + 2)  l2 ( (tRel (i+1)) :: dB1 ) ((tRel i) :: dB2 ) (mkAnd (mkEq  A' (tRel (S (S i))) (tRel (S i) )) andeq) 
    end in 
    (* let '((dB1 , dB2), andeq) := aux2 n 0 l2 [] [] True_reif in *)
    let '((dB1 , dB2), andeq) := 
    let '(((((n',i'),l2'),dB1'),dB2'),andeq') := 
    match (n,l2) with 
    | (S n',[]) => (((((n,1),[]),[]),[]),True_reif) 
    | (S n', A' :: l2') =>  (n',2,l2',[tRel 1 ], [tRel 0] , (mkEq  A' (tRel 2) (tRel 1 )))
    | (0, _) => (0,0,l2,[],[],True_reif)
    end 
    in aux2 n' i' l2' dB1' dB2' andeq'  
    in 
    let fix aux3 l1 t :=
      match l1 with 
      | [] => t
      |  A :: l1 => aux3 l1 (tProd (mkNamed "x") A t)
      end in aux3 l1 (tProd mkNAnon (mkEq (lift0 d B) (tApp f' dB1) (tApp f' dB2)) andeq)   
    . 

(* 
Definition inj_test1 := Eval compute in (is_inj  (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]   1  ).
Print inj_test1.
MetaCoq Unquote Definition inj_test1_u := inj_test1. 
Print inj_test1_u.

*)

(* 
Inductive and_Set (A B : Set ) : Set:= conj_Set : A -> B -> and_Set A B.
MetaCoq Quote Definition and_Set_reif := and_Set.
MetaCoq Quote Definition conj_Set_reif := conj_Set.
*)


(* 
Goal False.
Proof. 
  pose_unquote_term_hnf (is_inj (list_nat_reif) cons_nat_reif [nat_reif ; list_nat_reif ] 0) blutt.
  pose_unquote_term_hnf (is_inj Prop_reif and_reif [Prop_reif ; Prop_reif ] 0) blut.
  pose_unquote_term_hnf (is_inj Set_reif and_Set_reif [Set_reif ; Set_reif ] 0) blut'. clear.

Check conj_Set. (* forall A B : Set, A -> B -> and_Set A B *)
pose_unquote_term_hnf (is_inj (tApp and_Set_reif [tRel 3 ; tRel 2]) conj_Set_reif [Set_reif ; Set_reif  ; tRel 1; tRel 1 ] 2) conjblut. 
Abort. *)

(*
Definition S_inj_reif :=  (is_inj nat_reif S_reif [nat_reif] 0).

MetaCoq Unquote Definition really_S_inj_reif := S_inj_reif.
Print really_S_inj_reif.

MetaCoq Unquote Definition O_inj := (is_inj nat_reif O_reif [] 0).
Print O_inj.


MetaCoq Unquote Definition really_cons_nat_inj_reif := (is_inj list_nat_reif cons_nat_reif  [nat_reif; list_nat_reif] 0).
Print really_cons_nat_inj_reif. 
*)



Ltac ctor_is_inj B f lA  n p := 
   match n with
   | 0 => idtac 
   | S _ => let Hu := fresh "H"  in  
  (pose_unquote_term_hnf (is_inj B f lA  p) Hu ); let t := fresh "H" in assert (t:Hu)   ; [  unfold Hu ; intros ;
 match goal with  
 | h : _ = _ |- _ =>  progress (inversion h)   
 end  ; 
 repeat split  | ..]   ; subst Hu
   end.
   

(* MetaCoq Quote Definition and_Set_reif := (forall A B : Set, A -> B -> and_Set A B). *)

(* 
Goal False.
Proof.   ctor_is_inj (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]] 2 1.
ctor_is_inj (list_nat_reif) cons_nat_reif [nat_reif ; list_nat_reif ] 2 0. clear.
assert (blutcons : forall (x x' : nat) (l l' : list nat), x :: l = x' :: l' -> x = x' /\ l = l').
intros. inversion H. split. split. split.  
(* assert (blut : forall (A A' B B' : Set), conj_Set A B = conj_Set A' B' -> A = A' /\ B = B').
intros. inversion H. *)
(* assert (kik : forall (x x0 : Set) (x1 x2 : x) (x3 x4 : x0),
            conj_Set x x0 x1 x3 = conj_Set x x0 x2 x4 -> x1 = x2 /\ x3 = x4 ). 
            intros. inversion H. split. split. split.
assert (blut := is_inj Set_reif and_Set_reif [Set_reif ; Set_reif ]  0).
ctor_is_inj Set_reif and_Set_reif [Set_reif ; Set_reif ] 2 0.
ctor_is_inj Prop_reif and_reif [Prop_reif ; Prop_reif ] 2 0.*)
Abort.
*)

(*
Ltac metacoq_get_value p :=
  let id := fresh in
  let _ := match goal with _ => run_template_program p
  (fun t => pose (id := t)) end in
  let x := eval cbv delta [id] in id in
  let _ := match goal with _ => clear id end in
  x. 

  
  let x := (metacoq_get_value (tmQuoteRec bool)) in assert (y := x).
  *)

(*
MetaCoq Unquote Definition is_inj_cons :=
(is_inj (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]  1).
Print is_inj_cons.



Goal 2 + 2 = 4.
Proof.   assert (x : 2 + 3 = 5). reflexivity. 
ctor_is_inj (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ;  tApp list_reif [tRel 1]]  1 2.
  ctor_is_inj list_nat_reif cons_nat_reif [nat_reif ; list_nat_reif] 0 2. clear.
 ctor_is_inj nat_reif O_reif (@nil term) 0 0 .
 Abort.
  *)                                                                                              


Definition nilterm := @nil term.

(* Check nil. *)
MetaCoq Quote Definition nil_type_reif := (forall (A : Set), list A).
(* Print nil_type_reif. *)


Ltac ctors_are_inj_tac lB lf lA ln p :=  
  match lA with
  |  nil  => idtac 
  | ?A1 :: ?tlA => 
    match lf with 
    | nil => idtac "Wrong branch ctors_are_inj" 
    | ?f1 :: ?tlf =>
      match lB with
      | nil => idtac "Wrong branch ctors_are_inj"    
      | ?B1 :: ?tlB =>
        match ln with
        | nil => idtac "Wrong branch ctors_are_inj"
        | ?n1 :: ?tln  => let Hnew := fresh "H" in 
   ctor_is_inj B1 f1 A1 n1 p ;  
   ctors_are_inj_tac tlB tlf tlA tln p 
         end
      end      
    end
  end.
  

(*  
Goal 2 + 2 = 4.
Proof.  
ctors_are_inj_tac [list_nat_reif ; list_nat_reif] [nil_nat_reif ; cons_nat_reif] [(@nil term) ; [nat_reif; list_nat_reif]] [0 ; 2] 0. 
ctors_are_inj_tac [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [ nil_reif ; cons_reif] [ [Set_reif] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]] [0 ; 1] 1. 
Abort.
*)                                                                
    
  
(*** Disjoints codomains ***)



Definition new_codom_disj (B f g: term)  (lAf lAg : list term) (p : nat)  :=
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
     
(* 
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
*)


Ltac codom_disj_discr B f g lAf lAg p:=
  let H := fresh "H" in (pose_unquote_term_hnf (new_codom_disj B f g lAf lAg p) H); 
  assert  H ; [unfold H ; intros ;
  try discriminate | .. ]  ; subst H. 

      
                            

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



Ltac pairw_aux B f lAf lf lA p :=
     lazymatch constr:((lf , lA)) with
        | ([] , []) => idtac 
        | (?f1 :: ?tllf , ?A1 :: ?tllA ) => codom_disj_discr B f f1 lAf A1 p  ;pairw_aux B f lAf tllf tllA p  
        | _ => idtac "wrong branch pairw_aux"  ; fail                               
      end.

Goal 2 + 2 = 4.
  Proof.
pairw_aux list_nat_reif nil_nat_reif  (@nil term) [cons_nat_reif]  [ [nat_reif; list_nat_reif]] 0.
      reflexivity. Abort. 
 
    
Ltac pairw_disj_codom_tac B lf  lA p := lazymatch eval hnf in lf with
  | [] => idtac  
  | ?f1 :: ?tllf => lazymatch eval hnf in lA with 
    ?A1 :: ?tllA  => pairw_aux B f1 A1 tllf tllA p  ; pairw_disj_codom_tac B tllf tllA p 
  | _ =>   idtac "wrong branch pair_disj_codom_tac"  
  end
  end.

Goal nat -> 2 + 2 = 4.
Proof.
pairw_disj_codom_tac list_nat_reif [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] 0.  
reflexivity. Abort.

Goal nat -> 2 + 2 = 4.
Proof.
  pairw_disj_codom_tac (tApp list_reif [tRel 0])  [nil_reif ;  cons_reif]   [[Set_reif ]  ;[Set_reif; tRel 0 ; tApp list_reif [tRel 1] ]] 1.
Abort. 





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


(* 
MetaCoq Quote Definition nut1_check := (forall (A : Set) (l : list A), l = nil \/ (exists x l0, l = x :: l0)).
Print nut1_check. 


Example nut1 := Eval compute in union_direct_total [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [(cutEvar nil_reif) ; (cutEvar cons_reif) ] [ [Set_reif ] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1] ]] 1.
Print nut1.
Print ex.


MetaCoq Unquote Definition nut1u := nut1.
Print nut1u.


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
*)


Definition codom_union_total (B : term) (lf : list term) (lA : list (list term)) :=
(* lf is a list of function [f1;...;fn] whose return type is B, lA = [lA1 ; ...; lAn] is the list of the list of the types of the fi, e.g. lA1 is the list of argument types of lA *)
  let fix arg_org (B  t : term) (lf : list term) (lA: list (list term)) :=
      match (lf , lA)  with
      | (f1 :: tllf, lA1 :: tllA)  => (is_in_codom B t f1 lA1) :: (arg_org B t tllf tllA )
      | ([], []) => []
      | _ => [False_reif]               
      end
  in tProd (mkNamed "x") B  (or_nary_reif (arg_org B (tRel 0)  lf lA)).


(* 
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

Fail MetaCoq Unquote Definition cdu_u4 := cdu_4.


Example cdu'1 := codom_union_total nat_reif [zero_reif ; S_reif ] [ [] ; [nat_reif]].
MetaCoq Unquote Definition cdu_u'1 := cdu'1.
(* Print cdu_u'1. *)




Example cdu'2 := codom_union_total list_nat_reif [nil_nat_reif ; cons_nat_reif ] [ [] ; [nat_reif; list_nat_reif]].
MetaCoq Unquote Definition cdu_u'2 := cdu'2.
(* Print cdu_u'2. *)

*)

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


(* Ltac incr_subg t  := let i:= 0 in destruct t ;    *)


From Coq Require Import List Utf8.
Import ListNotations.




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
Abort.

  

  
    

(*** Global properties of constructors ***)

Inductive my_type :=
  | A : my_type
  | B : my_type -> my_type
  | C : my_type -> my_type.

MetaCoq Quote Definition mt_reif := my_type.  
MetaCoq Quote Definition A_reif := A. 
MetaCoq Quote Definition B_reif := B.
MetaCoq Quote Definition C_reif := C.

Goal False.
Proof.
ctors_are_inj_tac [mt_reif; mt_reif ; mt_reif ] [A_reif ; B_reif ; C_reif ] [[] ; [mt_reif] ; [mt_reif] ] [ 0 ; 0 ; 0] 0. (* marche*) 
pairw_disj_codom_tac mt_reif [A_reif ; B_reif ; C_reif ] [[] ; [mt_reif] ; [mt_reif] ] 0.
pairw_disj_codom_tac (tApp list_reif [tRel 0])  [ nil_reif ; cons_reif] [ [Set_reif] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]] 1.
Abort.

Ltac inj_total_disj_tac B lf lA   :=
  ctors_are_inj_tac B lf lA  ; pairw_disj_codom_tac B lf lA ; codom_union_total_tac B lf lA.

Ltac inj_disj_tac lB lf lA ln p  :=  
  lazymatch eval hnf in lB with
   | ?B :: ?tlB => ctors_are_inj_tac lB lf lA ln p ; pairw_disj_codom_tac B lf lA  p
    end.


(*
Goal 2+ 2 = 4.
Proof. 
  idtac "NEW TEST 1".
  inj_disj_tac  [nat_reif  ; nat_reif] [O_reif  ; S_reif] [  (@nil term) ; [nat_reif]] [0 ; 1] 0.   
  idtac "NEW TEST 2".
inj_disj_tac [list_nat_reif ; list_nat_reif] [nil_nat_reif ; cons_nat_reif] [[] ; [nat_reif; list_nat_reif]] [0; 2] 0.
inj_disj_tac  [tApp list_reif [tRel 0] ; tApp list_reif [tRel 2]] [ nil_reif ; cons_reif] [ [Set_reif] ; [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]]] [0;2] 1. 
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
*)





Definition list_ctor_oind ( oind : one_inductive_body ) : list term :=
  let fix list_lctor ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => []
  | ((idc , ty) , n ) :: tlctor => list_lctor  tlctor  (ty :: acc) 
  end in  List.rev (list_lctor oind.(ind_ctors) []).
  


(*
Definition list_nat_mind := ltac:(let s := fresh "s" in pose_mind_tac (list nat) s ; exact s). 


Definition nat_indu := ltac:(let s := fresh "s" in pose_inductive_tac nat s; exact s).
Print nat_indu.
Eval compute in nat_indu.
Print nat_indu.





Definition even_indu := ltac:(let s := fresh "s" in pose_inductive_tac even s; exact s).
Eval compute in even_indu.  

Definition even_oind := ltac:(let s :=  fresh "s" in pose_oind_tac even 0 s; exact s). 
*)

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




(* old version: takes lA a list of parameters and outputs the expected type*)
(* Fixpoint debruijn_mess_aux' (indu : inductive ) (p: nat) (sp: nat) (n : nat) (u : Instance.t)  (k: nat) (lA : list term) (B: term):=
  match B with 
    | tRel j  =>
    match (Nat.leb (j + 1) (k - p), Nat.leb (j+1) k)  with
    | (true , _ ) => tRel j
    | (false,true) => nth (k - j - 1) lA imposs_mark
    | _ => tInd (switch_inductive indu (n +k - 1 - j) ) u  (* in practice, j >= k + n impossible *)
    end
  | tProd na ty body  => if Nat.eqb sp 0 then 
  tProd na (debruijn_mess_aux' indu p sp n u  k lA ty) (debruijn_mess_aux' indu p sp n u  (k+1) lA body) 
  else  (debruijn_mess_aux' indu p (sp - 1) n u  (k+1) lA body) 
  | tLambda na ty body => tLambda na (debruijn_mess_aux' indu p sp n u  k lA ty) (debruijn_mess_aux' indu p sp n u  (k+1) lA body) 
  | tLetIn na def def_ty body => tLetIn na (debruijn_mess_aux' indu p sp n  u  k lA def  ) (debruijn_mess_aux' indu p sp n u  k lA def_ty) (debruijn_mess_aux' indu p sp n u  (k+1) lA body ) 
  | tApp f lg => tApp (debruijn_mess_aux' indu p sp n u  k lA f ) (map (debruijn_mess_aux' indu p sp n u k lA) lg)                      
  | _ => B  (* tVar, tEvar, tCast, tSort, tFix, tCofix,tCase  *) 
  end. *)

  Fixpoint debruijn_mess_aux (indu : inductive )  (n : nat) (u : Instance.t)  (k: nat)  (B: term):=
    match B with 
      | tRel j  =>
      match Nat.leb (j + 1) k  with
      | true  => tRel j
      | _ => tInd (switch_inductive indu (n +k - 1 - j) ) u  (* in practice, j >= k + n impossible *)
      end
    | tProd na ty body  => tProd na (debruijn_mess_aux indu    n u k ty) (debruijn_mess_aux indu   n u  (k+1)  body) 
    | tLambda na ty body => tLambda na (debruijn_mess_aux indu   n u  k  ty) (debruijn_mess_aux indu  n u  (k+1)  body) 
    | tLetIn na def def_ty body => tLetIn na (debruijn_mess_aux indu  n  u  k def  ) (debruijn_mess_aux indu   n u  k  def_ty) (debruijn_mess_aux indu   n u  (k+1)  body ) 
    | tApp f lg => tApp (debruijn_mess_aux indu   n u  k  f ) (map (debruijn_mess_aux indu   n u k ) lg)                      
    | _ => B  (* tVar, tEvar, tCast, tSort, tFix, tCofix,tCase...  *) 
    end.



(* Check debruijn_mess_aux. *)

(* 
Example dbmaO :=  Eval cbn in (debruijn_mess_aux nat_indu  1 []  0  (tRel 0)).
(* tRel 0 corresponds to O in the declaration of nat_oind *)
Print dbmaO. 

(* Print nat_indu.
Print nat_oind. *)
Example dbmaS :=  Eval cbn in (debruijn_mess_aux nat_indu  1 []  0  (tProd mkNAnon (tRel 0) (tRel 1))).
(* (tProd mkNAnon (tRel 0) (tRel 1)) : décla de S dans nat_oind *)
Print dbmaS. 
MetaCoq Unquote Definition typ_S := dbmaS.
Print typ_S.
(*
Print listS_env_reif.
Print listS_reif. *)
Definition listS_indu := {| inductive_mind := (MPfile ["interpretation_algebraic_types"], "listS"); inductive_ind := 0 |}.
(* Print consS_typ. *)

Example dbmaconsS := Eval compute in (debruijn_mess_aux listS_indu  1 [] 0  consS_typ).
Print dbmaconsS.
(* tProd "A" Set_reif. tProd mkNAnon (tRel 0). tProd (listS_reif (Rel 1) ). listS_reif (Rel 2)  *)
(* Print cons_typ_reif. *)
MetaCoq Unquote Definition dbmaconsS_u := dbmaconsS.
Print dbmaconsS_u.

Example dlist_consS := Eval cbn in dom_list_f dbmaconsS 3. 
(* Print dlist_consS. *)
(* [ Set_reif ; Rel 0 ; (listS_reif (Rel 1))] *)

Example dbmaevenS := Eval cbn in (debruijn_mess_aux even_indu 2 [] 0 
                                  (tProd (mkNamed "n")
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

*)                                              
(* Print dbmaevenS. *)
(* tProd nat_reif tProd (odd_reif (Rel 0)) . (even_reif (S_reif (Rel 1)))  *)
(* Print evenS. *)
(* evenS forall n : nat, odd n -> even (S n) *) 


(*
Definition list_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).
  


Example nil_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 [] 0 
(tProd (mkNamed "A") Set_reif  
     (tApp (tRel 1) [tRel 0])).
 
     
Print nil_dbm_try.
  


MetaCoq Unquote Definition nil_dbm_unquote := nil_dbm_try.
*)
(* Print nil_dbm_unquote. *)

(*
Example cons_dbm_try := Eval cbn in debruijn_mess_aux list_indu 1 [] 0 
(tProd (mkNamed "A")
                                  Set_reif
                                  (tProd mkNAnon  (tRel 0)
                                     (tProd mkNAnon 
                                        (tApp (tRel 2) [tRel 1])
                                        (tApp (tRel 3) [tRel 2]))))
.
MetaCoq Unquote Definition cons_dbm_unquote := cons_dbm_try.
*)
(* Print cons_dbm_unquote. *)



Definition get_ctors_and_types_i (indu : inductive) (p :nat) (n: nat) (i : nat) (u : Instance.t) (oind : one_inductive_body ) :=
              (* n: nb of oind *)
              (* i: indice of oind in the mutual inductive block *)
              (* lA : les paramètres *)
let indui := switch_inductive indu i in 
  let fix treat_ctor_oind_aux (indu : inductive) (n : nat) (j: nat)   (l : list ((ident * term) * nat  ))  :=
    match l with
      | [] => ([], [] , [], [])
      | ctor :: tll => let '((_ , typc) , nc ) := ctor in let nc' := nc + p in
      let '((tll1,tll2),tll3,tll4) := (treat_ctor_oind_aux indu  n (j+1)  tll) in let (B_ctor, lA_ctor) :=  dom_list_f (debruijn_mess_aux indui n u 0  typc) nc' in
      (B_ctor :: tll1,  (tConstruct indui j u)     :: tll2 , lA_ctor :: tll3 , nc :: tll4) 
    end in  treat_ctor_oind_aux indu n 0  oind.(ind_ctors).

(* Check get_ctors_and_types_i. *)

(* 
Goal forall (l : list_nat), (l = [] ) \/ (exists n l0, l = n :: l0).
Proof.  
  intros. destruct l.
  - (* congruence fails *) left. reflexivity.
  - right. (* congruence fails *) exists n. exists l. reflexivity. 
Abort.
*) 

(*
Definition hd0 := hd 0.
Definition hd' := hd imposs_mark.
Definition hd'' := hd [imposs_mark].


Definition gctt_ex1 := (let '(((a,b),c),d) := (get_ctors_and_types_i  nat_indu 0 0 1  []  nat_oind)  in  hd' (hd'' (tl c))). 
Eval compute in gctt_ex1.
Print gctt_ex1. 

MetaCoq Unquote Definition tclo_nat1' := gctt_ex1.
Print tclo_nat1'. 


Definition list_oind := ltac:(let s := fresh "s" in pose_oind_tac list 0 s ; exact s).


Definition list_mind :=  ltac:(let s := fresh "s" in pose_mind_tac list s ; simpl in s; exact s).


Example list_get_ctors_types1 := Eval compute in let '(((a,b),c),d) := get_ctors_and_types_i list_indu 1 1 1  []  list_oind in hd' (tl (hd'' (tl c))).
Print list_get_ctors_types1.
*)

(* MetaCoq Unquote Definition gct_list_unquote1 := list_get_ctors_types1.
Eval cbn in gct_list_unquote1.
Print gct_list_unquote1.   *)


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

(*
Definition Ntree_indu) :=  ltac:(let s := fresh "s" in pose_inductive_tac Ntree s ; exact s).


Definition Ntree_mind :=  ltac:(let s:= fresh "s" in pose_mind_tac Ntree s ; exact s ).

      
Definition Ntree_oind := 
   ltac:(let s:= fresh "s" in pose_oind_tac Ntree 0 s ; exact s ).
      

Definition Nforest_oind :=
  ltac:(let s:= fresh "s" in pose_oind_tac Ntree 1 s ; exact s ).
*)

Ltac treat_ctor_list_oind_tac_i_gen statement indu p n i u  oind  :=
  (* n: number of oind *)
  (* i: is the rank oind in the mutual inductive block *)
 let indui := constr:(switch_inductive indu i)
 in  let gct :=
  constr:(get_ctors_and_types_i indu p n i u  oind) 
 in  lazymatch eval hnf in gct with 
  | (?lBfA,?ln) => lazymatch eval hnf in lBfA with
    | (?lBf,?lA) =>  lazymatch eval cbv in lBf with
      | (?lB,?lf) =>  statement lB lf lA ln p 
      end
    end
  end.
(* todo : supprimer le /\ True inutile dans l'injectivité *)

Ltac treat_ctor_list_oind_tac_i indu p n i u oind := treat_ctor_list_oind_tac_i_gen inj_disj_tac indu p n i u oind.

Ltac interpretation_alg_types_oind_i := treat_ctor_list_oind_tac_i_gen inj_disj_tac.

(*
Goal 2+ 2 = 4.
  Proof.
    treat_ctor_list_oind_tac_i nat_indu 0 1 0 ([] : Instance.t)   nat_oind.
  reflexivity.
  Abort.
 *) 

(*
Goal False.
Proof.
  treat_ctor_list_oind_tac_i  list_indu 1 1 0 ([] : Instance.t) list_oind.
  (* problème: pas disj_cons pour list. Sans doute un pb de param ?*)
Abort.
*)


Ltac treat_ctor_mind_aux_tac_gen statement indu p n  u  mind  i  loind :=
 lazymatch eval cbv in loind with
| nil => idtac 
| ?oind :: ?tlloind => treat_ctor_list_oind_tac_i_gen statement indu p n i u  oind ; 
treat_ctor_mind_aux_tac_gen statement indu p n u mind constr:(S i) tlloind
end.



Ltac treat_ctor_mind_tac_gen statement indu p n u  mind  
:=  let loind := constr:(mind.(ind_bodies)) in 
treat_ctor_mind_aux_tac_gen statement indu p n u mind 0   loind. 
   
(* Ltac treat_ctor_mind_tac indu p n u  mind := treat_ctor_mind_tac_gen inj_total_disj_tac indu p n u  mind p. *)


Ltac interpretation_alg_types_mind_tac := treat_ctor_mind_tac_gen inj_disj_tac.

(*
Goal False.
Proof.
 assert (blut := nth 3 [] Level.lSet).   
 interpretation_alg_types_mind_tac Ntree_indu 0 2 ([] : Instance.t)   Ntree_mind.  
Abort. 
*)

(*
Goal False.
Proof.
  interpretation_alg_types_mind_tac list_indu 1 1 ([] : Instance.t)   list_mind.
Abort.
*)

 
Ltac  checkProp t :=  (* improve this function *)
  let blut := fresh in assert (False -> t) as blut ; [ let H := fresh in intro H; intros 
  ; lazymatch goal with
  | [  |- Prop] => fail
  | _ => idtac
  end ; elim H 
  |clear blut]. 

  (*  lazymatch t with 
  | Prop => fail 
  | forall x , ?H   => checkProp H 
(*  | forall x , @?H x  => checkProp (H x) *)
  | _ =>  idtac 17 
  end . *)


  Goal True.
  checkProp (forall n, even n -> nat).
  Fail checkProp (forall n, even n -> Prop).
Abort.

Ltac fo_prop_of_cons_tac_gen statement t := 
  let ty := type of t in 
  let _ := match goal with  _ => checkProp ty end in
    let geip := fresh "geip" in get_env_ind_param t geip ; 
    lazymatch eval hnf in geip with
    | (?Sigma,?induu) => lazymatch eval hnf in induu with
      | (?indu,?u) =>      let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
       lazymatch eval cbv in lkup  with
       | Some ?d =>    
         match d with
         |  InductiveDecl ?mind => let indu_p := constr:(mind.(ind_npars)) in 
            let n := constr:(List.length mind.(ind_bodies)) in treat_ctor_mind_tac_gen statement indu indu_p n u  mind ; clear geip
         end       
       end         
     end
     end 
    .




Ltac fo_prop_of_cons_tac := fo_prop_of_cons_tac_gen inj_total_disj_tac.

Ltac interp_alg_types := fo_prop_of_cons_tac_gen inj_disj_tac.

(* 
Inductive vec A : nat -> Type :=
  |nilVec  : vec A 0
  |consVec : forall (h:A) (n:nat), vec A n -> vec A (S n).
*)

Goal False.
interp_alg_types nat.
Fail interp_alg_types (list nat). 
interp_alg_types list.
(* interp_alg_types and. *)
Fail interp_alg_types True.
(* interp_alg_types and_Set. *)
(* interp_alg_types (list (vec bool)). *)
Abort.


(* 
(* Todo: use CompDec term  *)
Definition eqb_ind (indu indu': inductive ) := true.
Definition eqb_term (t t': term) := true. (* nécessaires ?*)
Definition eqb_list_term (t t': list term) := true.


Fixpoint In_ind (indu : inductive ) l :=
  match l with
  | [] => false 
  | x :: l => orb (eqb_ind indu x)  (In_ind indu l)
  end.



Fixpoint In_term (t : term ) l :=
    match l with
    | [] => false 
    | x :: l => orb (eqb_term t x) (In_term t l) 
  end.

Fixpoint In_list_term lA l :=
  match l with
  | [] => false 
  | x :: l => orb (eqb_list_term lA x) (In_list_term lA l) 
end.

Fixpoint get_rank_term  (t : term) (l : list term) k :=
  match l with
  | [] => k
  | x :: l => if eqb_term t x then 0 else get_rank_term t l (S k)
  end. 

Fixpoint get_rank_ind  (t : inductive ) l acc :=
  match l with
  | [] => acc
  | x :: l => if eqb_ind t x then 0 else get_rank_ind t l (S acc)
  end.


Fixpoint get_nth_def (A : Type) (k : nat) (a: A) (l : list A) :=
  match (k,l) with
  | (_,[]) => a
  | (0, x :: l) => x
  | (S k , x :: l) => get_nth_def A k a l
  end.

Fixpoint add_type (t : term)  k l  :=  
  (* not tail recursive *)
  match (k,l) with
  | (_ , []) => []
  | (0 , l0 :: l) => (t :: l0) :: l
  | (S k, l0 :: l) => l0 :: add_type t k l
  end.

Ltac smart_interp_alg_types_gen statement t lI lT lP  :=
  (* [lI]: generic datatypes already met *)
  (* [lT]: instances of datatypes *)
  (* [lP]: list of already produced statements *) 
  let ip_t := fresh "ip_t" in get_ind_param t ip_t  ; 
  lazymatch eval hnf in ip_t with
  | (?indu,?lA) => let b := constr:(List.In indu lA) in 
  lazymatch b with
  | true =>  let t_q := fresh "t_q" in pose (tApp (tInd indu []) lA) as t_q ;
    (* t_q is (almost) [quote t] *)
    let b' := constr:(List.In t_q lT ) in 
    lazymatch eval hnf in b' with
    | false => let k:= fresh "k" in let k := constr:(get_rank_ind indu lT)  in let lT' := fresh "lT'" in let lT' := constr:(add_type t_q k lT)  in smart_interp_alg_types_gen statement lI lT' lP ; clear lT' k t_q
    end     
  | false => 
  (* fin nouveau*)
  let geip := fresh "geip" in get_env_ind_param t geip ; 
  lazymatch eval hnf in geip with
  | (?Sigma,?t_reif) => lazymatch eval hnf in t_reif with
    | (?induu,?lA) => lazymatch eval hnf in induu with
    | (?indu,?u) =>      let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
     lazymatch eval cbv in lkup  with
     | Some ?d =>    
       match d with
       |  InductiveDecl ?mind => let indu_p := constr:(mind.(ind_npars)) in 
          let n := constr:(List.length mind.(ind_bodies)) in treat_ctor_mind_tac_gen statement indu indu_p n u  mind ; clear geip  
       end       
     end
     end         
   end
   end
   end 
   end
  .  
*)


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

Ltac contains_not_eq t := let u := eval cbv in t in 
match u with 
| ?x = ?y => fail 1
| _ => idtac
end.

Goal True.
Fail contains_not_eq (1=1). contains_not_eq (fun x: nat => x). exact I. Qed.

Ltac interp_alg_types_context_aux' p :=
match goal with 
| |- context C[?y] =>
is_not_in_tuple p y ;contains_not_eq y ;
interp_alg_types y ;
interp_alg_types_context_aux' (p, y)
| _ : context C[?y] |- _ =>
is_not_in_tuple p y ; contains_not_eq y ;
interp_alg_types y ; interp_alg_types_context_aux' (p, y)
| _ => idtac
end.


Definition prod_types := (Z, bool, True, False, and, or, iff).

Ltac interp_alg_types_goal := let p := eval unfold prod_types in prod_types in
interp_alg_types_goal_aux p.
Ltac interp_alg_types_context_goal := 
let p := eval unfold prod_types in prod_types in
(interp_alg_types_context_aux' p).


Goal forall (x : option bool) (l : list nat) (u : Z), x = x -> l =l -> u = u.
(* interp_alg_types_goal. *)
interp_alg_types_context_goal.
Abort.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
intros.
interp_alg_types_context_goal.

Abort.




Section Test. 
Variable A : Type. 
Lemma hd_error_tl_repr : forall l (a:A) r,
   hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. intros l.
interp_alg_types_context_goal.
Abort.



Goal 2+2 = 4.
Proof.
(* fo_prop_of_cons_tac (list nat). *)
clear. Fail interp_alg_types (list nat).
(* fo_prop_of_cons_tac nat. 
fo_prop_of_cons_tac Ntree.   *)
reflexivity.
Abort.
End Test.


