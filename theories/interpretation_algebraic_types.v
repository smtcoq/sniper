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


Require Import MetaCoq.Template.All.
Require Import List String.  
Require Import utilities. 
Require Import ZArith.
Require Import PArith.BinPos.


Open Scope string_scope.  

Import ListNotations MonadNotation. 

(* TODO : use metacoq_get_value in utilities to avoid continuations *)

Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).

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

Ltac pose_unquote_term_hnf t idn  := (run_template_program (tmUnquote t ) ltac:(fun x =>  (pose (my_projT2 x) as idn))); simpl in idn.

Ltac assert_unquote_term_hnf t  idn := (run_template_program (tmUnquote t ) ltac:(fun x =>  (assert (idn : my_projT2 x)))).


Ltac unquote_term_cbv' t idn  := unquote_term t idn ltac:(fun x => cbv in x).

MetaCoq Quote Definition eq_nat_reif := Eval cbn in (@eq nat).
(* Print eq_nat_reif. *)

MetaCoq Quote Definition eq_term_reif := Eval cbn in (@eq term).
(* Print eq_term_reif.*)

MetaCoq Quote Definition True_reif := Eval cbn in True.
MetaCoq Quote Definition False_reif := Eval cbn in False.
MetaCoq Quote Definition and_reif := Eval cbn in and.
MetaCoq Quote Definition or_reif := Eval cbn in or.

(** reified equalities **)

(* Definition mkNamed s := ({| binder_name := nNamed (s%string); binder_relevance := Relevant |} : aname).
Definition mkNAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

Definition mkNamedtry := mkNamed (("B"%string) : ident).*)


Definition consS_typ := tProd (mkNamed "A") (tSort (Universe.from_kernel_repr (Level.lSet, false) []))
                                  (tProd mkNAnon (tRel 0)
                                     (tProd mkNAnon (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))).

(** reified connectives **)


MetaCoq Quote Definition ex_reif := Eval cbn in @ex.
MetaCoq Quote Definition ex_intro_reif := Eval cbn in @ex_intro.


(*** Useful operators ***)


Definition mkImpl A B := tProd mkNAnon A (lift0 1 B). 

(* write examples to check specif *)

Definition mkNot (A :term) := mkImpl A False_reif.

Definition mkAnd (A B : term) := tApp and_reif [A ; B]. 

Definition mkOr (A B : term) := tApp or_reif [A ; B].


(** mkAnd_n [A1_reif ; ... ; An_reif ] = 
    the reification of A1 /\ (A2 /\ ... An) (associates to the right)   **)
(** tail-recursive (actually linear) *)
(* \TODO check that it is SMTLib friendly *)
Definition mkAnd_n0 (l : list term):=
  let l_rev := tr_rev l in 
  match l_rev with
  | [] => True_reif
  | t0 :: l0 => 
    let fix aux l acc :=
      match l with
      | [] => acc             
      | t :: tll => aux tll (mkAnd t acc)
      end 
    in aux  l0 t0 end.


Definition mkAnd_n (l : list term) :=
  match l with
  | [] => True_reif
  | t0 :: l0 => 
  let fix aux l acc := match l with
  | [] => acc
  | t :: l => aux l (tApp and_reif (acc :: [t])) 
  end
  in aux l0 t0
  end.
          


(* remove and replace with mkOr, which is tr *)
(* \todo check that it is SMTLib friendly *)
Fixpoint or_nary_reif (l : list term):=
  match l with
  | [] => False_reif           
  | t :: [] => t
  | t :: tll => tApp or_reif [t ; or_nary_reif tll ]                
  end.


  


    
(***  Marks impossible cases ***)

Inductive impossible_type : Type  := .

MetaCoq Quote Definition imposs_mark :=  impossible_type  .


(*** Extracting parameters ****)

Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.

Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tInd ?indu ?u =>  pose (indu,u) as idn  ; clear tq
     end.

Ltac pose_inductive_tac t idn := let s := fresh "s" in get_ind_param t s ; pose (fst s) as idn ;  simpl in idn ; clear s.

Ltac get_env_ind_param t idn := 
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
     | tInd ?indu ?u => pose (Sigma,(indu,u)) as idn ; clear rqt
     end
     end.






(* info_indu t idn takes a Coq term t which an *unquoted* inductive
     and outputs the pair (indu,mind) : inductive × mutual_inductive_body
     where indu in the 'inductive' inside t and mind its mutual_inductive_body as it is defined
     in the global environment Sigma  
*)
Ltac info_indu t idn :=   (* \TODO factorize code!*)
    let rqt := fresh "rqt" in rec_quote_term t rqt ; 
    lazymatch eval hnf in rqt with
     | (?Sigma,?ind) =>  lazymatch eval hnf in ind with 
     | tApp ?t_ind ?lA =>  
       lazymatch eval hnf in t_ind with
       | tInd ?indu ?u => 
     let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
       lazymatch eval cbv in lkup  with
       | Some ?d =>   
         match d with
         |  InductiveDecl ?mind =>  let x:= constr:(((indu,u),mind)) in pose x as idn ; compute in idn ; clear rqt
         end       
       end
       end  
       |   tInd ?indu ?u => 
       let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
         lazymatch eval cbv in lkup  with
         | Some ?d =>    
           match d with
           |  InductiveDecl ?mind =>  let x:= constr:(((indu,u),mind)) in pose x as idn; compute in idn ; clear rqt
           end       
         end     
     end
     end
    .


Ltac pose_mind_tac t idn :=   (* \TODO factorize code!*)
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
         |  InductiveDecl ?mind =>  pose mind as idn ; compute in idn ; clear rqt
         end       
       end
       end  
       |   tInd ?indu ?u => 
       let indu_kn := constr:(indu.(inductive_mind)) in   let lkup := constr:(lookup_env Sigma indu_kn) in 
         lazymatch eval cbv in lkup  with
         | Some ?d =>    
           match d with
           |  InductiveDecl ?mind =>  pose mind as idn ; compute in idn ; clear rqt
           end       
         end     
     end
     end
    .



(* get_params_from_mind mind = (p , lA) 
  where p is the number of parameters of mind and lA the list of the parameters types *in order*
  (note that mind.(ind_params)) stores the types in *reverse* order
*)
(* \TODO move in utilities *)
(* \TODO in utilites, unify and factorize all the tactics which retrieve parameters from reified inductives *)
Definition get_params_from_mind mind :=
  let p := mind.(ind_npars) in 
  let l0 := tr_revmap (fun d => d.(decl_type)) mind.(ind_params)
in (p, l0).
(* \TODO maybe use this tactic in fo_prop_of_cons_tac *)




(* \TODO here, it seems that only *applied* inductive types are considered *)
(* \TODO modify or remove *)
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

  

(*** Properties of inductives ***)

(*** Injectivity ***)


(** cutEvar (tApp t  [evar ; u_1 ; ... ; u_n ]) = t
      i.e. cutEvar removes all the arguments of t if they start with an evar  
**)
Definition cutEvar (t: term) :=
  (* perhaps a bit naive *)
  match t with 
  | tApp t' ((tEvar _ _ ) :: u) =>  t'
  | _ => t
  end.




 (* is_inj B f [A1 ; ... ; An ] is the reification of 
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



Ltac ctors_are_inj_tac lB lf lA ln p :=  
  match lA with
  |  nil  => idtac 
  | ?A1 :: ?tlA => 
    match lf with 
    | nil => idtac "Wrong branch 1 ctors_are_inj" 
    | ?f1 :: ?tlf =>
      match lB with
      | nil => idtac "Wrong branch 2 ctors_are_inj"    
      | ?B1 :: ?tlB =>
        match ln with
        | nil => idtac "Wrong branch 3 ctors_are_inj"
        | ?n1 :: ?tln  => let Hnew := fresh "H" in 
   ctor_is_inj B1 f1 A1 n1 p ;  
   ctors_are_inj_tac tlB tlf tlA tln p 
         end
      end      
    end
  end.
  
(*** Disjoints codomains ***)



Definition new_codom_disj (B f g: term)  (lAf lAg : list term) (p : nat)  :=
  let (n,n') := (List.length lAf , List.length lAg) in 
   let (d,d') := ( n - p, n' - p) in 
    let fix removeandlift p l :=
      match (p, l)  with
      | (0 , _) => tr_rev (lAf ++ tr_map (lift0 d) l) (* \TODO optimize *)
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

Ltac codom_disj_discr B f g lAf lAg p:=
  let H := fresh "H" in (pose_unquote_term_hnf (new_codom_disj B f g lAf lAg p) H); 
  assert  H ; [unfold H ; intros ;
  try discriminate | .. ]  ; subst H. 



Ltac pairw_aux B f lAf lf lA p :=
     lazymatch constr:((lf , lA)) with
        | ([] , []) => idtac 
        | (?f1 :: ?tllf , ?A1 :: ?tllA ) => codom_disj_discr B f f1 lAf A1 p  ;pairw_aux B f lAf tllf tllA p  
        | _ => idtac "wrong branch pairw_aux"  ; fail                               
      end.
 
    
Ltac pairw_disj_codom_tac B lf  lA p := lazymatch eval hnf in lf with
  | [] => idtac  
  | ?f1 :: ?tllf => lazymatch eval hnf in lA with 
    ?A1 :: ?tllA  => pairw_aux B f1 A1 tllf tllA p  ; pairw_disj_codom_tac B tllf tllA p 
  | _ =>   idtac "wrong branch pair_disj_codom_tac"  
  end
  end.


(*** Generation statements ***)


        

Fixpoint is_in_codom (B t f: term ) (lA : list term) :=
  (* if t : A and f : Pi lx lA . A, tells when t is in the codomain of f: returns exist vecx : lA, f vecx = t  *)
  match lA with
  | [] => tApp eq_reif [B ; t ; f]
  | A :: tllA => tApp ex_reif [A ;  tLambda (mkNamed "x") A   (is_in_codom B (lift0 1 t) (tApp (lift0 1 f) [tRel 0] )   tllA  )]
  end.
(* base case : f is 0-ary and  t is just f *)



Definition union_direct_total (lB : list term ) (lf : list term) (lD : list (list term) ) (p : nat) :=
  let lD' := tr_map(fun l => (@List.skipn term p l)) lD in 
  let lLen := tr_map  (fun l => (@List.length term l) ) lD' in 
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
  let aux2 B f lA k := aux1 (tr_rev lA) (mkEq (lift0 1 B) (tRel k) (tApp f (aux0 p (k+1) (aux0 k 0 [])))) in 
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


Definition codom_union_total (B : term) (lf : list term) (lA : list (list term)) :=
(* lf is a list of function [f1;...;fn] whose return type is B, lA = [lA1 ; ...; lAn] is the list of the list of the types of the fi, e.g. lA1 is the list of argument types of lA *)
  let fix arg_org (B  t : term) (lf : list term) (lA: list (list term)) :=
      match (lf , lA)  with
      | (f1 :: tllf, lA1 :: tllA)  => (is_in_codom B t f1 lA1) :: (arg_org B t tllf tllA )
      | ([], []) => []
      | _ => [False_reif]               
      end
  in tProd (mkNamed "x") B  (or_nary_reif (arg_org B (tRel 0)  lf lA)).


Ltac revert_intro_ex_tac_aux e :=
    match goal with
        | H : _ |- _ =>  first [ revert H ;  let e':= (intro H; e)  in revert_intro_ex_tac_aux  e'  ; exists H   | e]
end.

Ltac revert_intro_ex_tac  := revert_intro_ex_tac_aux ltac:(idtac).

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
  

(* \TODO see if useful / move in utilities *)
Ltac dotac n t :=
  match constr:(n) with
  | 0 => idtac
  | S ?k => t ; dotac k t
  end.



Ltac codom_union_total_tac lB lf lD p :=
  let toto := fresh "H" in pose_unquote_term_hnf (union_direct_total lB lf lD p) toto ; assert toto; unfold toto ;[ dotac p intro ; (let x := fresh "x" in intro x ; destruct x ; ctor_ex_case ) | ..] ; subst toto. 

(*** Global properties of constructors ***)


Ltac inj_total_disj_tac B lf lA   :=
  ctors_are_inj_tac B lf lA  ; pairw_disj_codom_tac B lf lA ; codom_union_total_tac B lf lA.

Ltac inj_disj_tac lB lf lA ln p  :=  
  lazymatch eval hnf in lB with
   | ?B :: ?tlB => ctors_are_inj_tac lB lf lA ln p ; pairw_disj_codom_tac B lf lA  p
    end.


    (* list_ctor_oind is probably redundant. Remove it ? \TODO *)
Definition list_ctor_oind ( oind : one_inductive_body ) : list term :=
  let fix list_lctor ( l : list ((ident × term) × nat )) acc :=
  match l with
  | [] => acc
  | ((idc , ty) , n ) :: tlctor => list_lctor  tlctor  (ty :: acc) 
  end in  tr_rev (list_lctor oind.(ind_ctors) []).
  

(* \TODO integrate get_blut in the functions below *)


(* metavariable i metavariable p *)
Definition get_ctors_and_types_i (indu : inductive) (p :nat) (no: nat) (io : nat) (u : Instance.t) (oind : one_inductive_body ) :=
              (* p  : number of parameters of indu *)
              (* no : number of oind's *)
              (* io  : index of oind in the mutual inductive block *)
              (* lA : the (reified) types of the parameters *)
let indui := switch_inductive indu io in 
  let fix treat_ctor_oind_aux (indu : inductive) (n : nat) (j: nat)   (l : list ((ident * term) * nat  ))  :=
    match l with
      | [] => ([], [] , [], [])
      | ctor :: tll => let '((_ , typc) , nc ) := ctor in let nc' := nc + p in
      let '((tll1,tll2),tll3,tll4) := (treat_ctor_oind_aux indu  no (j+1)  tll) in let (B_ctor, lA_ctor) :=  dom_list_f (debruijn0 indui no u   typc) nc' in
      (B_ctor :: tll1,  (tConstruct indui j u)     :: tll2 , lA_ctor :: tll3 , nc :: tll4) 
    end in  treat_ctor_oind_aux indu no 0  oind.(ind_ctors).

Ltac treat_ctor_list_oind_tac_i_gen statement indu p no io u  oind  :=
  (* p : number of parameters *)
  (* n : number of oind *)
  (* i : is the rank oind in the mutual inductive block *)
 let indui := constr:(switch_inductive indu io)
 in  let gct :=
  constr:(get_ctors_and_types_i indu p no io u  oind) 
 in  lazymatch eval hnf in gct with 
  | (?lBfA,?ln) => lazymatch eval hnf in lBfA with
    | (?lBf,?lA) =>  lazymatch eval cbv in lBf with
      | (?lB,?lf) =>  statement lB lf lA ln p 
      end
    end
  end.
(* todo : supprimer le /\ True inutile dans l'injectivité *)

Ltac treat_ctor_list_oind_tac_i indu p no io u oind := treat_ctor_list_oind_tac_i_gen inj_disj_tac indu p no io u oind.

Ltac interpretation_alg_types_oind_i := treat_ctor_list_oind_tac_i_gen inj_disj_tac.

Ltac treat_ctor_mind_aux_tac_gen statement indu p no  u  mind  io  loind :=
 lazymatch eval cbv in loind with
| nil => idtac 
| ?oind :: ?tlloind => treat_ctor_list_oind_tac_i_gen statement indu p no io u  oind ; 
treat_ctor_mind_aux_tac_gen statement indu p no u mind constr:(S io) tlloind
end.



Ltac treat_ctor_mind_tac_gen statement indu p no u  mind  
:=  let loind := constr:(mind.(ind_bodies)) in 
treat_ctor_mind_aux_tac_gen statement indu p no u mind 0   loind. 
   
(* Ltac treat_ctor_mind_tac indu p n u  mind := treat_ctor_mind_tac_gen inj_total_disj_tac indu p n u  mind p. *)


Ltac interpretation_alg_types_mind_tac := treat_ctor_mind_tac_gen inj_disj_tac.

 
Ltac  checkProp t :=  (* improve this function *)
  let blut := fresh in assert (False -> t) as blut ; [ let H := fresh in intro H; intros 
  ; lazymatch goal with
  | [  |- Prop] => fail
  | _ => idtac
  end ; elim H 
  |clear blut]. 

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
            let no := constr:(List.length mind.(ind_bodies)) in treat_ctor_mind_tac_gen statement indu indu_p no u  mind ; clear geip
         end       
       end         
     end
     end 
    .





Ltac fo_prop_of_cons_tac := fo_prop_of_cons_tac_gen inj_total_disj_tac.

Ltac interp_alg_types := fo_prop_of_cons_tac_gen inj_disj_tac.

Goal False.
interp_alg_types nat.
Fail interp_alg_types (list nat). 
interp_alg_types list.
(* interp_alg_types and. *)
Fail interp_alg_types True.
(* interp_alg_types and_Set. *)
(* interp_alg_types (list (vec bool)). *)
Abort.


Ltac contains_not_eq t := let u := eval cbv in t in 
match u with 
| ?x = ?y => fail 1
| _ => idtac
end.

Goal True.
Fail contains_not_eq (1=1). contains_not_eq (fun x: nat => x). exact I. Qed.


(* In the goal, we look for the terms whose type is an algebraic type 
and the terms who are an algebraic type *)
Ltac interp_alg_types_aux_goal_term p y :=
is_not_in_tuple p y ;
try (interp_alg_types y).

Ltac interp_alg_types_aux_goal_type p y :=
is_not_in_tuple p y ;
let y' := get_head y in is_not_in_tuple p y';
try (interp_alg_types y').


(* In the context, we look for the not applied type of the variables, 
or the implicit parameter of an equality *)
Ltac interp_alg_types_aux_context p y :=
is_not_in_tuple p y ;
let y' := get_head y in
let T := type of y in 
is_not_in_tuple p y' ; 
first [
constr_neq T Prop ;
interp_alg_types y' | match y with 
|?x = ?y => let T := type of x in let T' := get_head T in
is_not_in_tuple p T' ; is_not_in_tuple p T ;
try (interp_alg_types T')
end].

Ltac interp_alg_types_context_aux p :=
match goal with 
| |- context C[?y] => 
let T :=
type of y in interp_alg_types_aux_goal_term p y ; interp_alg_types_aux_goal_type (p, y) T ;
interp_alg_types_context_aux (p, y, T)
| _ : ?y |- _ => interp_alg_types_aux_context p y ; interp_alg_types_context_aux (p, y)
| _ => clear_dups
end.


Ltac interp_alg_types_context_goal p := 
interp_alg_types_context_aux p.

Goal forall (x : option bool) (l : list nat) (u : Z), x = x -> l =l -> u = u.
intros ; interp_alg_types_context_goal (bool, Z). 
Abort.

Goal forall (l : list Z) (x : Z),  hd_error l = Some x -> (l <> []).
intros.
interp_alg_types_context_goal (bool, Z).

Abort.

Section Test. 
Variable A : Type. 
Lemma hd_error_tl_repr : forall l (a:A) r,
   hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. intros l.
interp_alg_types_context_goal bool.
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

