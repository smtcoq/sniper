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


Require Import utilities. 
Require Import instantiate_type.
Require Export clearbodies.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import interpretation_algebraic_types. 
Require Import SMTCoq.SMTCoq.

(*********************)
(** General specification **)

(* The goal of this file is two-fold:
(1) automatically declare the projections of an inductive datatype I. 
For instance, for the type list, whose constructors are [] (0 argument) and :: (2 arguments ), 
we declare in the local context two functions proj_{1,0} : forall (A : Type), A -> list A -> list A and 
proj_{1,1} : forall (A : Type) list A -> list A -> list A such that:
* proj_{1,0} def [] = def and proj_{1,0} d {a :: l} = a 
* proj_{1,1} def [] = def and proj_{1,1} d {a :: l} = l 
The metavariable d stands for a dummy default value, 
of respective types A (for proj_{1,0}) and list A (for proj_{1,1})

(2) automatically prove in the local context the generation statement, specifying that every inhabitant t of I 
is equal to a constructor applying to the projections of t.
For instance, in the case of list, the main tactic produces and proves the statement:
forall (A : Type) (d_{1,0} : A)  (d_{1,1} l: list A), (l =  []) \/ (l = ((proj_{1,0} d_{1,0} l)) :: ((proj_{1,1} d_{1,1} l))

Some implicit arguments have been omitted: technically,  proj_{1,0} : forall (A : Type), A -> list A -> list A and proj_{1,1} : forall (A : Type) list A -> list A -> list A and the generation statement is: 
forall (A : Type) (d_{1,0} : A)  (d_{1,1} l: list A), (l = @nil A) \/ (l = (proj_{1,0} A d_{1,0} l) :: (proj_{1,1} A d_{1,1} l) *)



(* 
Let us get now into the technical details.
Given an inductive datatype I, we use the following conventions:
* p : number of parameters of I
* P_0, ..., P_{p-1}: the types of the parameters of I
  lP := [ P_0 ; ... ; P_{p-1} ]
* C_1,...., C_k: the constructors of I
  lctors = [ C_0 ; ... ; C_k ]
* n_i is the number of arguments of C_i (withstanding parameters): thus, C_i has p + n_i arguments in total
  ln := [ n_0 ; ... ; n_{k-1} ]
* A_{i,j} is the type of the rank j argument of C_i (withstanding parameters): thus, C_i has the type (forall X_0 : .A_0) (X_{p-1} : A_{p-1}) (x_{i,0} : A_{i,0}) ... (x_{i,n_i-1} : A_{i, n_i-1}), B_i (* \TODO spécifier B_i: on en a besoin ?*)
  llA := [ [A_{0,0} ; ... ; A_{0,n_0-1} ] ;
            ... ;
           [ A_{k-1,0} ; ... ; A_{k-1,n_{k-1}-1}] ]

(** lift and unlift **)

A^{+i} (resp. A^{-i}) denotes A where all the free de Bruijn indices have been lifted with + i (resp. unlifted with -i)

* We set Aunlift_{i,j}/Au_{i,j} := (A_{i,j}^{-j})
  llAunlift/llAu := [ [Au_{0,0} ; Au_{0,1} ; ... ] ;
                       ... ;
                      [Au_{k-1,0} ; Au_{k-1,1} ; ... ] ]

Example: for I = nelist, the type of non-empty list, whose reification is denoted nelist_reif 
* p = 1 and lP_0 = [ Type_Reif ]
* k = 2, C_0 = sing and C_1 = necons
* n_0 = 1 and n_1 = 2, ln = [1 ; 2]
* llA =  [ [ tRel 0 ] ; [ tRel 0 ; tApp nelist_reif [tRel 1] ] ] 
* llAu = [ [ tRel 0 ] ; [ tRel 0 ; tApp nelist_reif [tRel 0] ] ]

From the reified point of view, an inductive type contains:
* a term of type 'inductive' (metavariable indu)
* a mutual_inductive_body (metavariable mind)
* mind contains a list of one_inductive_body's (metavariable oind)
* each one_inductive_body contains relevant information about, e.g., its constructors and their types

We must define projections proj_{i,j} for i = 0, ... , k-1 and j = 0, ..., n_i-1
proj_{i,j} = fun (X_0 : A_0) ...  (X_{p-1} : A_{p-1)} (def_{i,j} : Aunlift_{i,j}) (x : (I X_0 ... X_{p-1})), 
match x with
| C_i x_{i,0} ... x_{i,n_i-1} => x_{i,j}  
| C_q x_{q,0} ... x_{q,n_q-1} => def_{i,j} (* q <> i, the default value is returned *)
end.


To obtain the reification of reification of proj_{i,j}, we e set I' = tApp I [tRel p ; ... ; tRel 1]
Then proj_{i,j}_reif is:
tLam P_0 ... P_{p-1} tLam Aunlift_{i,j} tLam I' 
tCase (I_indu , p , relevant ) ( tProd ((I')^{+1}) -> (Aunlift_{i,j}^{+3}) ) (tRel 0) 
        [ (n_0 ; tLam A_{0,0}^{+2} ... A_{0,n_0-1}^{+2}) (tRel (S n_0)) ) ; ... ;
        (n_q ; tLam A_{0,q}^{+2} ... A_{q,n_q-1}^{+2}) (tRel (S n_q)) ) ; ... ;  (* for q <> i *)
        (n_i ; tLam A_{0,0}^{+2} ... A_{i,n_i-1}^{+2} tRel (n_i-1-j ) ) ; ...]  
        

To obtain the reificaiton of the generation statement, we set
N_i = n_0 + ... + n_{i-1} 
N'_i := n_{i+1} + ... + n_{k-1} 
and N = n_0 + ... + n_{k-1} = N_k = N'_{-1} 
Then, the reification of the statement is:
tProd A_0 ... A_ {p-1} 
tProd Au_{0,0}^{+0} Au_{0,1}^{+1} ... Au_{0,j}^{+j} ... Au_{0,n_0-1}^{+n_0-1}
      Au_{1,0}^{+n_0} Au_{1,1}^{n_0+1} ...
      .... Au_{i,j}^{N_i+j}... Au_{k-1,n_k-1}^{N-1}
tProd (x : (I')^{+N})
  or_reif 
     eq_reif _ (tRel 0)  pstat_0 ; 
     eq_reif _ (tRel 0) pstat_1 ; ... ;
     eq_reif _ (tRel 0) pstat_{k-1}
where pstat_i := C_i [ _p ; 
        proj_{i,0} [ _p ; tRel (N'_{i-1}) ; tRel 0 ]
        .... ;
        proj_{i,j} [ _ p ; tRel (N'_{i-1}-j) ; tRel 0] ; ... ]
where _p is a macro for p evars 
 *)


(* get_term_applied t p = tApp t [tRel (p + n -1) ; .... ; tRel p] *)
(* tail-recursive *)
Definition get_term_applied (t : term) (p n: nat) := 
  tApp t (Rel_list p n).




(***************)

Ltac find_inhabitant_context t := 
first[ constructor ; assumption | 
apply Inh | epose (inhab := ?[t_evar] : t)]. 

Ltac find_inh t :=
match goal with
| H : t |- _ => H
| _ => let H := fresh in let _ := match goal with _ => assert (H : t) by find_inhabitant_context t end in H
end.


(* removes k to each de Brujin index: useful when variables are removed *)
Fixpoint unlift (k : nat) (t : term) : term :=
 match k with
| 0 => t
| S k' => unlift k' (subst10 <%default%> t)
end.


(* branch_proj_or_default n_i i j q = tRel kp
    where kp is defined with:
    kp = n_q - 1 - j if q = j
    kp = n_q + 1 if q <> j 
    * If j <> q then, tRel kp denotes def, the default variable
    Indeed, tRel dq is tRel 1 lifted nq times
    * If j = k, then tRel dq denotes the variable that is bound by the hole of rank i
  Thus, branch_default_var n_q i j q  denotes the branch of rank q of the 
  pattern-matching specifying proj_{i,j}, where nq is the number of arguments of 
  the constructor C_q
*)
Definition result_branch_proj_or_default (nq : nat)  (i : nat) (j : nat) (q : nat) := 
      if Nat.eqb i q then tRel (nq - (S j))  
      else tRel (S nq).

   
(* Constructs the pattern matching in the proj
for instance, given the right arguments to construct the predecessor function we get the reified
< match x with
| 0 => default
| S y => y > *)


(* mkbranch_proj [n_0 ; ... ; n_{k-1} ] i j 
     is the list (branch term) expected by the 'tCase' constructor to define the pattern-matching 
     specifying the proj_{i,j} 
     Namely, it is the list:
     [ {| bcontext := "context with nO fresh names"; bbody := result_branch_proj_or_default n_0 i j 0 |} ; ... ; 
      {| bcontext := "context with nk fresh names"; bbody := result_branch_proj_or_default n_{k-1} i j (k-1)|} ]
*)
Definition mkCase_list_param (ln : list nat)  (i : nat) (j : nat) : list (branch term):=
  let fix aux ln q acc :=
  match ln with
  | [] => acc
  | nq :: ln => aux ln (S q)  ({| bcontext := list_aname nq ; bbody := result_branch_proj_or_default nq i j q |} :: acc) 
  end
  in List.rev (aux ln 0 []). 

(* We use Coq type inference to avoid bothering with 
typing the match and the parameters *)
Definition get_predicate_term (p : nat) (I : term) (inst: Instance.t) (return_type : term) :=
{| puinst := inst; pparams := list_of_holes p; pcontext := [mknAnon] ; preturn := return_type |}.


(* proj_ij p lP_rev I indu i j llAu ln Au_{i,j} 
    defines the reification of proj_ij, where the parameters follow the
    metavariables conventions specified in the head of this file
    (lP_rev is lP reverted)
*)
Definition proj_ij (p : nat) (lP_rev : list term) (I : term) (indu : inductive)  (i : nat) (j : nat)
(ln : list nat) (Auij : term):= 
let info := get_info_inductive I in 
let instances := match info with
      | None => []
      | Some p => p.2 
    end in
mkLam_rec lP_rev 
 (mkLam Auij (mkLam (get_term_applied I p 1)
(tCase {| ci_ind := indu; ci_npar := p ; ci_relevance := Relevant|}  
       (get_predicate_term p I instances (lift 3 0 Auij)) (tRel 0) (mkCase_list_param ln i j)))).


(* This function computes the projections of an inductive type the projections in the local environment
*)
Definition collect_projs (p : nat) (lP_rev : list term) (I : term) (indu: inductive)
(llAunlift : list (list term)) (ln : list nat) (k : nat)
:= let fix aux1 (i : nat) (nk :nat) lAk' acc :=
  match (nk,lAk') with 
  | (0,[]) => acc 
  | (S j, Auij :: lAk') => aux1 i nk lAk' ((proj_ij p lP_rev I indu i j  ln (Auij)):: acc)
  | _ => [] (* this case should not happen *)
  end 
in 
let fix aux2 llAu' ln' i'  acc :=
match (i',llAu',ln') with
| (0,[],[]) => acc
| (S i,lAi :: llAu' , ni :: ln' ) => aux2 llAu' ln' i ((aux1 i ni (List.rev lAi) []) :: acc)
| _ => []
end in
aux2 (List.rev llAunlift) (List.rev ln) k []. 


Ltac declare_projs_ctor_i na p lP_rev I indu llAu ln i lAi ni :=
  let _ := match goal with _ =>  idtac end in let lAi' := constr:(List.rev lAi) in 
  let rec aux1 i j lAi' acc :=
  lazymatch j with
  | 0 => constr:(acc)
  | S ?j0 => lazymatch eval hnf in lAi' with
   | ?Auij :: ?tlAi' =>  let pij := constr:(proj_ij p lP_rev I indu i j0 ln Auij) in let name :=  fresh "proj_" na  in 
                          let _ := match goal with _ => pose_unquote_term_hnf pij name
    end in 
    let pij_tVar := metacoq_get_value (tmQuote name) in 
    let acc0 := constr:(pij_tVar :: acc) in 
    let z := aux1 i j0 tlAi' acc0 in constr:(z)
   end 
   | _ => idtac "erroc declare_projs_ctor_i"
  end
  in   let res_dpi := aux1 i ni lAi' (@nil term) in constr:(res_dpi)
.

(* declare_projs_for_one_ctor .... k lAk k 
   (1) declare the projections of Ck, the ctor of rank k of I with the base name na (hopefully, the name of the inductive)
   (2) outputs the list of reified projections as tVar's [ tVar "na_k_0" ; .... ; tVar "na_k_nk" ] (i.e. projections are in order)
   where 
   * lA is the list of types of the arguments of C_k
   * nk is the number of parameters of C_k
   * the other metavariables follow the usual conventions 
*)
(* declare_projs na ... nc
  (1) declare the projs of an inductive using base name na (the name of inductive)
  (2) outputs the list of lists of the reified projectors as tVar's 
      [[ tVar "na_0_0" ; .... ; tVar "na_k_n0" ] ; ....
      ;  [ tVar "na_nc_0" ; .... ; tVar "na_nc_{k_nc}" ] ]
      (i.e. projections are in order)
  where nc is the number of constructors of the inductive
  *)

Ltac declare_projs na p lP_rev I indu llAu ln nc :=
  let llAu_rev := constr:(List.rev llAu) in let ln_rev := 
constr:(List.rev ln)    
in 
 let rec aux llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in lazymatch eval hnf in y with
| (?y0 , ?ln0') => 
  match eval cbv in ln0' with
  | (@nil nat) =>   constr:(acc) 
  | ?nk :: ?tln0 =>
    match eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k => match eval hnf in lAu' with
        | ?lAk :: ?tlAu'=> 
        let dpk  := declare_projs_ctor_i na p lP_rev I indu llAu ln k  lAk nk in
        let acc0 := constr:(dpk :: acc ) in 
        let res2 := aux tlAu' tln0 k acc0 in  constr:(res2)
  end 
  end   
  end
  end 
 |_ => idtac "error declare_projs "
end
in 
let res_dp := aux llAu_rev ln_rev nc (@nil (list term))  in constr:(res_dp)
. 



(************************************************************************************)
(* The tactic defining projections in the local context have been specified above   *)
(* Below, we define the tactic stating and proving the generation statement         *)
(************************************************************************************)



(*
proj_return_types [[A_{0,0} ; ... ; A_{0,n_0-1}] ; ... ; [A_{k,0} ; .... ; A_{k-1,n_{k-1}}] ]
    = [ [A_{0,0}] ; A_ {0,1} ^{-1} ; ... ; A_{0,n_0-1}^{-n_0+1} ] ; ... ;
         [A_{k-1,0}] ; A_ {k-1,1} ^{-1} ; ... ; A_{k-1,n_{k-1}}^{-n_k+1}] ]
      helps compute llAu, this list of list of the return types of the projections
*)
Definition proj_return_types (llA: list (list term)) :=
  let fix aux acc i lA :=
    match lA with
    | [] => acc 
    | A :: tlA => aux ((unlift i A) :: acc ) (S i) tlA
  end  in  (List.map (fun lA => List.rev(aux [] 0  lA)) llA).



(* warning: handles parameters but not dependent arguments *)


(* bind_def_val_in_gen [[A_{0,0} ; ... ; A_{0,n_0-1}] ; ... ; [A_{k-1,0} ; .... ; A_{k-1,n_k-1}] ]
                                  [ n_0 ; ... ; n_{k-1} ]
    = [ A_{k,n_k}^N ; ... ; A_{0,1}^{+1} ; A_{0,0}^0 ]
      where N = n_0 + ... + n_{k-1}
      Thus, bind_def_val_in_gen performs a flattening, a revert and a incremental lift of all the elements of the initial list of lists
    *)
Definition bind_def_val_in_gen (llAunlift : list (list term)) (ln : list nat) :=
  let fix aux1  acc i (lA : list term) : list term  := 
  match lA with
  | [] => acc  
  | A0 :: lA => aux1 ((lift0 i A0) :: acc) (S i) lA
  end 
  in let fix aux2 acc  a1 a2 llA ln :=
  match (llA,ln) with
  | ([],[]) => acc 
  | (lA :: llA, na :: ln)  => let a1'  :=  na + a1 in  aux2 (aux1 acc  a1 lA )  a1' na  llA ln
  | _ => [] (* this cases does not happen: ln and llAunflit have the same length *)
  end 
  in  aux2 [] 0 0  llAunlift ln.
  
  (* holes_p p = [hole ; ... ; hole ; tRel db ; tRel 0] with p holes *)
  Definition holes_p' (p : nat) (db : nat) :=
    let fix aux p acc := 
    match p with
    | 0 => acc 
    | S p => aux p (hole :: acc)
  end in aux p [tRel db; tRel 0].



(** get_eq_x_ctor_projs p ctor [proj_0, ..., proj_{n-1}] db  
   is the reification of the equality "tRel 0" = ctor (proj0 [ _p ; tRel db  ; tRel 0] ; 
 proj_{n-1} [ _p : tRel (db -1) ; tRel 0] ; ... ; [ _p ; tRel (db-n+1) ; tRel 0] ]
   where p is the number of parameters of the inductive
   proj_0,...., proj_{n-1} are supposed to be the reified projections of the reified constructor ctor, n is the number of argument of this constructor (withstanding parameters) and _p is a sequence of p holes
   That is, intuitively, the ouput represents an equality of the form x = ctor (proj_0 x) ... (proj_{n-1} x), where x is tRel 0 
   **)
(** tail-recursive **)   
  Definition get_eq_x_ctor_projs (p: nat) (ctor : term) (projs : list term)  (db: nat) :=  
(* \tTODO see it one needs to give the parameters: probably not *)  
let fix aux lprojs i  acc :=
   match (lprojs,i) with
   | ([],_) => acc 
   | (pki :: lprojs, S i) => aux lprojs i ((tApp pki (holes_p' p i))::acc)
   | _ => [] (* this case does not happen *)
  end in 
  mkEq hole (tRel 0) (tApp ctor (rev_append (list_of_holes p) (List.rev (aux projs (S db) [])))).


(* get_generation_disjunction p ctors list_proj ldb 
   outputs the reification of forall x : I, 
   x = C0 (projs0 x) \/ .... \/ x = Ck (projsk x)
   where lctors is the list of the (reified) constructors of an inductive, list_proj is the list of lists of their projections  (which are computed by the tactic declare_projs)
  x = Ck (projsk x) is a shortening of x = Ck (proj_{k,0} d_{k,0} x) .... (proj_{k,nk-1} d_{k,nk-1} x) and d_{k,i} the default value for d_{k,i} (x = Ck (projsk x) is computed with get_eq_x_ctor_projs)
   ldb is the list of De Bruijn indices of ????
   N is the total number of the arguments of all constructors (withstanding type parameters )
   Note that mkProd tApp I (Rel_list N p) _
   is forall x : I A1 ... Ap, _
   *)


 Definition get_generation_disjunction  (p : nat) (I: term) (N : nat) (lc : list term) (list_proj : list (list term)) (ln : list nat) :=
  let fix aux lc list_proj lN acc := 
  match (lc,list_proj,lN) with
  | ([],[],[]) => acc
  | (ctor :: tlc , projs :: tl_proj, db :: tlN ) => aux tlc tl_proj tlN  ((get_eq_x_ctor_projs p ctor projs db) :: acc)
  | _ => [] (* this cases does not happen *)
 end in let lN := rev_acc_add (List.rev ln)    
 in tProd (mkNamed "x") (tApp I (Rel_list p N)) (mkOr_n (List.rev (aux lc list_proj lN []))) .



(** args_of_projs_in_disj [ n1 ; .... ; nk ] = [[tRel N ; tRel N-1 ; ....; tRel (N-n1+1) ] ; ... ; [tRel nk ; ... ; tRel 1]  ] 
    where N = n1 + ... + n1
    i.e. the sublists have respective lengths ni and the de Bruijn index decreases at each step
    args_of_projs_in_disj [1 ; 3 ; 2 ] = [ [tRel 6 ] ; [tRel 5 ; tRel 4 ; tRel 3] ; [tRel 2 ; Rel 1]]
    This function helps specify the Db index of the default variable of each projection in the big disjunction
    **)
(* \Q : do we need this function? *)
Definition args_of_projs_in_disj (ln : list nat) : list (list term) :=
  let ln_rev := List.rev ln in
  let fix aux l0 acc res :=
  match l0 with
  | [] => res
  | ni :: l0 =>  aux l0 (ni + acc) ((Rel_list ni acc) :: res)
  end in aux ln_rev 1 [].

Ltac prove_by_destruct_varn n  := 
match n with 
| 0 =>
let x := fresh in 
intro x ; destruct x; repeat first [first [reflexivity | right ; reflexivity] | left]
| S ?m => let y := fresh in intro y ; prove_by_destruct_varn m 
end.

Ltac clearbody_list_of_list l :=
match l with
| @nil (list term) => idtac
| cons ?x ?xs => clearbody_list_tVar x ; clearbody_list_of_list xs
end.

Ltac gen_statement t := 
  let Helim := fresh "gen_" t in let _ := match goal with _ => 
  let indmind := fresh "indmind" in info_indu t indmind ; 
  lazymatch eval compute in indmind with
  | (?induu,?mind) => 
    lazymatch eval hnf in induu with
    | (?indu, ?u) =>
    let pparams := eval compute in (get_params_from_mind mind) in
    lazymatch eval hnf in pparams with 
    | (?p,?lP) =>
    lazymatch eval hnf in pparams with
    | (?p, ?lP) => let oind := eval compute in (hd default_body mind.(ind_bodies)) in
     let gct := eval compute in  (get_ctors_and_types_i indu p 1 0 u  oind) 
   in  lazymatch eval hnf in gct with 
    | (?lBfA,?ln) => lazymatch eval hnf in lBfA with
      | (?lBf,?llA) =>  lazymatch eval cbv in lBf with
        | (?lB,?lc) => let llAtrunc := eval compute in (List.map (skipn p) llA) in  let nc := eval compute in (List.length ln) in 
        let lP_rev := eval compute in (List.rev lP) in let llAu := eval compute in (proj_return_types llAtrunc) in 
        let t_reif := constr:(tInd indu u) in  let N := constr:(fold_left Nat.add ln 0) in
        let res3 := 
         declare_projs t p lP_rev t_reif indu llAu ln nc in 
        let llprojs := fresh "llprojs" in 
         pose (llprojs  := res3) ; 
        let ltypes_forall := constr:(bind_def_val_in_gen llAu ln) in 
        let ggd := constr:(mkProd_rec_n "A" lP_rev (mkProd_rec_n "d" ltypes_forall (get_generation_disjunction  p t_reif N  lc  llprojs  ln))) in 
          let gent := fresh "gen_stat" t in pose_unquote_term_hnf ggd gent  ; let N' := eval compute in (p + N) in assert (Helim : gent) by prove_by_destruct_varn N' ; 
        unfold gent in Helim ; let llprojs2 := eval unfold llprojs in llprojs in 
       clearbody_list_of_list llprojs2; (* unfold gent in Helim ; *) clear gent indmind llprojs
        end 
      end
    end
    end
  end end end end in Helim.       
   

Ltac pose_gen_statement t :=
let x := gen_statement t in idtac. (* pose x as gent *)

Ltac get_projs_st_return t := gen_statement t. 

Ltac get_projs_st t := pose_gen_statement t.

Ltac get_projs_st_return_quote t := pose_gen_statement t.

Section tests_proj.

(* non-empty lists *)
Inductive nelist {A : Type} : Type :=
	sing :  A -> nelist    | necons : A -> nelist -> nelist .

(* bicolor lists *)
Inductive biclist {A B : Type} : Type :=
  | bicnil : biclist
  | cons1 : A -> biclist -> biclist
  | cons2 : B -> biclist -> biclist. 


Inductive Ind_test (A B : Type) :=
| ind0 : Ind_test A B
| ind1 : A -> B -> Ind_test A B -> nat -> Ind_test A B.

Inductive Ind_test2 (A B C : Type) := 
| bar1 : C -> Ind_test2 A B C
| bar2 : nat -> nat -> A -> Ind_test2 A B C.

Goal False. 
get_projs_st @list. generalize proj_list. clear.
get_projs_st nat. clear.
get_projs_st option. clear.
get_projs_st @nelist. clear.
get_projs_st @biclist. clear.
get_projs_st Ind_test. clear.
get_projs_st Ind_test2. clear.
Abort.


Goal False.
pose_gen_statement nat. clear.
pose_gen_statement list. clear.
pose_gen_statement @nelist. clear.
pose_gen_statement @biclist. clear.
pose_gen_statement Ind_test. clear.
pose_gen_statement Ind_test2. clear.
Abort.


End tests_proj.

Ltac instantiate_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x) end in H'
  | _ => fail
      end.

(* Instantiate a statement by trying to find an inhabitant in the local context (or by using 
the canonical inhabitant of the CompDec typeclass *)
Ltac instantiate_inhab H :=
let T := type of H in 
match T with 
| forall (y : ?A), forall (z : ?B), _ => try (let inh := find_inh A in
let H' := instantiate_ident H inh in instantiate_inhab H' ; clear H)
| _ => idtac
end.

(* Instantiate polymorphic statements with a given tuple of subterms of type Type 
and calls instantiate_inhab *)
Ltac instantiate_tuple_terms_inhab H t1 t2 := match t1 with
| (?x, ?t1') => try (let H' := instantiate_ident H x in
instantiate_tuple_terms_inhab H' t2 t2) ; try (instantiate_tuple_terms_inhab H t1' t2)
| default =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => first [constr_eq A Type ; clear H | instantiate_inhab H]
            | _ => idtac
            end
end.

Ltac instantiate_tuple_terms_goal_inhab H t0 := let t0 := return_tuple_subterms_of_type_type in
let t := eval compute in t0 in instantiate_tuple_terms_inhab H t t.


Ltac get_projs_st_default_quote I t0 :=
let t := eval compute in t0 in 
let H' := gen_statement I in
instantiate_tuple_terms_inhab H' t t.

Section tests_default.

Variable A : Type.
Variable a : A.

Goal nat -> A -> False.
let t0 := return_tuple_subterms_of_type_type in 
get_projs_st_default_quote list t0. clear -a.
let t0 := return_tuple_subterms_of_type_type in 
get_projs_st_default_quote Ind_test t0. clear -a.
let t0 := return_tuple_subterms_of_type_type in 
get_projs_st_default_quote Ind_test2 t0. clear -a.
Abort.

End tests_default.



Fixpoint is_ind_not_in_list (t : term) (l : list term) := 
match t with
| tInd ind _ => let name := (inductive_mind ind).2 in match l with
         | nil => true
         | cons x xs => match x with
                           | tInd ind' _ => let name' := (inductive_mind ind').2 in if String.eqb name name' then false 
else is_ind_not_in_list t xs
                           | _ => is_ind_not_in_list t xs
                        end
         end
| _ => false
end.

Fixpoint get_ind_of_prod_no_dup (t : term) (acc : list term) (acc' : list term) :=
match t with
| tProd _ A u => let I := (dest_app A).1 in if is_ind_not_in_list I acc
then get_ind_of_prod_no_dup u (I:: acc) (I :: acc') else get_ind_of_prod_no_dup u acc acc'
| _ => acc'
end.

Definition get_ind_of_prod_no_dup_default t := 
get_ind_of_prod_no_dup t [bool_reif ; Z_reif; nat_reif ; eq_reif] [].

Ltac elims_on_list l t := 
match l with 
| nil => idtac 
| cons ?x ?xs => let u := metacoq_get_value (tmUnquote x) in 
                 let I := eval hnf in (u.(my_projT2)) in 
                 try (get_projs_st_default_quote I t) ; elims_on_list xs t
end.

Ltac get_projs_in_goal := 
let t0 := return_tuple_subterms_of_type_type in
let t := eval compute in t0 in
match goal with 
| |- ?T => let T_reif := metacoq_get_value (tmQuote T) in 
          let l := eval compute in (get_ind_of_prod_no_dup_default T_reif) in
          elims_on_list l t
end.

From Ltac2 Require Import Ltac2.

(* Checks if a given term is a variable of type which is not Prop *)
Ltac2 is_var (v : constr) :=
let k := Constr.Unsafe.kind v in
match k with
| Constr.Unsafe.Var id => true
| _ => false
end.

Ltac2 is_indu (c : constr) := 
let k := Constr.Unsafe.kind c in
match k with
| Constr.Unsafe.Ind indu inst => true
| _ => false
end.


(* Returns the tuple of variables in a local context *)
Ltac2 vars () := 
let hyps := Control.hyps () in
List.map (fun x => match x with
            | (x1, x2, x3) => x1 end) 
(List.filter (fun x => match x with
            | (x1, x2, x3) => let x' := Control.hyp x1 in is_var (x') end) hyps).

Ltac2 rec is_not_in_tuple (p : constr) (z : constr) := 
match! p with
| (?x, ?y) =>  if is_not_in_tuple x z then is_not_in_tuple y z else false
| _ => if Constr.equal p z then false else true
end.

Ltac2 get_head (c : constr) :=
let k := Constr.Unsafe.kind c in 
match k with
| Constr.Unsafe.App c1 carr => c1 
| _ => c
end.

Ltac2 rec list_constr_printer (l : constr list) :=
match l with
| [] => (Message.print (Message.of_string "empty"))
| x :: xs => Message.print (Message.of_constr x) ; list_constr_printer xs
end.

Ltac2 message_of_bool (b: bool) :=
match b with
| true => (Message.print (Message.of_string "true"))
| false => (Message.print (Message.of_string "false"))
end.

Ltac2 is_sort (c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Sort _ => true
  | _ => false
  end.

Ltac2 get_projs_in_variables (p : constr) := 
let var := vars () in 
let rec aux (p : constr) (l: ident list) := 
match l with
| [] => ()
| x :: xs =>  let x' := Control.hyp x in
    let ty := Constr.type x' in
    let tyty := Constr.type ty in 
    if is_sort ty then aux p xs else
    if Constr.equal tyty 'Prop then aux p xs else
    let hd := get_head ty in
    if is_indu hd then 
    if
    is_not_in_tuple p ty then
    let ind := get_head ty in
    if is_not_in_tuple p ind then 
    (ltac1:(ind ty |- try (let params := get_tail ty in (* removing this idtac may cause infinite loops *)
    get_projs_st_default_quote ind params)) (Ltac1.of_constr ind) (Ltac1.of_constr ty)) ; 
    aux constr:(($p, $ty)) xs 
    else aux p xs else aux p xs else aux p xs
end
in aux p var.

Section tests.

Inductive test: Set :=
    one : test
  | two : test
  | three : test
  | four : test
  | five : test
  | six : test.

Goal test -> False.
   
Proof. intros. get_projs_in_variables 'bool.
Abort.

Variable A : Type.
Variable HA : CompDec A.

Goal (forall (A : Type) (HA : CompDec A) (l : list A), False -> False).
Proof. intros. get_projs_in_variables 'bool. Abort.

Lemma app_eq_nil (l l' : list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. get_projs_in_variables 'unit. Abort. 

End tests.
