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
Require Import elimination_polymorphism.
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
For instance, for the type list, whose constructors are [] (0 argument) and :: (2 arguments ), we declare in the local context two functions proj_{1,0} : forall (A : Type), A -> list A -> list A and proj_{1,1} : forall (A : Type) list A -> list A -> list A such that:
* proj_{1,0} def [] = def and proj_{1,0} d {a :: l} = a 
* proj_{1,1} def [] = def and proj_{1,1} d {a :: l} = l 
The metavariable d stands for a dummy default value, of respective types A (for proj_{1,0}) and list A (for proj_{1,1})

(2) automatically prove in the local context the generation statement, specifying that every inhabitant t of I is equal to a constructor applying to the projections of t.
For instance, in the case of list, the main tactic produces and proves the statement:
forall (A : Type) (d_{1,0} : A)  (d_{1,1} l: list A), (l =  []) \/ (l = ((proj_{1,0} d_{1,0} l)) :: ((proj_{1,1} d_{1,1} l))

Some implicit arguments have been omitted: technically,  proj_{1,0} : forall (A : Type), A -> list A -> list A and proj_{1,1} : forall (A : Type) list A -> list A -> list A and the generation statement is: 
forall (A : Type) (d_{1,0} : A)  (d_{1,1} l: list A), (l = @nil A) \/ (l = (proj_{1,0} A d_{1,0} l) :: (proj_{1,1} A d_{1,1} l) *)

(* \TODO change metavariables A and lA into P and lP *)

(* 
Let us get now into the technical details.
Given an inductive datatype I, we use the following conventions:
* p : number of parameters of I
* A_0, ..., A_{p-1}: the types of the parameters of I
  lA := [ A_0 ; ... ; A_{p-1} ]
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

From the ???? point of view, a reified inductive type contains:
* a term of type 'inductive' (metavariable indu)
* a mutual_inductive_body (metavariable mind)
* mind contains a list of one_inductive_body's (metavariable oind)
* each one_inductive_body contains relevant information about, e.g., its constructors and their types
(* \TODO pointer vers le fonctions de aux_fun_list comme pose_mind etc *)

We must define projections proj_{i,j} for i = 0, ... , k-1 and j = 0, ..., n_i-1
proj_{i,j} = lam X_0 : A_0 ... lam X_{p-1} : A_{p-1} Lam def_{i,j} : Aunlift_{i,j} x : (I X_0 ... X_{p-1}), match x with
| C_i X_0 ... x_{i,0} ... x_{i,n_i-1} => x_{i,j} 
| C_j X_0 ... x_{j,0} ... x_{j,n_j-1} => def_{i,j}
end.




We set I' = tApp I [tRel p ; ... ; tRel 1]
Then, the reification of proj_{i,j} is:
tLam P_0 ... P_{p-1} tLam Aunlift_{i,j} tLam I' 
tCase (I_indu , p , relevant ) ( tProd ((I')^{+1}) -> (Aunlift_{i,j}^{+3}) ) (tRel 0) 
tCase [ (n_0 ; tLam A_{0,0}^{+2} ... A_{0,n_0-1}^{+2}) (tRel (S n_0)) ) ; ... ;
        (n_i ; tLam A_{0,i}^{+2} ... A_{i,n_i-1}^{+2}) (tRel (S n_i)) ) ; ... ;  
        (n_j ; tLam A_{0,0}^{+2} ... A_{j,n_j-1}^{+2} tRel (n_j-1-i ) ) ; ...]  (* \TODO check if -1 *)
        


The reificaiton of the generation statement is:
tProd A_0 ... A_ {p-1} 
tProd Au_{0,0}^{+0} Au_{0,1}^{+1} ... Au_{0,j}^{+j} ... Au_{0,n_0-1}^{+n_0-1}
      Au_{1,0}^{+n_0} Au_{1,1}^{n_0+1} ...
      .... Au_{i,j}^{L_j+j}... Au_{k-1,n_k-1}^{L_{k-1}-1}
tProd (x : (I')^{+????} }  
  or_reif 
     eq_reif _ (tRel 0)  pstat_0 ; 
     eq_reif _ (tRel 0) pstat_1 ; ... ;
     eq_reif _ (tRel 0) pstat_{k-1}

where L_i := n_0 + ... + n_{i-1} 
and pstat_i := C_i [ _p ; 
        proj_{i,0} [ _p ; tRel ??? ; tRel 0 ]
        .... ;
        proj_{i,j} [ _ p ; tRel ??? ; tRel 0] ; ...]
       
_p is a macro for p evars 
 *)


(* list_types_of_each_constructor est déjà calculée, dans utilities
  \TODO unifier
*)


(* \TODO : renommer impossible_term, qui est un inductif vide et qui sert surtout de marqueur *)

(* \TODO éliminer la variable return_type, qui est probablement un lift de default_type *)



(* get_indu_app_to_params t p = tApp t [tRel (p-1) ; .... ; tRel 0]
   tail-recursive
   \TODO remove this function, the lift0 1 in the main function and use the one below (get_indu_app_to_params0) instead
*)
Definition get_indu_app_to_params (t : term) (p : nat) := 
  let fix aux p acc :=
   match p with
   | 0 => acc 
   | S p => aux p ((tRel p)::acc)
   end
in tApp t (tr_rev (aux p [])). 

(* get_indu_app_to_params t p = tApp t [tRel p ; .... ; tRel 1]
   tail-recursive
*)
Definition get_indu_app_to_params0 (t : term) (p n: nat) := 
  tApp t (Rel_list p n).

(* \TODO transfer in utilities *)
(* mkProd [A1 ; .... ; An ] t = tProd _ An. ... tProd _ A1. t   (reverts list) *)
Fixpoint mkProd_rec (l : list term)  (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd (mkNamed "x")  x t)
end.
(* \TODO mkProd_rec n'est utilisée que dans get_projs_st_return, mais deux fois sur la même ligne
Voir si on peut éliminer ou facto du code.
*)

(* same thing but one provides a name for the bound variables *)
Fixpoint mkProd_rec_n (na : ident) (l : list term)  (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec_n na xs (tProd (mkNamed na)  x t)
end.



(* mkLam [A1 ; .... ; An ] t = Lam "x/A" An. ... tProd "x/A" A1. t   (reverts list) *)
Fixpoint mkLam_rec (l : list term)  (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkLam_rec xs (mkLam x t)
end.


(***************)

Ltac find_inhabitant_context t := 
first[ constructor ; assumption | apply Inh | epose (inhab := ?[t_evar] : t)]. 

Ltac find_inh t :=
match goal with
| H : t |- _ => H
| _ => let H := fresh in let _ := match goal with _ => assert (H : t) by find_inhabitant_context t end in H
end.


(* removes k to each de Brujin index: useful when variables are removed *)
(* Remark: does not work with dependencies. Should perhaps use subst instead *)
Fixpoint unlift (k : nat) (t : term)  {struct t} : term :=
  match t with
  | tRel i => tRel (i-k)
  | tEvar ev args => tEvar ev (map (unlift k) args)
  | tCast c kind t0 => tCast (unlift k c) kind (unlift k t0)
  | tProd na A B => tProd na (unlift k A) (unlift k B)
  | tLambda na T M => tLambda na (unlift k T) (unlift k M)
  | tLetIn na b t0 b' => tLetIn na (unlift k b) (unlift k t0) (unlift k b')
  | tApp u v => tApp (unlift k u) (map (unlift k) v)
  | tCase ind p c brs =>
      let brs' := map (on_snd (unlift k)) brs in
      tCase ind (unlift k p) (unlift k c) brs'
  | tProj p c => tProj p (unlift k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (unlift k) (unlift k')) mfix in tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (unlift k) (unlift k')) mfix in
      tCoFix mfix' idx
  | _ => t
  end.

(** version with default = tRel 1 **)

(* constructs the function associated with the branchs which should return a default value *)
(* l0 is supposed to be the list of types of the parameters of the constructors, e.g. for cons: 
[tRel 0 ; tApp list_reif [tRel 1]]
*)
(* \Q what is n supposed to represent? *)
 
(* branch_default_var l0 i k n  (* \TODO metavariables *)
   = Prod x1 hole. ... Prod xlen hole. Rel (len - rkproj) if k = n
   = Prod x1 hole ... Prod xlen hole. Rel (len + 1) if k
   where len = length l0
   Motivation: \TODO 
*)

(* branch_default_var l0 i k j  =  (* \TODO update *)
    tRel kp _  ... _ (with len0 holes)
    where len0 is the length of l0
    kp = len0 - i if j = k
    kp = len0 + 1 if j <> k 
    * If j <> k then, tRel kp denotes def, the default variable
    Indeed, tRel kp is tRel 1 lifter len0 times
    * If j = k, then tRel kp denotes the variable that is bound by the hole of rank i
    *)
(* same function, but when the length is given*)
(* \TODO metavariables? What should q be? *)


Definition branch_default_var (ni : nat)  (i : nat) (j : nat) (q : nat) := 
      let kp := if Nat.eqb i q then ni - (S j)  
      else S ni in
      let fix aux i acc :=
      match i with 
      | 0 => acc 
      | S i => aux i (mkLam hole acc)
      end
      in aux ni (tRel kp).  

   

(* \TODO long term: recover the "relevant" parameter and not hard-code it *)
(* Constructs the pattern matching in the proj
for instance, given the right arguments to construct the predecessor function we get the reified
< match x with
| 0 => default
| S y => y > *)
(* note: pas besoin de list de list de termes, mais seulement de leur longueur,
cf. branch_default_var *)
(* construit le match de l'éliminateur et le default variable non-liée tRel 1 *)



 (* \TODO : pas clair ce que sont les entier dans list (nat * term) de tCase *)
(* mkCase [len0 ; ... ; lenn ] i k = [(0, tProd _(len0) (tRel db0) ) ; 
... ; (n, tProd _(len0) dbn)] : list (nat * term) 
    where tProd _(lenj) denotes tProd _ ... tProd _   (leni times)
    and dbk = lenk - i  
        dbj = lenj + 1   if j <> j 
*)

  
  Definition mkCase_list_param (ln : list nat)  (i : nat) (j : nat) :=
    let fix aux ln q acc :=
    match ln with
    | [] => acc
    | len0 :: ln => aux ln (S q)  ((len0 , branch_default_var len0 i j q) :: acc )
    end
    in tr_rev (aux ln 0 (* 1*) []). 


(* \TODO calculer directement lift0 1 I_app *)
(* \TODO voir si pas de rev qui se cachent plus haut, notamment pour retourner llAunlift *)
(* rq: ty_arg_constr = map rev llAunlift *)
Definition proj_ij (p : nat) (lA_rev : list term) (I : term) (indu : inductive)  (i : nat) (j : nat)
(llAunlift : list (list term)) (ln : list nat) (Aiju : term):= 
mkLam_rec lA_rev  
 (mkLam Aiju (mkLam (get_indu_app_to_params0 I p 1)
(tCase (indu, p, Relevant)  (mkLam (get_indu_app_to_params0 I p 2) (lift0 3 Aiju)) (tRel 0)  (mkCase_list_param ln i j)))).


(* This function computes the projections of an inductive type the projections in the local environment
  \TODO some tr_rev's could perhaps be avoided if collect_projs is merged with the Ltac function declare_projs below
*)
Definition collect_projs (p : nat) (lA_rev : list term) (I : term) (indu: inductive)
(llAunlift : list (list term)) (ln : list nat) (k : nat)
:= let fix aux1 (i : nat) (nk :nat) lAk' acc :=
  match (nk,lAk') with 
  | (0,[]) => acc 
  | (S j, Aiju :: lAk') => aux1 i nk lAk' ((proj_ij p lA_rev I indu i j llAunlift ln (Aiju)):: acc)
  | _ => [] (* this case should not happen *)
  end 
in 
let fix aux2 llAu' ln' i'  acc :=
match (i',llAu',ln') with
| (0,[],[]) => acc
| (S i,lAi :: llAu' , ni :: ln' ) => aux2 llAu' ln' i ((aux1 i ni (tr_rev lAi) []) :: acc)
| _ => []
end in
aux2 (tr_rev llAunlift) (tr_rev ln) k []. 


(* \TODO improve the naming of the functions *)
Ltac declare_projs_ctor_i  na p lA_rev I indu llAu ln i lAi ni :=
  let _ := match goal with _ =>  idtac end in let lAi' := constr:(tr_rev lAi) in 
  let rec aux1 i j lAi' acc :=
  lazymatch j with
  | 0 => constr:(acc)
  | S ?j0 => lazymatch eval hnf in lAi' with
   | ?Aiju :: ?tlAi' =>  let pij := constr:(proj_ij p lA_rev I indu i j0 llAu ln Aiju) in let name :=  fresh "proj_" na  in let _ := match goal with _ => pose_unquote_term_hnf pij name
    end in let pij_tVar := metacoq_get_value (tmQuote name)  in let acc0 := constr:(pij_tVar :: acc) in let z := aux1 i j0 tlAi' acc0 in constr:(z)
   end 
   | _ => idtac "erroc declare_projs_ctor_i"
  end
  in   let res_dpi := aux1 i ni lAi' (@nil term) in constr:(res_dpi)
.

(* \TODO améliorer le nommage *)
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
  (* \TODO  currently, the projections are in order in the output, but it would be better that they are in the reverse order to produce the generation statement
  (indeed, we need to perform one reverse)
  *)

Ltac declare_projs na p lA_rev I indu llAu ln nc :=
  let llAu_rev := constr:(tr_rev llAu) in let ln_rev := 
constr:(tr_rev ln)    
in 
 let rec aux llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in match eval hnf in y with
| (?y0 , ?ln0') => 
  match eval cbv in ln0' with
  | (@nil nat) =>   constr:(acc) 
  | ?nk :: ?tln0 =>
    match eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k =>  (* idtac "blut 5" ; *)  match eval hnf in lAu' with
        | ?lAk :: ?tlAu'=> 
        let dpk  := declare_projs_ctor_i na p lA_rev I indu llAu ln k  lAk nk in let acc0 := constr:(dpk :: acc ) in let res2 := aux tlAu' tln0 k acc0 in  constr:(res2)
  end 
  end   
  end
  end 
 |_ => idtac "error declare_projs "
end
in 
let res_dp := aux llAu_rev ln_rev nc (@nil (list term))  in constr:(res_dp)
. 






(*** \TODO one unique function which declares the projectors of I in the local context
 and outputs the list of lists of their tVar's
*)
Ltac declare_projs0 p lA_rev  I indu llAunlift  ln nc 
:= 
match goal with _ => let rec aux1 k  i  lAk' acc := 
 let x := constr:((i,lAk'))   in (* idtac "blut 0" ; *)
  lazymatch eval hnf in x with
   | (?i,?lAk') => lazymatch eval hnf in i with
     | 0 => constr:(acc) 
     | S ?i => lazymatch eval hnf in lAk' with
       | ?Akiu :: ?lAk' => let res1 := aux1 k i lAk' constr:(((proj_ij p lA_rev I indu k i llAunlift ln (Akiu)):: acc))in constr:(res1)
       end end
   | _ => idtac "error declare_projs 1"
  end 
in
let rec aux2 llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in  lazymatch eval hnf in y with
| (?y0 , ?ln0') => 
  lazymatch eval cbv in ln0' with
  | (@nil nat) => constr:(acc) 
  | ?i :: ?ln1' => 
    lazymatch eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k => (* idtac "blut 5" ; *) lazymatch eval hnf in lAu' with
        | ?lAk :: ?lAu'=> let res2 := aux2 llAu' ln' k constr:((aux1 k i (tr_rev lAk) (@nil term)) :: acc) in constr:(res2)
  end 
  end   
  end
  end 
  |_ => idtac "error declare_projs 1"
end
in let res := aux2 constr:(tr_rev llAunlift) constr:(tr_rev ln) nc (@nil term)  in constr:(res)
end
.





(************************************************************************************)
(* The tactic defining projections in the local context have been specified above   *)
(* Below, we define the tactic stating and proving the generation statement         *)
(************************************************************************************)

(**  mkOr0 [A1_reif ; ... ; An_reif] produce the reification of(...(An \/ (A_{n-1}) ... A_2) \/ A_1)..)
     i.e. reverts list and associates to the *left* (better for SMTLib) **)
(**     tail-recursive **)
(* \TODO rename into mkOr_n *)
Definition mkOr (l : list term) :=
  match l with
  | [] => True_reif
  | t0 :: l0 => 
    let fix aux l acc := match l with
    | [] => acc
    | t :: l => aux l (tApp or_reif (acc :: [t])) 
    end
    in aux l0 t0
  end.


(*
proj_return_types [[A_{0,0} ; ... ; A_{0,l_0}] ; ... ; [A_{k,0} ; .... ; A_{k,l_k}] ]
    = [ [A_{0,0}] ; A_ {1,1} ^{-1} ; ... ; A_{l_0}^{-l_0} ] ; ... ;
         [A_{k,0}] ; A_ {k,1} ^{-1} ; ... ; A_{l_k}^{-l_k}] ]
      \TODO helps compute the return types of the projections
*)
(* \TODO choose between proj_return_types and ret_ty_proj (the former is the latter + tr_map )*)
Definition proj_return_types (llA: list (list term)) :=
  let fix aux acc i lA :=
    match lA with
    | [] => acc 
    | A :: tlA => aux ((unlift i A) :: acc ) (S i) tlA
  end  in  (tr_map (fun lA => tr_rev(aux [] 0  lA)) llA).


Definition ret_ty_proj lA 
  := let fix aux l k acc := 
    match l with
    | [] => acc 
    | A :: l => aux l (S k) ((unlift k A) :: acc)
    end in tr_rev (aux lA 0 []).


(* warning: handles parameters but not dependent arguments *)


(* \TODO : bind_def_val_in_gen [[A_{0,0} ; ... ; A_{0,l_0-1}] ; ... ; [A_{k,0} ; .... ; A_{k,l_k-1}] ]
                                  [l0 ; ... ; lk ]
    = [ A_{k,l_k}^L ; ... ; A_{0,1}^{+1} ; A_{0,0}^0 ]
      where L = l_0 + ... + l_k
      Thus, bind_def_val_in_gen performs a flattening, a revert and a incremental lift of all the elements of the initial list of lists
    *)
(* \TODO peut-être conserver les accumulateurs l0, l0+l1, l0+l1+l2, ou alors les calculer séparément et faire 
l'incrémentation à partir de la liste lnacc *)
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



(* holes_p p = [hole ; ... ; hole] (p occurrences)
   linear *)
   Definition holes_p (p : nat) :=
    let fix aux p acc := 
    match p with
    | 0 => acc 
    | S p => aux p (hole :: acc)
  end in aux p [].
  
  (* holes_p p = [hole ; ... ; hole ; tRel db ; tRel 0] with p holes 
      \TODO useful to pass the parameters to the projections,
      cf. get_elim_applied and get_eq_x_ctor_projs *)
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
  mkEq hole (tRel 0) (tApp ctor (rev_append (holes_p p) (tr_rev (aux projs (S db) [])))).


(* \todo check that the db are computed somewhere *)
(* \todo, here, one rather needs a revert mkOr *)
(* \todo see if this needs to be reverted later*)
(* get_generation_disjunction p ctors list_proj ldb 
   outputs the reification of forall x : I, 
   x = C0 (projs0 x) \/ .... \/ x = Ck (projsk x)
   where lctors is the list of the (reified) constructors of an inductive, list_proj is the list of lists of their projections  (which are computed by the tactic declare_projs)
  x = Ck (projsk x) is a shortening of x = Ck (proj_{k,0} d_{k,0} x) .... (proj_{k,nk-1} d_{k,nk-1} x) and d_{k,i} the default value for d_{k,i} (x = Ck (projsk x) is computed with get_eq_x_ctor_projs)
   ldb is the list of De Bruijn indices of ????
   L is the total number of the arguments of all constructors (withstanding type parameters )
   Note that mkProd tApp I (Rel_list L p) _
   is forall x : I A1 ... Ap, _
   *)
(* \TODO remove ldb argument *)


 Definition get_generation_disjunction  (p : nat) (I: term) (L : nat) (lc : list term) (list_proj : list (list term)) (ln : list nat) :=
  let fix aux lc list_proj lN acc := 
  match (lc,list_proj,lN) with
  | ([],[],[]) => acc
  | (ctor :: tlc , projs :: tl_proj, db :: tlN ) => aux tlc tl_proj tlN  ((get_eq_x_ctor_projs p ctor projs db) :: acc)
  | _ => [] (* this cases does not happen *)
 end in let lN := rev_acc_add (tr_rev ln)   (* perhaps some optimization there *) 
 in tProd (mkNamed "x") (tApp I (Rel_list p L)) (mkOr (aux lc list_proj lN [])) .



(** args_of_projs_in_disj [ n1 ; .... ; nk ] = [[tRel L ; tRel L-1 ; ....; tRel (L-n1+1) ] ; ... ; [tRel nk ; ... ; tRel 1]  ] 
    where L = n1 + ... + n1
    i.e. the sublists have respective lengths ni and the de Bruijn index decreases at each step
    args_of_projs_in_disj [1 ; 3 ; 2 ] = [ [tRel 6 ] ; [tRel 5 ; tRel 4 ; tRel 3] ; [tRel 2 ; Rel 1]]
    This function helps specify the Db index of the default variable of each projection in the big disjunction
    **)
(* \Q : do we need this function? *)
Definition args_of_projs_in_disj (ln : list nat) : list (list term) :=
  let ln_rev := tr_rev ln in
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




(*  \TMP *)
(* Ltac clearbody_tVar_list l :=
  match eval hnf in l with
  | [] => idtac 
  | ?c :: ?l0 => match c with
    | tVar ?idn => cbd idn ; clearbody_tVar_list l0
end
end. *)

(* Ltac clearbody_tVar_llist l :=
  match eval hnf in l with
  | [] => idtac 
  | ?l0 :: ?tl0 => clearbody_tVar_list l0 ; clearbody_tVar_llist tl0
end. *)

(* \TODO move up the definition of nat_oind. In utilities.v? *)



Ltac gen_statement t := 
  let Helim := fresh "gen_" t in let _ := match goal with _ => 
  let indmind := fresh "indmind" in info_indu t indmind ; 
  lazymatch eval compute in indmind with
  | (?induu,?mind) => 
    lazymatch eval hnf in induu with
    | (?indu, ?u) =>
    let pparams := eval compute in (get_params_from_mind mind) in
    lazymatch eval hnf in pparams with 
    | (?p,?lA) =>
    lazymatch eval hnf in pparams with
    | (?p, ?lA) => let oind := eval compute in (hd nat_oind mind.(ind_bodies)) in
     let gct := eval compute in  (get_ctors_and_types_i indu p 1 0 u  oind) 
   in  lazymatch eval hnf in gct with 
    | (?lBfA,?ln) => lazymatch eval hnf in lBfA with
      | (?lBf,?llA) =>  lazymatch eval cbv in lBf with
        | (?lB,?lc) =>    let llAtrunc := eval compute in (tr_map (skipn p) llA) in  let nc := eval compute in (leng ln) in 
        let lA_rev := eval compute in (tr_rev lA) in let llAu := eval compute in (tr_map ret_ty_proj llAtrunc) in let t_reif := constr:(tInd indu u) in  let L := constr:(fold_left Nat.add ln 0) in
        let res3 := 
         declare_projs t p lA_rev t_reif indu llAu ln nc in let llprojs := fresh "llprojs" in 
         pose (llprojs  := res3) ; 
        let ltypes_forall := constr:(bind_def_val_in_gen llAu ln) in 
        let ggd := constr:(mkProd_rec_n "A" lA_rev (mkProd_rec_n "d" ltypes_forall (get_generation_disjunction  p t_reif L  lc  llprojs  ln))) in 
          let gent := fresh "gen_stat" t in pose_unquote_term_hnf ggd gent  ; let L' := eval compute in (p + L) in assert (Helim : gent) by  prove_by_destruct_varn L' ; unfold gent in Helim ; 
      (* clearbody_tVar_llist llprojs; *) clear gent indmind llprojs (* \TODO add clearbody  *)
        end 
      end
    end
    end
  end end end end in Helim
  .       
   

Ltac pose_gen_statement t :=
  let gent := fresh "gen_st_" t in let x := gen_statement t in pose x as gent.


(* \TMP *)
Ltac get_projs_st_return t := gen_statement t. 




(* \TMP *)
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
get_projs_st list. clear.
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
| impossible_term =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => first [constr_eq A Type ; clear H | instantiate_inhab H]
            | _ => idtac
            end
end.

Ltac instantiate_tuple_terms_goal_inhab H t0 := let t0 := return_tuple_subterms_of_type_type in
let t := eval compute in t0 in instantiate_tuple_terms_inhab H t t.

Ltac get_projs_st_default I t0 :=
let t := eval compute in t0 in 
let H' := gen_statement I in
instantiate_tuple_terms_inhab H' t t.

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
| tProd _ A u => let I := (no_app A).1 in if is_ind_not_in_list I acc
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

(* Checks if a given term is a variable *)
Ltac is_var v :=
let v_reif := metacoq_get_value (tmQuote v) in 
match v_reif with 
| tVar _ => idtac
| _ => fail
end.

(* Returns the tuple of variables in a local context *)
Ltac vars := 
match goal with
| v : _ |- _ => let _ := match goal with _ => is_var v ; revert v end in let acc := vars in 
let _ := match goal with _ => intro v end in constr:((v, acc))
| _ => constr:(unit)
end.

Ltac get_projs_in_variables p := 
let t := vars in 
let rec tac_rec v tuple :=
match v with
| (?v1, ?t') => let T := type of v1 in first [ let U := type of T in constr_eq U Prop ; tac_rec t' tuple |
                let I := get_head T in 
                let params := get_tail T in 
                try (is_not_in_tuple tuple T  ;
                get_projs_st_default_quote I params) ; try (tac_rec t' (tuple, T)) ]
| _ => idtac
end
in let prod_types0 := eval compute in p in tac_rec t prod_types0.

Section tests.

Inductive test: Set :=
    one : test
  | two : test
  | three : test
  | four : test
  | five : test
  | six : test.

Goal test -> False.
   
Proof. intros. get_projs_in_variables bool.
Abort.

End tests.
