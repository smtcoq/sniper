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

(* \TMP *)
MetaCoq Quote Definition S_reif := S. 
MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition Set_reif := Set.
MetaCoq Quote Definition list_reif := list.
(* \TODO changer les metavariables 
- nb --> rk ou k ou n tout court (avec spec )
- une métavariable pour les rangs dans tCase 
- i metavariable pour rang de la proj (anciennment nbproj)
*)

(* list_types_of_each_constructor  est déjà calculée, dans utilities
  \TODO unifier
*)




(* \TODO : renommer impossible_term, qui est un inductif vide *)

(* \TODO éliminer la variable return_type, qui est probablement un lift de default_type *)



(* get_indu_app_to_params t n = tApp t [tRel (n-1) ; .... ; tRel 0]
   tail-recursive
   \TODO remove this function, the lift0 1 in the main function and use the one below (get_indu_app_to_params0) instead
*)
Definition get_indu_app_to_params (t : term) (n : nat) := 
  let fix aux n acc :=
   match n with
   | 0 => acc 
   | S n => aux n ((tRel n)::acc)
   end
in tApp t (tr_rev (aux n [])). 

(* get_indu_app_to_params t n = tApp t [tRel n ; .... ; tRel 1]
   tail-recursive
*)
Definition get_indu_app_to_params0 (t : term) (p n: nat) := 
  tApp t (get_list_of_rel_lifted p n).

(* mkProd [A1 ; .... ; An ] t = tProd _ An. ... tProd _ A1. t   (reverts list) *)
Fixpoint mkProd_rec (l : list term)  (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd (mkNamed "x")  x t)
end.
(* \TODO mkProd_rec n'est utilisée que dans get_eliminators_st_return, mais deux fois sur la même ligne
Voir si on peut éliminer ou facto du code.
*)



Goal False.
let x := constr:(mkProd_rec [tRel 3 ; tRel 5 ; tRel 8] (tRel 13)) in pose x as mprex ; compute in mprex.
Abort.

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


(* removes k to each de Brujin indexes: useful when variables are removed *)
(* \TODO ??? higher order version where fun i => i - k abstracted, if possible (not sure with tCase )*)
(* \Rk does not work with dependencies. Should perhaps use subst instead *)
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
 
(* branch_default_var l0 i k n 
   = Prod x1 hole. ... Prod xlen hole. Rel (len - rkproj) if k = n
   = Prod x1 hole ... Prod xlen hole. Rel (len + 1) if k
   where len = length l0
   Motivation: \TODO 
*)

(* branch_default_var l0 i k j  = 
    tRel kp _  ... _ (with len0 holes)
    where len0 is the length of l0
    kp = len0 - i if j = k
    kp = len0 + 1 if j <> k 
    * If j <> k then, tRel kp denotes def, the default variable
    Indeed, tRel kp is tRel 1 lifter len0 times
    * If j = k, then tRel kp denotes the variable that is bound by the hole of rank i
    *)

 

(* same function, but when the length is given*)
(* \TODO order of the parameters? *)
Definition branch_default_var (lenk  : nat) (i : nat) (k : nat) (j : nat) := 
    let kp := if Nat.eqb k j then lenk - i
    else S lenk in
    let fix aux k acc :=
    match k with 
    | 0 => acc 
    | S k => aux k (mkLam hole acc)
    end
    in aux lenk (tRel kp).  


Definition branch_default_var1 (lenk  : nat)  (k : nat) (i : nat) (j : nat) := 
      let kp := if Nat.eqb k j then lenk - (S i)  
      else S lenk in
      let fix aux k acc :=
      match k with 
      | 0 => acc 
      | S k => aux k (mkLam hole acc)
      end
      in aux lenk (tRel kp).  

   

(* \TODO long term: recover the "relevant" parameter and not hard-code it *)
(* Constructs the pattern matching in the eliminator
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
 Definition mkCase_list_param (llen : list nat) (i : nat) (k : nat) :=
  let fix aux llen j acc :=
  match llen with
  | [] => acc
  | len0 :: llen => aux llen (S j)  ((len0 , branch_default_var len0 i k j) :: acc )
  end
  in tr_rev (aux llen 0 (* 1*) []). 
  
  Definition mkCase_list_param1 (llen : list nat)  (k : nat) (i : nat) :=
    let fix aux llen j acc :=
    match llen with
    | [] => acc
    | len0 :: llen => aux llen (S j)  ((len0 , branch_default_var1 len0 k i j) :: acc )
    end
    in tr_rev (aux llen 0 (* 1*) []). 



(*  \TODO 
  mkCase_eliminator_default_var0 indu p i k ty_arg_constr return_type 
    denotes the pattern-matching of the projector p_{i,k} for an inductive type I
    whose 'inductive' is indu, which has p parameters
    ty_arg_constr is supposed to be \TODO
    return_type is supposed to be \TODO
*)
Definition mkCase_eliminator_default_var (indu : inductive) (p : nat) (i : nat) (k : nat)
(ty_arg_constr : list (list term)) (return_type : term) := 
let llen := tr_map (@List.length term) ty_arg_constr  in 
tCase (indu, p, Relevant) return_type (tRel 0) (mkCase_list_param llen i k).



(* \TODO calculer directement lift0 1 I_app *)
(* \TODO voir si pas de rev qui se cachent plus haut, notamment pour retourner llAunlift *)
(* rq: ty_arg_constr = map rev llAunlift *)
Definition proj_ki (p : nat) (lA_rev : list term) (I : term) (indu : inductive)  (k : nat) (i : nat)
(llAunlift : list (list term)) (ln : list nat) (Akiu : term):= 
mkLam_rec lA_rev  
 (mkLam Akiu (mkLam (get_indu_app_to_params0 I p 1)
(tCase (indu, p, Relevant)  (mkLam (get_indu_app_to_params0 I p 2) (lift0 3 Akiu)) (tRel 0)  (mkCase_list_param1 ln k i)))).






(* This function computes the projections of an inductive type the projections in the local environment
  \TODO some  tr_rev's could perhaps be avoided if collect_projs is merged with the Ltac function declare_projs below
*)
Definition collect_projs (p : nat) (lA_rev : list term) (I : term) (indu: inductive)
(llAunlift : list (list term)) (ln : list nat) (nc : nat)
:= let fix aux1 (k : nat) (nk :nat) lAk' acc :=
  match (nk,lAk') with 
  | (0,[]) => acc 
  | (S i, Akiu :: lAk') => aux1 k nk lAk' ((proj_ki p lA_rev I indu k i llAunlift ln (Akiu)):: acc)
  | _ => [] (* this case should not happen *)
  end 
in 
let fix aux2 llAu' ln' k  acc :=
match (k,llAu',ln') with
| (0,[],[]) => acc
| (S k,lAk :: llAu' , nk :: ln' ) => aux2 llAu' ln' k ((aux1 k nk (tr_rev lAk) []) :: acc)
| _ => []
end in
aux2 (tr_rev llAunlift) (tr_rev ln) nc []. 


(* \TODO améliorer le nommage *)
Ltac declare_projs_ctor_k  na p lA_rev I indu llAu ln k lAk nk :=
  let _ := match goal with _ =>  idtac end in let lAk' := constr:(tr_rev lAk) in 
  let rec aux1 k i lAk' acc :=
  lazymatch i with
  | 0 => (* idtac "blut 0" ;*) constr:(acc)
  | S ?i0 => (* idtac "blut 1" ;*) lazymatch eval hnf in lAk' with
   | ?Akiu :: ?tlAk' =>  (* idtac "blut 2" ;*) let pki := constr:(proj_ki p lA_rev I indu k i0 llAu ln Akiu) in let name :=  fresh "proj_" na (* k "_" i0 *) in let _ := match goal with _ =>(** pose (name := pki )*) pose_unquote_term_hnf pki name
    end in let pki_tVar := metacoq_get_value (tmQuote name)  in let acc0 := constr:(pki_tVar :: acc) in (* idtac "blut 3" ;*) let z := aux1 k i0 tlAk' acc0 in constr:(z)
   end 
   | _ => idtac "erroc declare_projs_ctor_k"
  end
  in   let res_dpk := aux1 k nk lAk' (@nil term) in constr:(res_dpk)
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
in (* idtac "loool" ;*) match eval hnf in y with
| (?y0 , ?ln0') => (* idtac "blut 1" ; *)
  match eval cbv in ln0' with
  | (@nil nat) =>  (* idtac "blut 3 0" ; *) constr:(acc) 
  | ?nk :: ?tln0 => (*  idtac "blut 3" ;*)
    match eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k =>  (* idtac "blut 5" ; *)  match eval hnf in lAu' with
        | ?lAk :: ?tlAu'=> 
        let dpk  := declare_projs_ctor_k na p lA_rev I indu llAu ln k  lAk nk in let acc0 := constr:(dpk :: acc ) in let res2 := aux tlAu' tln0 k acc0 in  constr:(res2)
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
Ltac declare_projs0 p lA_rev  I  indu llAunlift  ln nc 
:= 
match goal with _ => let rec aux1 k  i  lAk' acc := 
 let x := constr:((i,lAk'))   in (* idtac "blut 0" ; *)
  lazymatch eval hnf in x with
   | (?i,?lAk') => lazymatch eval hnf in i with
     | 0 => constr:(acc) 
     | S ?i => lazymatch eval hnf in lAk' with
       | ?Akiu :: ?lAk' => let res1 := aux1 k i lAk' constr:(((proj_ki p lA_rev I indu k i llAunlift ln (Akiu)):: acc))in constr:(res1)
       end end
   | _ => idtac "error declare_projs 1"
  end 
in
let rec aux2 llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in  lazymatch eval hnf in y with
| (?y0 , ?ln0') => (* idtac "blut 1" ; *)
  lazymatch eval cbv in ln0' with
  | (@nil nat) =>  (* idtac "blut 3 0" ; *) constr:(acc) 
  | ?i :: ?ln1' => (*  idtac "blut 3" ;*)
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



(* The following two functions bind the arguments of the eliminators : the parameters and the default term *)
(* \TODO : fusionner proj_one_ctor_default_var *)
Definition proj_one_ctor_default_var (I_app : term) (ty_default : term) (indu : inductive) (p : nat) (i : nat) (k : nat)
(ty_arg_constr : list (list term)) (return_type : term) := mkLam ty_default (* lambda truc du type par défaut *)
(mkLam (lift0 1  I_app) (* \TODO intégrer le lift dans le calcul de I_app*)
(mkCase_eliminator_default_var indu p i k ty_arg_constr return_type)).


(* le premier arg est la valeur par défaut, qu'on instancie plus tard, à l'aide CompDec *)
(* disons que :: et on s'intéresse à proj droite *)
(* i : inductif réifié,ici list_nat_reif (doit être un inductif appliqué à un tRel de chaispas*) 
(*       en fait, i est renommé I_app plus tard *)
(* ty_default : list_nat_reif *)
(* I : inductive, cf. constructeur metacoq tCase *)
(* p : 1, car type de base est list *)
(* nbproj (numéro de proj) : 1 (ou 2 ?) *) 
(* k (numéro du constructeur) : 1 (ou 2 ?) *)
(* ty_arg_constr: list (list term) : c'est la liste des types des constructeurs appliqué à des trucs génériques
 (déjà calculée dans interp_alg_type mais aussi calculée avec des trous )
  ty_arg_constr := rev_list_map list_args 
*) 
(* return_type : devrait être la même chose que le type défaut. Est-ce un arg inutile ? 
ou alors return_type est lifté par rapport à ty_default *)

(* let res0 := proj_one_ctor_default_var  *)


(* \!!!!!!!!!!!!! ICI ON SE SERT DU CONTENU DE ty_arg_constr *)
(* Peut-être pour binder tous les paramètres dans l'assert que les constructeurs engendrent tous les habitants ? *)
Definition proj_one_ctor_params_default_var (ty_params : list term) (I_app : term) (ty_default : term) (I : inductive) (p : nat) (i : nat) 
(k : nat) (ty_arg_constr : list (list term)) (return_type : term) :=
let fix aux ty_params acc :=
match ty_params with 
| nil => acc
| x :: xs => aux xs (mkLam x acc)
end in aux ty_params (proj_one_ctor_default_var I_app ty_default I p i k ty_arg_constr return_type).
(* ty_params is probably the revert of the list of the types of 
the parameters *)

(***********************************************************************)
(* \TODO vérifier ?
   Ici se termine la partie où on définit les constructeurs.
   Ensuite, on va construire l'énoncé de génération 
*)


(**  mkOr0 [A1_reif ; ... ; An_reif] produce the reification of An \/ (A_{n-1} ... (A_2 \/ A_1)..)  
     (reverts list and associates to the *right* )
     tail-recursive **)
     Definition mkOr0 (l : list term) := 
   (*  let l' := tr_rev l in  *)
      match l with
      | [] => impossible_term_reif 
      | x0 :: l0 => 
      let fix aux l acc :=
    match l with
    | [] => impossible_term_reif
    | [x] => tApp or_reif (x :: [acc])
    | x :: xs => aux xs (tApp or_reif (x :: [acc]))
    end in aux l0 x0
    end.
    
    (*  mkOr [A1_reif ; ... ; An_reif] produce the reification of (...(An \/ (A_{n-1}) ... A_2) \/ A_1)..)
         (reverts list and associates to the *left*
        not tail-recursive *)
    (* \TODO replace mkOr with mkOr0 by suitably modifying tactics below *)    
    Fixpoint mkOr (l : list term) := 
    match l with
    | nil => impossible_term_reif
    | [ x ] => x
    | cons x xs => tApp or_reif ([mkOr xs] ++ [x])
    end.
    
    (* Goal False. (* \TMP *)
    let x := constr:(mkOr0 [nat_reif; (tRel 0) ; (tRel 3)]) in pose x as mkOr0ex ; compute in mkOr0ex.
    let x := constr:(mkOr [nat_reif; (tRel 0) ; (tRel 3)]) in pose x as mkOrex ; compute in mkOrex.
    Abort. *)
    
    
    


(* map_iter k f [a_0 ; ... ; a_n ] = [f k a_0 ; f (k+1) a_1 ; ... ; f (k+n) a_n]   
*)
(* tail-recursive *) 
 Definition map_iter {A B : Type} (k : nat) (f : nat -> A -> B) (l : list A) :=
  let fix aux k l acc := 
  match l with
  | [] => acc 
  | a :: t => aux (S k) t ((f k a ) :: acc)
  end
  in tr_rev (aux k l []). 


(* Goal False. (* \Q Keep? *)
let x := constr:(map_iter 4 (fun x y => x * x + 2* y ) [1; 2 ; 3 ; 5]) in pose x as kik ;
unfold map_iter in kik ; simpl in kik.  
let x := constr:(map_iter0 4 (fun x y => x * x + 2* y ) [1; 2 ; 3 ; 5]) in pose x as koo ;
unfold map_iter0 in koo ; unfold tr_rev in koo ; simpl in koo.   
Abort. *)
 



Definition args_of_prod_with_length (t : term)  (p : nat) := 
  (* \TODO what args_prod_with_length does is unclear and so is its use*)
  (* unlift the de Bruijn indexes of the types of the constructors such as we have got the from ???? *)
  (* the reason is \TODO *)
  (* manifestement, t ne compte pas, sauf les Prod prénexes *)
let fix aux t acc n :=
match t with 
| tProd _ Ty v => aux v (Ty :: acc ) (S n)
| _ => (acc, n - p)
end
in
let res0 := aux t [] 0 in
(map_iter 0 unlift (skipn p (tr_rev (fst res0))), snd res0). 
(* \TODO pê problème de unlift, car on doit relifter après *)

Check args_of_prod_with_length.
Check unlift.

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


(* \TODO vérifier la spec *) (* \TODO probablement déjà fait dans interp_alg_typ *)
(* get_args_list_with_lengths [t_1 ; ... ; t_k ] n =
   [args_of_prod_with_length t_k n ; .... ; args_of_prod_with_length t_1 n] *)
Definition get_args_list_with_length (l : list term) (p : nat):=
let fix aux l acc := 
match l with 
| [] => acc
| x :: xs => let x' := args_of_prod_with_length x p in aux xs (x' :: acc)
end
in tr_rev (aux l []). 
(* 
Goal False.
let x := constr:(get_args_list_with_length (tProd (mkNamed "x") (tRel 1) (tProd (mkNamed "x") (tRel 52) ( tProd (mkNamed "x") (tRel 100) (tProd  (mkNamed "x") (tRel 9)
(tApp list_reif  [nat_reif ; tRel 3 ; tRel 5 ; tRel 8 ; tRel 13 ; tRel 21]) ))) ) 0 ) in pose x as galenex ; unfold get_args_list_with_length in galenex ;
unfold args_of_prod_with_length in galenex  ; unfold skipn in galenex ; unfold map_iter in galenex ; simpl in galenex.
Abort.  *)



(* rev_list_map [ l1 ; ... ; lk ] = [ rev l1 ; rev l2 ; ... ; rev lk ]
   linear 
*)
Definition rev_list_map {A} (l : list (list A)) := @tr_map (list A) (list A) (@tr_rev A) l.
(* \TODO voir si on ne peut pas se débarrasser de rev_list_map: une liste de listes probablement mal construite.
Sa seule utilisation dans le code est effectif est dans get_one_eliminator_return sur list_args. Ainsi, la 1ère version de list_args doit être mal construite. Cf. pê le tr_rev ajouté sur une des fonctions plus haut (laquelle ? get_args_list_with_length ?)
*)

(* total_arg_ctors [ (l1 , n1) ; ... ; (lk ; nk)] = 
   n1 + ... + nk *)
Definition total_arg_ctors (l : list (list term × nat)) := 
let fix aux l n :=
match l with
| [] => n
| x :: xs => aux xs (snd x + n)
end
in aux l 0.
Check total_arg_ctors.
(* \TODO total_arg_ctors n'est utilisé que dans Ltac get_eliminators_st_return sur list_args_len. Une info est sans doute calculée deux fois. 
On peut s'en doute s'en débarrasser 
*)

(* \TODO : trouver meilleur nom *)
(* \TODO : pre_bind_all_for_proj [[A_{0,0} ; ... ; A_{0,l_0-1}] ; ... ; [A_{k,0} ; .... ; A_{k,l_k-1}] ]
                                  [l0 ; ... ; lk ]
    = [ A_{k,l_k}^L ; ... ; A_{0,1}^{+1} ; A_{0,0}^0 ]
      where L = l_0 + ... + l_k
      Thus, pre_bind_all_for_proj performs a flattening, a revert and a incremental lift of all the elements of the initial list of lists
    *)
(* \TODO peut-être conserver les accumulateurs l0, l0+l1, l0+l1+l2, ou alors les calculer séparément et faire 
l'incrémentation à partir de la liste lnacc *)
Definition pre_bind_all_for_proj (llAunlift : list (list term)) (ln : list nat) :=
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


  (* same as pre_bind_all_for_proj, but performs products
  currently, binds in the reverse order : function should probably be discarded *)
  Definition pre_bind_all_for_proj0 (t: term) (llAunlift : list (list term)) (ln : list nat) :=
    let fix aux1  acc i (lA : list term) : term  := 
    match lA with
    | [] => acc  
    | A0 :: lA => aux1 (mkProd (lift0 i A0)  acc) (S i) lA
    end 
    in let fix aux2 acc  a1 a2 llA ln :=
    match (llA,ln) with
    | ([],[]) => acc 
    | (lA :: llA, na :: ln)  => let a1'  :=  na + a1 in  aux2 (aux1 acc  a1 lA )  a1' na  llA ln
    | _ => impossible_term_reif (* this cases does not happen: ln and llAunflit have the same length *)
    end 
    in  aux2 t 0 0  llAunlift ln.


Goal False.
let x := constr:(pre_bind_all_for_proj [[tRel 0 ] ; [tRel 0 ; tApp list_reif [tRel 0] ; tApp list_reif [tRel 0]]; [tRel 0 ; tApp nat_reif [tRel 1]]  ] [1 ; 3 ; 2]) in pose x as kik ; compute in kik.
let x := constr:(pre_bind_all_for_proj0 S_reif [[tRel 0 ] ; [tRel 0 ; tApp list_reif [tRel 0] ; tApp list_reif [tRel 0]]; [tRel 0 ; tApp nat_reif [tRel 1]]  ] [1 ; 3 ; 2]) in pose x as koo ; compute in koo.
Abort.


(* lift_rec_rev [A0; ...; An] = [lift0 n An ; .... ; lift1 1 A1 ; lift0 0 A0] *)
(* tail-recursive *)
Definition lift_rec_rev (l : list term) :=
let fix aux l acc n :=
match l with
| [] => acc
| x :: xs => aux xs ((lift0 n  x) :: acc) (n + 1) 
end
in aux l [] 0.
(* \TODO n'est utilisée que dans get_eliminators_st_return 
    pas clair pourquoi on a besoin de retourner la liste 
    \TODO apparemment, bcp de listes sont calculées à l'envers. Voir si on ne peut pas optimiser l'utilisation de rev
*)



(* holes_n n = [hole ; ... ; hole] (n occurrences)
   linear *)
   Definition holes_n (n : nat) :=
    let fix aux n acc := 
    match n with
    | 0 => acc 
    | S n => aux n (hole :: acc)
  end in aux n [].
  
  (* holes_n n = [hole ; ... ; hole ; tRel db ; tRel 0] with n holes 
      \TODO useful to pass the parameters to the projections,
      cf. ??? and ??? *)
  Definition holes_n' (n : nat) (db : nat) :=
    let fix aux n acc := 
    match n with
    | 0 => acc 
    | S n => aux n (hole :: acc)
  end in aux n [tRel db; tRel 0].

(* gets each elimination function applied to the parameters, the default and the term *)
(* get_elim_applied [(p0 , d0 ); ... ; (pn , dn)] [A1 ; ... ; Ak ]
     = [ tApp p0 [ A1 ; ... ; Ak ; tRel d0 ; tRel0 ] 
     ; ... ; tApp pn [A1 ; ... ; An ; tRel dn ; tRel 0]]*)
Fixpoint get_elim_applied (list_tVar : list (term * nat)) (lpars : list term) :=
match list_tVar with
| nil => nil
| (elim, db) :: xs => (tApp elim (holes_n' (length lpars) db)):: get_elim_applied xs lpars
end.
(* \TODO comprendre pq ici le default est Rel 0 et pas Rel 1, ou alors c'est tRel db ?  *)
(* n'est utilisée que dans get_eliminators_one_ctor_return_aux sur list_elims *)
Check get_elim_applied. 

(* get_eq_x_ctor_proj p ctor [p_0, ..., p_{k-1}] db  
   is the reification of the equality "tRel 0" = ctor (p0 [ _p ; tRel db  ; tRel 0] ; 
     [ _p : tRel (db -1) ; tRel 0] ; ... ; [ _p ; tRel (db-k+1) ; tRel 0] ]
   where p is the number of parameters of the inductive
   p_0,...., p_k are supposed to be the reified projections of the reified constructor ctor, k is the number of argument of this constructor (withstanding parameters) and _p is a sequence of p holes
   That is, intuitively, the ouput represents an equality of the form x = ctor (proj_0 x) ... (proj_k) x, where x is tRel 0
  tail-recursive 
   *)
  Definition get_eq_x_ctor_proj (p: nat) (ctor : term) (projs : list term)  (db: nat) :=  
(* \tTODO see it one needs to give the parameters: probably not *)  
let fix aux lprojs i  acc :=
   match (lprojs,i) with
   | ([],_) => acc 
   | (pki :: lprojs, S i) => aux lprojs i ((tApp pki (holes_n' p i))::acc)
   | _ => [] (* this case does not happen *)
  end in 
  mkEq hole (tRel 0) (tApp ctor (rev_append (holes_n p) (tr_rev (aux projs (S db) [])))).



(* \TMP *)
Goal false.
clear.
let x := constr:(get_eq_x_ctor_proj 3 (S_reif) [tRel 0; tRel 25; tRel 49] 
8) in pose x as gexcpex ; compute in gexcpex.
Abort.


(* \todo check that the db are computed somewhere *)
(* \todo, here, one rather needs a revert mkOr *)
(* \todo see if this needs to be reverted later*)
(* get_generation_disjunction p ctors list_proj ldb 
   outputs the reification of forall x : I, 
   x = C0 (projs0 x) \/ .... \/ x = Ck (projsk x)
   where lctors is the list of the (reified) constructors of an inductive, list_proj is the list of lists of their projections  (which are computed by the tactic declare_projs)
  x = Ck (projsk x) is a shortening of x = Ck (proj_{k,0} d_{k,0} x) .... (proj_{k,nk-1} d_{k,nk-1} x) and d_{k,i} the default value for d_{k,i} (x = Ck (projsk x) is computed with get_eq_x_ctor_proj)
   ldb is the list of De Bruijn indices of ????
   L is the total number of the arguments of all constructors (withstanding type parameters )
   Note that mkProd tApp I (get_list_of_rel_lifted L p) _
   is forall x : I A1 ... Ap, _
   *)
(* \TODO remove ldb argument *)


 Definition get_generation_disjunction  (p : nat) (I: term) (L : nat) (lc : list term) (list_proj : list (list term)) (ln : list nat) :=
  let fix aux lc list_proj lN acc := 
  match (lc,list_proj,lN) with
  | ([],[],[]) => acc
  | (ctor :: tlc , projs :: tl_proj, db :: tlN ) => aux tlc tl_proj tlN  ((get_eq_x_ctor_proj p ctor projs db) :: acc)
  | _ => [] (* this cases does not happen *)
 end in let lN := rev_acc_add (tr_rev ln)   (* perhaps some optimization there *) 
 in tProd (mkNamed "x") (tApp I (get_list_of_rel_lifted p L)) (mkOr (aux lc list_proj lN [])) .

 

Goal False.
let x:= constr:(get_generation_disjunction 3 nat_reif  100 [S_reif ; O_reif ; O_reif ]
  [[tRel 13 ; tRel 15 ; tRel 8] ; [tRel 33 ; tRel 45] ; [tRel 60 ; tRel 70 ; tRel 72]] [3 ; 2 ; 3]) in pose x as ggdex ; compute in ggdex.  clear.
  Abort.


(* \todo: coupler avec pre_bind_all_for_proj *)
(* \todo : gérer la liste des db, qui est 
[[L; ... ; lk + ... + l2 +1 ] ; ....; [lk + l_{k-1}  ....; lk+2 ; lk+1 ] ;[ lk ...; 2 ; 1]]
*)



(** args_of_projs_in_disj [ n1 ; .... ; nk ] = [[tRel L ; tRel L-1 ; ....; tRel (L-n1+1) ] ; ... ; [tRel nk ; ... ; tRel 1]  ] 
    where L = n1 + ... + n1
    i.e. the sublists have respective lengths ni and the de Bruijn index decreases at each step
    args_of_projs_in_disj [1 ; 3 ; 2 ] = [ [tRel 6 ] ; [tRel 5 ; tRel 4 ; tRel 3] ; [tRel 2 ; Rel 1]]
    This function helps specify the Db index of the default variable of each projection in the big disjunction
    **)
(* \Q : do we need this function ? *)
Definition args_of_projs_in_disj (ln : list nat) : list (list term) :=
  let ln_rev := tr_rev ln in
  let fix aux l0 acc res :=
  match l0 with
  | [] => res
  | n :: l0 =>  aux l0 (n + acc) ((get_list_of_rel_lifted n acc) :: res)
  end in aux ln_rev 1 [].

Goal False.
let x := constr:(args_of_projs_in_disj [3 ; 8 ; 2]) in pose x as kik ; compute in kik.
Abort.
(* maintenant, on doit collecter les constructeurs *)


(* get_list_ctors_tConstruct_applied I k n := [tApp C0 holes_n ; ... ; tApp Ck holes_n ]
  where C0, ..., Ck are the constructors of I
  k should be the number of ctors of I
  n the number of parameters of I
*)
(* linear *)
Definition get_list_ctors_tConstruct_applied (I : term) (n : nat) (p : nat) :=
let l := holes_n p in
match I with
| tInd indu inst => let fix aux n acc  := match n with
          | 0 => acc
          | S m => aux m ((tApp (tConstruct indu m inst) l) :: acc )
          end in aux n []
| _ => []
end.
(* \TODO : remove tApp when n = 0 *)



(* \TMP, ici, on calcule un projecteur cf. def de elim ci-dessous *)
Ltac get_one_eliminator_return I ty_pars I_app ty_default I_indu p i k list_args return_ty nb_args_previous_construct total_args :=
  (* trackons les 9è (-4è) et 10è (-3è) arg, i.e. lists_args et return_type *)
let p := eval compute in (proj_one_ctor_params_default_var ty_pars I_app ty_default I_indu p i (k - 1) (rev_list_map list_args) return_ty) in
(* ici, l'avant-dernier param de proj_one_ctor_params_default_var est 
   (rev_list_map list_args). Ainsi, *)
let u := metacoq_get_value (tmUnquote p) in 
let x := eval compute in u.(my_projT2) in
let name := fresh "proj_" I  in let _ := match goal with _ => (*\Q pourquoi ce match goal with ici et pas plus haut? *)
pose (name := x) end in
let elim := metacoq_get_value (tmQuote name) in 
let db := eval compute in (total_args + 1 - nb_args_previous_construct - i) in
constr:((elim, db)).







(*  mkLam I_app (lift0 1  ty_default) seems to compute a return type. Of what ? *)
(*  -> ty_default   *)
(* \TMP *)
Ltac get_def_ret_ty n I ty_pars I_app I_indu p k list_args nb_args_previous_construct total_args lpars c_reif list_elims :=
match n with
| S ?n' =>  let ty_default := eval compute in (nth n' (nth (k -1) list_args nil ) impossible_term_reif) 
in 
            let return_ty := eval compute in (lift0 2 (mkLam I_app (lift0 1  ty_default))) in constr:((ty_default,return_ty))
            end.

(* \TODO chercher get_equality *)

(* Definition get_eq (c : term) (t : term) (l : list term) := 
 tApp eq_reif [hole ; t ; tApp c  l].*) (*\Q pourquoi échange d'ordre entre c et t ?*) 

 (* \TODO get_elim_applied semble calculer le décalage total de dB quand on construit l'énorme disjonction. Noter que list_elims : list (term x nat) est le dernier arg de get_eliminators_one_ctor_return_aux, qui est construit progressivement  () *)
Ltac get_eliminators_one_ctor_return_aux n I ty_pars I_app I_indu p k list_args nb_args_previous_construct total_args lpars c_reif list_elims :=
match n with
| 0 => let elim_app := eval compute in (get_elim_applied list_elims lpars) in
       let get_equ := constr:(tApp eq_reif [hole ; (tRel 0) ; tApp c_reif elim_app ])
       in get_equ
| S ?n' =>  let ty_default := eval compute in (nth n' (nth (k -1) list_args nil ) impossible_term_reif) 
in 
            let return_ty := eval compute in (lift0 2 (mkLam I_app (lift0 1  ty_default)))
(* différence entre ty_default et return_ty: faire control F *)
 in (* idtac ty_default ;*) 
(*  idtac "kikooo"  return_ty ; *)
(*let k1 := fresh "kikoooootydef" in pose ty_default as k1  ; *)
(* let l2 := fresh "kikoooreturnty" in pose return_ty as k2  ; *)
            let x := get_one_eliminator_return I ty_pars I_app ty_default I_indu p n k list_args return_ty nb_args_previous_construct total_args in 
    (* list_args devient le 8ème  arg de    get_eliminators_one_ctor_return_aux  *)   
     get_eliminators_one_ctor_return_aux n' I ty_pars I_app I_indu p k list_args nb_args_previous_construct total_args lpars c_reif  (x :: list_elims)
end.


(* Doit donner une égalité du type 
(x = (Ci (proj_{0,i} x) ... (proj_{l_i-1,i} x))
*)
Ltac get_eliminators_one_ctor_return n I ty_pars I_app I_indu p k list_args0 nb_args_previous_construct total_args lpars c_reif :=
let list_args := eval compute in (split (list_args0)).1 in (* \Q pourquoi list_args calculé plusieurs fois ?
la même chose est faite dans la fonction finale get_eliminators_st_return
dans laquelle list_args0 s'appelle list_args_len....
*)
(* maintenant, list_args := val compute in (split (list_args0)).1  
   et list_args0 est le 8è param de get_eliminators_one_ctor_return
*)
get_eliminators_one_ctor_return_aux n I ty_pars I_app I_indu p k list_args nb_args_previous_construct total_args lpars c_reif (@nil (term*nat)).


(* \TODO spec 
probably gets the disjunction saying that 
forall A1.... Ap (v0 : A_{0,0}) ... (v_{l_{k-1},k-1} : A_{l_{k-1},k-1}) (x : I A1 ... A p), 
(x = (C0 (proj_{0,0} A1 ... Ap v_{0,0} x) ... (proj_{l_0-1,0} x)) 
\/ ... \/  (x = (Ci (proj_{0,i} x) ... (proj_{l_i-1,i} x)) 
\/ ... \/ (x = (C_{k-1} (proj_{0,k-1} x) ... (proj_{l_{k-1}-1,k} x)) 
*)
Ltac get_eliminators_aux_st n I ty_pars I_app I_indu p list_args total_args lpars list_ctors_reif nb list_eq :=
match n with
| 0 => constr:(list_eq)
| S ?n' => let prod := eval compute in (nth n' list_args (nil, 0)) in
           let i := eval compute in (prod.2) in 
           let c_reif := eval compute in (nth n' list_ctors_reif impossible_term_reif) in
           let nb_args_previous_construct := eval compute in (nb - i) in
          let x :=
          get_eliminators_one_ctor_return i I ty_pars I_app I_indu p n list_args nb_args_previous_construct total_args lpars c_reif in
 (* ici, le 8ème arg de get_eliminators_one_ctor_return s'appelle list_args et non list_args0.
 c'est aussi le 7ème arg de get_eliminators_aux_st, qui s'appelle list_args
*) 
          get_eliminators_aux_st n' I ty_pars I_app I_indu p list_args total_args lpars list_ctors_reif nb_args_previous_construct constr:(x::list_eq)
end.

Ltac prove_by_destruct_varn n  := 
match n with 
| 0 =>
let x := fresh in 
intro x ; destruct x; repeat first [first [reflexivity | right ; reflexivity] | left]
| S ?m => let y := fresh in intro y ; prove_by_destruct_varn m 
end.

(* Main tactic : from an inductive not applied, generates the generation statement and a projection function for each non dependent argument of each constructor *)
Ltac get_eliminators_st_return I_rec na := 
let I_rec_term := eval compute in (I_rec.2) in
let opt := eval compute in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?p, ?ty_pars) =>
  let list_ty := eval compute in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval compute in (get_args_list_with_length list_ty p) in 
  let list_args := eval compute in (split list_args_len).1 in 
  let list_ty_default0 := eval compute in (tr_flatten list_args) in
  let list_ty_default := eval compute in (lift_rec_rev list_ty_default0) in 
  let k := eval compute in (Datatypes.length list_args) in
  let list_ctors_reif := eval compute in (get_list_ctors_tConstruct_applied I_rec_term k p) in 
  let total_args := eval compute in (total_arg_ctors list_args_len) 
  in
  (* idtac total_args *)
 (*   \Q pq idtac total_args fait planter le prog ? *) 
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted p (S total_args))) in
  let I_app := eval compute in (get_indu_app_to_params I_rec_term p) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st k na ty_pars I_app I_indu p list_args_len total_args list_of_pars_rel list_ctors_reif total_args (@nil term) in 
(* le 7ème arg de get_eliminators_aux_st est list_args_len, que l'on obtient dans get_info *)
                      let t := eval compute in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
let nb_intros := eval compute in (p + total_args) in 
 assert (Helim : u') by (prove_by_destruct_varn nb_intros)
 end in Helim
        | _ => fail
| None => fail
end
end.



(* \TODO move up the definition of nat_oind. In utilities.v? *)
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

Print Ltac pose_blut.
(* pv new verion*)
Print mutual_inductive_body.




Ltac get_my_bluts t na := 
  let indmind := fresh "indmind" in pose_blut t indmind ; 
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
        | (?lB,?lc) =>    let llAtrunc := eval compute in (tr_map (skipn p) llA) in  let nc := eval compute in (List.length ln) in let info_uple :=
        constr:(((((((((llAtrunc,lB),lc),llA),ln),lA),p),nc)))  in 
        (* let x := constr:(proj_return_types llAtrunc) in pose x as llAunlift  ; *)
        let lA_rev := eval compute in (tr_rev lA) in let llAu := eval compute in (tr_map ret_ty_proj llAtrunc) in let t_reif := constr:(tInd indu u) in  let L := constr:(fold_left Nat.add ln 0) in
        let res3 := 
         declare_projs na p lA_rev t_reif indu llAu ln nc in let llprojs := fresh "llprojs" in 
        let _ := match goal with _ => pose (llprojs  := res3)  (* pose res3 as kik*) (*  pose t as na  *) end in
        let ltypes_forall := constr:(pre_bind_all_for_proj llAu ln) in 
        let ggd := constr:(mkProd_rec lA_rev (mkProd_rec ltypes_forall (get_generation_disjunction  p t_reif L  lc  llprojs  ln)))  in  
         let gent := fresh "gen" t in pose_unquote_term_hnf ggd gent  ;  let L' := eval compute in (p + L) in  let Helim := fresh "pr_gen_" t in assert (Helim : gent) by  prove_by_destruct_varn 3 ;
       clear indmind  
        end
      end
    end
    end
  end end end
  .       
   
  Print get_generation_disjunction.


  Goal False.
  let indmind := fresh "indmind" in pose_blut list indmind. clear.
  idtac "RESEEEET".
   get_my_bluts list ik. 
    
clear.



  (*  let x := get_my_bluts list ik in pose x as kikoo.*)
  Abort.





 
Ltac get_eliminators_st_return_quote I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_eliminators_st_return I_rec I.



Ltac get_eliminators_st I :=
let st := get_eliminators_st_return_quote I in idtac.


Section tests_eliminator.

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
Fail get_blut nat ds.
get_eliminators_st list. clear.
get_eliminators_st nat. clear.
get_eliminators_st @nelist. clear.
get_eliminators_st @biclist. clear.
get_eliminators_st Ind_test. clear.
get_eliminators_st Ind_test2. clear.
Abort.


End tests_eliminator.

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

Ltac get_eliminators_st_default I t0 :=
let t := eval compute in t0 in 
let H' := get_eliminators_st_return I in
instantiate_tuple_terms_inhab H' t t.

Ltac get_eliminators_st_default_quote I t0 :=
let t := eval compute in t0 in 
let H' := get_eliminators_st_return_quote I in
instantiate_tuple_terms_inhab H' t t.

Section tests_default.

Variable A : Type.
Variable a : A.

Goal nat -> A -> False.
let t0 := return_tuple_subterms_of_type_type in 
get_eliminators_st_default_quote list t0. clear -a.
let t0 := return_tuple_subterms_of_type_type in 
get_eliminators_st_default_quote Ind_test t0. clear -a.
let t0 := return_tuple_subterms_of_type_type in 
get_eliminators_st_default_quote Ind_test2 t0. clear -a.
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
                 try (get_eliminators_st_default_quote I t) ; elims_on_list xs t
end.

Ltac get_eliminators_in_goal := 
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

Ltac get_eliminators_in_variables p := 
let t := vars in 
let rec tac_rec v tuple :=
match v with
| (?v1, ?t') => let T := type of v1 in first [ let U := type of T in constr_eq U Prop ; tac_rec t' tuple |
                let I := get_head T in 
                let params := get_tail T in 
                try (is_not_in_tuple tuple T  ;
                get_eliminators_st_default_quote I params) ; try (tac_rec t' (tuple, T)) ]
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
   
Proof. intros. get_eliminators_in_variables bool.
Abort.

End tests.
