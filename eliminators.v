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


(* \TODO éliminer la variable return_type, qui est probablement un lift de default_type *)

Ltac find_inhabitant_context t := 
first[ constructor ; assumption | apply Inh | epose (inhab := ?[t_evar] : t)]. 

Ltac find_inh t :=
match goal with
| H : t |- _ => H
| _ => let H := fresh in let _ := match goal with _ => assert (H : t) by find_inhabitant_context t end in H
end.

Definition codomain_nbconstruct (list_ty_construct : list (list term)) (nbconstruct : nat) (nbproj : nat) := 
 nth nbproj (nth nbconstruct list_ty_construct nil) impossible_term_reif. 


Definition get_return_type_nbconstruct (indu_app_to_params : term) (codomain : term) :=
  mkLam  indu_app_to_params (lift 1 0 codomain).
  
(* get_return_type
 indu_app_to_params codomain. *)


Definition get_proj (n : nat) (l_ty : list term) := 
let k := Datatypes.length l_ty in 
let fix aux l t :=
match l with 
| nil => t
| x :: xs => aux xs (mkLam x t) 
end in aux l_ty (tRel (k - n)).

(* Shift De Brujin indexes: useful when variables are removed *)
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
Definition branch_default_var (l0 : list term) (nbproj : nat) (nbconstruct : nat) (n : nat) :=
let len := Datatypes.length l0 in 
let l := List.map (lift (len + 1) 0) l0 in (* \Q is l0 useful ???? apparently l0 is supposed to be the list of the types of the params *)
if Nat.eqb n nbconstruct then 
let fix aux l acc :=
match l with 
| [] => acc 
| y :: ys => aux ys (mkLam hole acc)
end
in aux l (tRel (len - nbproj))
else
let fix aux' l acc := match l with 
      | [] => acc
      | y :: ys =>  aux' ys (mkLam hole (lift 1 0 acc)) 
      end
in aux' l (tRel 1).  (* tRel 1 will be the parameter for the default value *)
    (* note that tRel 1 is not bound in the above function *)


(* Constructs the pattern matching in the eliminator
for instance, given the right arguments to construct the predecessor function we get the reified
< match x with
| 0 => default
| S y => y > *)
Definition mkCase_eliminator_default_var (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) := 
let fix aux (I : inductive) (npars: nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) (acc: list (nat × term)) (acc_nat : nat) :=
match ty_arg_constr with 
| [] => tCase (I, npars, Relevant) return_type (tRel 0) (List.rev acc)
| x :: xs => aux I npars nbproj nbconstruct xs return_type 
((acc_nat, branch_default_var x nbproj nbconstruct acc_nat)::acc) (acc_nat + 1)
end
in aux I npars nbproj nbconstruct ty_arg_constr return_type [] 0.
(* construit le match de l'éliminateur et le default variable non-liée tRel 1 *)


(* The following two functions bind the arguments of the eliminators : the parameters and the default term *)
Definition proj_one_constructor_default_var (i : term) (ty_default : term) (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) := mkLam ty_default (* lambda truc du type par défaut *)
(mkLam (lift 1 0 i)  (* lambda de l'inductif appliqué *)
(mkCase_eliminator_default_var I npars nbproj nbconstruct ty_arg_constr return_type)).

(* TODO c'est cette fonction dont on a besoin *)
Goal False.

(* ainsi, le premier arg est la valeur par défaut, qu'on instancie plus tard, à l'aide CompDec *)

(* disons que :: et on s'intéresse à proj droite *)
(* i : inductif réifié,ici list_nat_reif (doit être un inductif appliqué à un tRel de chaispas*) 
(*       en fait, i est renommé I_app plus tard *)
(* ty_default : list_nat_reif *)
(* I : inductive, cf. constructeur metacoq tCase *)
(* npars : 1, car type de base est list *)
(* nbproj (numéro de proj) : 1 (ou 2 ?) *) 
(* nbconstruct (numéro du constructeur) : 1 (ou 2 ?) *)
(* ty_arg_constr: list (list term) : c'est la liste des types des constructeurs appliqué à des trucs génériques
 (déjà calculée dans interp_alg_type mais aussi calculée avec des trous )
  ty_arg_constr := rev_list_map list_args 
*) 
(* return_type : devrait être la même chose que le type défaut. Est-ce un arg inutile ? 
ou alors return_type est lifté par rapport à ty_default *)

(* let p := proj_one_constructor_default_var  *)

Abort.


Definition proj_one_constructor_params_default_var (ty_params : list term) (i : term) (ty_default : term) (I : inductive) (npars : nat) (nbproj : nat) 
(nbconstruct : nat) (ty_arg_constr : list (list term)) (return_type : term) :=
let fix aux ty_params acc :=
match ty_params with 
| nil => acc
| x :: xs => aux xs (mkLam x acc)
end in aux ty_params (proj_one_constructor_default_var i ty_default I npars nbproj nbconstruct ty_arg_constr return_type).

Fixpoint remove_n {A} (n : nat) (l : list A) := 
match n with 
| 0 => l 
| S n' => match l with
        | nil => nil
        | cons x xs => remove_n n' xs
        end
end.

Fixpoint map_iter {A B : Type} (k : nat) (f : nat -> A -> B) (l : list A) :=
  match l with
  | [] => []
  | a :: t => f k a :: map_iter (k + 1) f t
  end.

Definition args_of_prod (t : term)  (npars : nat) := 
let fix aux t acc :=
match t with 
| tProd _ Ty v => aux v (acc ++ [Ty])
| _ => acc 
end
in map_iter 0 unlift (remove_n npars (aux t [])). 
(* warning: handles parameters but not dependent arguments *)

Definition get_args_list (l : list term) (npars : nat) : list (list term) :=
let fix aux l acc := 
match l with 
| nil => acc
| cons x xs => let x' := args_of_prod x npars in aux xs (x' :: acc)
end
in aux l [].

Definition args_of_prod_with_length (t : term)  (npars : nat) := 
let fix aux t acc n :=
match t with 
| tProd _ Ty v => aux v (acc ++ [Ty]) (S n)
| _ => (acc, n - npars)
end
in
let p := aux t [] 0 in
(map_iter 0 unlift (remove_n npars (fst p)), snd p). 



(* warning: handles parameters but not dependent arguments *)

Definition get_args_list_with_length (l : list term) (npars : nat):=
let fix aux l acc := 
match l with 
| nil => acc
| cons x xs => let x' := args_of_prod_with_length x npars in aux xs (x' :: acc)
end
in aux l [].

Definition get_list_args (I_rec : global_env* term) (npars : nat) := rev (get_args_list (list_types_of_each_constructor I_rec) npars).

Definition get_list_args_with_length (I_rec : global_env* term) (npars : nat) := rev (get_args_list_with_length (list_types_of_each_constructor I_rec) npars).

Fixpoint get_indu_app_to_params (t : term) (n : nat) := 
match n with 
| 0 => t
| S n' => get_indu_app_to_params (tApp t [tRel n']) n'
end.

Definition rev_list_map {A} (l : list (list A)) := @List.map (list A) (list A) (@rev A) l.

Definition total_arg_constructors (l : list (list term × nat)) := 
let fix aux l n :=
match l with
| [] => n
| x :: xs => aux xs (snd x + n)
end
in aux l 0.

Fixpoint mkProd_rec (l : list term) (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} x t)
end.

Definition lift_rec_rev (l : list term) :=
let fix aux l acc n :=
match l with
| [] => acc
| x :: xs => aux xs ((lift n 0 x) :: acc) (n + 1) 
end
in aux l [] 0.

(* gets each elimination function applied to the parameters, the default and the term *)
Fixpoint get_elim_applied (list_tVar : list (term * nat)) (lpars : list term) :=
match list_tVar with
| nil => nil
| (elim, db) :: xs => (tApp elim (lpars ++ [tRel db; tRel 0])) :: get_elim_applied xs lpars
end.

Fixpoint get_equality (c : term) (t : term) (l : list term) := 
match l with
| [] => tApp eq_reif [hole; t; c]
| x :: xs => get_equality (tApp c [x]) t xs
end.

Fixpoint get_list_of_hole (n : nat) :=
match n with
| 0 => nil
| S m  => hole :: get_list_of_hole m
end.

Definition get_list_ctors_tConstruct_applied (I : term) (n : nat) (npars: nat) :=
let l := get_list_of_hole npars in
match I with
| tInd indu inst => let fix aux n := match n with
          | 0 => nil
          | S m => (aux m) ++ [tApp (tConstruct indu m inst) l]
          end in aux n
| _ => []
end.

Fixpoint mkOr (l : list term) := 
match l with
| nil => impossible_term_reif
| [ x ] => x
| cons x xs => tApp or_reif ([mkOr xs] ++ [x])
end.

Ltac get_one_eliminator_return I ty_pars I_app ty_default I_indu npars nbproj nbconstruct list_args return_ty nb_args_previous_construct total_args :=
  (* trackons les 9è (-4è) et 10è (-3è) arg, i.e. lists_args et return_type *)

let p := eval cbv in (proj_one_constructor_params_default_var ty_pars I_app ty_default I_indu npars nbproj (nbconstruct - 1) (rev_list_map list_args) return_ty) in
(* ici, l'avant-dernier param de proj_one_constructor_params_default_var est 
   (rev_list_map list_args). Ainsi, *)
let u := metacoq_get_value (tmUnquote p) in 
let x := eval cbv in u.(my_projT2) in
let name := fresh "proj_" I  in let _ := match goal with _ =>
pose (name := x) end in
let elim := metacoq_get_value (tmQuote name) in 
let db := eval cbv in (total_args + 1 - nb_args_previous_construct - nbproj) in
constr:((elim, db)).

(***********************************)

(***** tests Pierre        *********)

(***********************************)

(* nbproj : numéro de la projection *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, nbproj est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)
(* ty_default *)

Ltac get_list_args_len I_rec na :=
  let I_rec_term := eval cbv in (I_rec.2) in
  let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars))
  in pose list_args_len as na
end.

Ltac get_list_args_len_quote I na:=  
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_list_args_len I_rec  na ; compute in na.

Goal False. (* debunking ty_arg_constr from list_args_len *)
get_list_args_len_quote list list_lal.
let x := constr:(split list_lal) in pose x as blut . 
compute in blut.
let x:= constr:(blut.1) in pose x as truc. compute in truc.
Print rev_list_map.
let x:= constr:(rev_list_map truc) in pose x as bid.
compute in bid.
Abort.


Ltac get_ty_arg_constr I_rec na := let lal := fresh "lal" in
 get_list_args_len_quote I_rec   lal ; 
  let x := constr:(rev_list_map ((split lal).1)) in pose x as na;
 compute in na ; clear lal. 

Goal False.
get_list_args_len_quote list list_lal.
get_ty_arg_constr list list_tarc.
Abort.

(* list_args := val cbv in (split (list_args0)).1   *)

Ltac get_ty_arg_constr_quote I na:=  
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_ty_arg_constr  I_rec  na.



Ltac get_info0 I_rec na := (* \TODO remove *)
  let I_rec_term := eval cbv in (I_rec.2) in
  let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars)) in 
  let list_args := eval cbv in (split list_args_len).1 in 
  pose list_args as na end .


Ltac get_info0_quote I na := (* \TODO remove *)
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_info0 I_rec  na ; compute in na.



Ltac get_info I_rec na :=
  let I_rec_term := eval cbv in (I_rec.2) in
  let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars)) in 
  let list_args := eval cbv in (split list_args_len).1 in 
let list_ty_default0 := eval cbv in (flatten list_args) in
  let list_ty_default := eval cbv in (lift_rec_rev list_ty_default0) in 
  let nbconstruct := eval cbv in (Datatypes.length list_args) in
  let list_constructors_reif := eval cbv in (get_list_ctors_tConstruct_applied I_rec_term nbconstruct npars) in 
  let total_args := eval cbv in (total_arg_constructors list_args_len) in
  let list_of_pars_rel := eval cbv in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval cbv in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
  let x := constr:((((((((npars,ty_pars),list_ty),
list_args),total_args),list_of_pars_rel),I_app),I_indu)) 
  in pose x as na 
end  
end.


Ltac get_info_quote I na := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_info I_rec  na ; compute in na.

 
(* list_of_pars_rel is also called lpars *)
 


Ltac get_info2 I_rec na :=
  let I_rec_term := eval cbv in (I_rec.2) in
  let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars)) in 
  let list_args := eval cbv in (split list_args_len).1 in 
let list_ty_default0 := eval cbv in (flatten list_args) in
  let list_ty_default := eval cbv in (lift_rec_rev list_ty_default0) in 
  let nbconstruct := eval cbv in (Datatypes.length list_args) in
  let list_ctors_reif := eval cbv in (get_list_ctors_tConstruct_applied I_rec_term nbconstruct npars) in 
  let total_args := eval cbv in (total_arg_constructors list_args_len) in
  let list_of_pars_rel := eval cbv in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval cbv in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
  let x := constr:(((((((list_args_len,list_args),list_ty_default0),list_ty_default),nbconstruct),list_ctors_reif),list_of_pars_rel))
  in pose x as na 
end  
end.

Ltac get_info2_quote I na := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_info2 I_rec  na; compute in na.






Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).


Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tInd ?indu ?u =>  pose (indu,u) as idn  ; clear tq
     end.



Goal 2 +  2 = 5.
Proof.
pose (2,3) as x. pose x.1 as y. Eval compute in y.
let list_info := fresh "list_info" in get_info_quote list list_info. 
pose list_info.2 as list_indu. compute in list_indu. (* \Q pq ça ne calcule pas ? *)
pose list_info.1.2 as list_I_app. compute in list_I_app.
pose list_info.1.1.2 as list_lpars. compute in list_lpars.
pose list_info.1.1.1.2 as list_total_args. compute in list_total_args.
pose list_info.1.1.1.1.2 as list_list_args. compute in list_list_args.
pose list_info.1.1.1.1.1.2 as list_list_ty. compute in list_list_ty.
pose list_info.1.1.1.1.1.1.2 as list_ty_pars. compute in list_ty_pars.
pose list_info.1.1.1.1.1.1.1 as list_npars.  hnf in list_npars. 
let truc := metacoq_get_value (tmQuote list) in pose truc as list_reif.
(* let na := fresh "na" in get_ind_param list na ; pose na.1 as list_indu . 
 match constr:(na) with | (?indu,_) => pose indu as bid end.*)
Fail let x := (get_one_eliminator_return list list_ty_pars 
list_I_app list_reif (* list_ty_default *) list_indu list_npars 2 (*list_nbproj *) 
2 (*nbconstruct*) list_list_args   list_return_ty  list_nb_args_prev list total_args )
in pose x as truc.


Abort.

(* get_one_eliminator_return 
I ty_pars I_app ty_default I_indu npars nbproj nbconstruct 
list_args return_ty nb_args_previous_construct total_args *)

Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=
match n with
| 0 => constr:(list_eq)
| S ?n' => let prod := eval cbv in (nth n' list_args (nil, 0)) in
           let nbproj := eval cbv in (prod.2) in 
           let c_reif := eval cbv in (nth n' list_constructors_reif impossible_term_reif) in
           let nb_args_previous_construct := eval cbv in (nb - nbproj) 
in constr:((nbproj,nb_args_previous_construct))
end.



(* 
Ltac get_ty_def_return_ty n I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif list_elims :=
match n with
| 0 => let elim_app := eval cbv in (get_elim_applied list_elims lpars) in
       let get_equ := eval cbv in (get_equality c_reif (tRel 0) elim_app) in get_equ
| S ?n' =>  let ty_default := eval cbv in (codomain_nbconstruct list_args (nbconstruct - 1) n' ) 
in 
            let return_ty := eval cbv in (lift 2 0 (get_return_type_nbconstruct I_app ty_default))
*) 

(***********************************)

(*****    fin tests       *************)

(***********************************)



Ltac get_eliminators_one_constructor_return_aux n I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif list_elims :=
match n with
| 0 => let elim_app := eval cbv in (get_elim_applied list_elims lpars) in
       let get_equ := eval cbv in (get_equality c_reif (tRel 0) elim_app) in get_equ
| S ?n' =>  let ty_default := eval cbv in (codomain_nbconstruct list_args (nbconstruct - 1) n' ) 
in 
            let return_ty := eval cbv in (lift 2 0 (get_return_type_nbconstruct I_app ty_default))
(* différence entre ty_default et return_ty: faire control F *)
 in (* idtac ty_default ;*) 
(*  idtac "kikooo"  return_ty ; *)
(*let k1 := fresh "kikoooootydef" in pose ty_default as k1  ; *)
(* let l2 := fresh "kikoooreturnty" in pose return_ty as k2  ; *)
            let x := get_one_eliminator_return I ty_pars I_app ty_default I_indu npars n nbconstruct list_args return_ty nb_args_previous_construct total_args in 
    (* list_args devient le 8ème  arg de    get_eliminators_one_constructor_return_aux  *)   
     get_eliminators_one_constructor_return_aux n' I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif  (x :: list_elims)
end.

Ltac get_eliminators_one_constructor_return n I ty_pars I_app I_indu npars nbconstruct list_args0 nb_args_previous_construct total_args lpars c_reif :=
let list_args := eval cbv in (split (list_args0)).1 in
(* maintenant, list_args := val cbv in (split (list_args0)).1  
   et list_args_0 est le 8è param de get_eliminators_one_constructor_return
*)
get_eliminators_one_constructor_return_aux n I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif (@nil (term*nat)).

Ltac get_eliminators_aux_st n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=
match n with
| 0 => constr:(list_eq)
| S ?n' => let prod := eval cbv in (nth n' list_args (nil, 0)) in
           let nbproj := eval cbv in (prod.2) in 
           let c_reif := eval cbv in (nth n' list_constructors_reif impossible_term_reif) in
           let nb_args_previous_construct := eval cbv in (nb - nbproj) in
          let x :=
          get_eliminators_one_constructor_return nbproj I ty_pars I_app I_indu npars n list_args nb_args_previous_construct total_args lpars c_reif in
 (* ici, le 8ème arg de get_eliminators_one_constructor_return s'appelle list_args et non list_args0.
 c'est aussi le 7ème arg de get_eliminators_aux_st
*) 
          get_eliminators_aux_st n' I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb_args_previous_construct constr:(x::list_eq)
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
let I_rec_term := eval cbv in (I_rec.2) in
let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars)) in 
  let list_args := eval cbv in (split list_args_len).1 in 
  let list_ty_default0 := eval cbv in (flatten list_args) in
  let list_ty_default := eval cbv in (lift_rec_rev list_ty_default0) in 
  let nbconstruct := eval cbv in (Datatypes.length list_args) in
  let list_constructors_reif := eval cbv in (get_list_ctors_tConstruct_applied I_rec_term nbconstruct npars) in 
  let total_args := eval cbv in (total_arg_constructors list_args_len) 
  in
  (* idtac total_args *)
 (*   \Q pq idtac total_args fait planter le prog ? *) 
  let list_of_pars_rel := eval cbv in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval cbv in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st nbconstruct na ty_pars I_app I_indu npars list_args_len total_args list_of_pars_rel list_constructors_reif total_args (@nil term) in 
(* le 7ème arg de get_eliminators_aux_st est list_args_len, que l'on obtient dans get_info *)
                      let t := eval cbv in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
let nb_intros := eval cbv in (npars + total_args) in 
 assert (Helim : u') by (prove_by_destruct_varn nb_intros)
 end in Helim
        | _ => fail
| None => fail
end
end.



Ltac get_blut I_rec na := 
let I_rec_term := eval cbv in (I_rec.2) in
let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval cbv in (rev (get_args_list_with_length list_ty npars)) in 
  let list_args := eval cbv in (split list_args_len).1 in 
  let list_ty_default0 := eval cbv in (flatten list_args) in
  let list_ty_default := eval cbv in (lift_rec_rev list_ty_default0) in 
  let nbconstruct := eval cbv in (Datatypes.length list_args) in
  let list_constructors_reif := eval cbv in (get_list_ctors_tConstruct_applied I_rec_term nbconstruct npars) in 
  let total_args := eval cbv in (total_arg_constructors list_args_len) in
  let list_of_pars_rel := eval cbv in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval cbv in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st nbconstruct na ty_pars I_app I_indu npars list_args_len total_args list_of_pars_rel list_constructors_reif total_args (@nil term) in 
  let kik := fresh "kik" in pose x as kik      
              (*    let t := eval cbv in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
let nb_intros := eval cbv in (npars + total_args) in 
 assert (Helim : u') by (prove_by_destruct_varn nb_intros)
 end in Helim
        | _ => fail
| None => fail
end
end *)
end
end.


 
Ltac get_eliminators_st_return_quote I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_eliminators_st_return I_rec I.


Ltac get_blut_quote I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_blut I_rec I.


Ltac get_eliminators_st I :=
let st := get_eliminators_st_return_quote I in idtac.


Ltac get_bluts I := let st := get_blut_quote I in idtac.

Section tests_eliminator.

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
let t := eval cbv in t0 in instantiate_tuple_terms_inhab H t t.

Ltac get_eliminators_st_default I t0 :=
let t := eval cbv in t0 in 
let H' := get_eliminators_st_return I in
instantiate_tuple_terms_inhab H' t t.

Ltac get_eliminators_st_default_quote I t0 :=
let t := eval cbv in t0 in 
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
let t := eval cbv in t0 in
match goal with 
| |- ?T => let T_reif := metacoq_get_value (tmQuote T) in 
          let l := eval cbv in (get_ind_of_prod_no_dup_default T_reif) in
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
in let prod_types0 := eval cbv in p in tac_rec t prod_types0.

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
