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

MetaCoq Quote Definition Set_reif := Set.
MetaCoq Quote Definition list_reif := Set.
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
 Definition branch_default_var (l0 : list term) (i : nat) (k : nat) (n : nat) :=
  let len := Datatypes.length l0 in 
  (* \TODO choisir metavariables*)
  (* \TODO factoriser le calcul de length dans les fonctions qui appellent branch_default_var
  branch_default_var n'a pas besoin de l0 mais seulement de sa longueur
  *)
  (* \TODO on peut pê se débarrasser d'un arg entier, n est probablement égal à ... *)
  let kp := if Nat.eqb n k then len - i
  else S len in
  let fix aux k acc :=
    match k with 
    | 0 => acc 
    | S k => aux k (mkLam hole acc)
    end
  in aux len (tRel kp).  
(* tRel 1 will be the parameter for the default value *)
    (* note that tRel 1 is not bound in the above function *)
 
Goal False.
let x := constr:(branch_default_var [tRel 30 ; tRel 50 ; tRel 90 ; tRel 12 ; tRel 42 ; tRel 9 ] 1 1 2) in pose x as kik ; compute in kik. (* A PRIORI, PAS BESOIN DE CALCULER LES TYPES DONC A QUOI SERT TY_CONSTRUCT ?*)
Abort.

Definition blut_case (I : term) (indu: inductive) (llA : list (list term))  (* lctors : list term *) (ln : list nat) (* (p : nat) *) (* : list (nat * term) *) :=  0.
(*   let fix aux1 llA acc := 0 in 0. *)


(* \TODO long term: recover the "relevant" parameter and not hard-code it *)
(* Constructs the pattern matching in the eliminator
for instance, given the right arguments to construct the predecessor function we get the reified
< match x with
| 0 => default
| S y => y > *)
(* note: pas besoin de list de list de termes, mais seulement de leur longueur,
cf. branch_default_var *)
Definition mkCase_eliminator_default_var (I : inductive) (p : nat) (i : nat) (k : nat)
(ty_arg_constr : list (list term)) (return_type : term) := 
let fix aux (I : inductive) (p: nat) (i : nat) (k : nat)
(ty_arg_constr : list (list term)) (return_type : term) (acc: list (nat × term)) (acc_nat : nat) :=
match ty_arg_constr with 
| [] => tCase (I, p, Relevant) return_type (tRel 0) (tr_rev acc)
| l0 :: xs => aux I p i k xs return_type 
((acc_nat, branch_default_var l0 i k acc_nat)::acc) (acc_nat + 1)
end
in aux I p i k ty_arg_constr return_type [] 0.
(* construit le match de l'éliminateur et le default variable non-liée tRel 1 *)







(* The following two functions bind the arguments of the eliminators : the parameters and the default term *)
(* \TODO : fusionner proj_one_ctor_default_var *)
Definition proj_one_ctor_default_var (I_app : term) (ty_default : term) (indu : inductive) (p : nat) (i : nat) (k : nat)
(ty_arg_constr : list (list term)) (return_type : term) := mkLam ty_default (* lambda truc du type par défaut *)
(mkLam (lift 1 0 I_app)  (* lambda de l'inductif appliqué 
\Q pourquoi le lift ? *)
(mkCase_eliminator_default_var indu p i k ty_arg_constr return_type)).

(* TODO c'est cette fonction dont on a besoin *)
Goal False.

(* ainsi, le premier arg est la valeur par défaut, qu'on instancie plus tard, à l'aide CompDec *)

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

Abort.

(* \!!!!!!!!!!!!! ICI ON SE SERT DU CONTENU DE ty_arg_constr *)
Definition proj_one_ctor_params_default_var (ty_params : list term) (I_app : term) (ty_default : term) (I : inductive) (p : nat) (i : nat) 
(k : nat) (ty_arg_constr : list (list term)) (return_type : term) :=
let fix aux ty_params acc :=
match ty_params with 
| nil => acc
| x :: xs => aux xs (mkLam x acc)
end in aux ty_params (proj_one_ctor_default_var I_app ty_default I p i k ty_arg_constr return_type).


Definition proj_one_ctor_params_default_var0 (ty_params : list term) (I_app : term) (ty_default : term) (I : inductive) (p : nat) (i : nat) 
(k : nat) (ty_arg_constr : list (list term)) (return_type : term) :=
let fix aux ty_params acc :=
match ty_params with 
| nil => acc
| x :: xs => aux xs (mkLam x acc)
end in aux ty_params (proj_one_ctor_default_var I_app (tRel p) I p i k ty_arg_constr return_type).




(* remove_n n [a_1; ... ; a_n ; .... ; a_p ] = [a_{n+1} ; ... ; a_p ]*)
Fixpoint remove_n {A} (n : nat) (l : list A) := 
match n with 
| 0 => l 
| S n' => match l with
        | nil => nil
        | cons x xs => remove_n n' xs
        end
end.


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
(map_iter 0 unlift (remove_n p (tr_rev (fst res0))), snd res0). 
(* \TODO problème de unlift, car on doit relifter après *)


Goal False.
(* let x := get_ctors_and_types_i t *)
clear.
let x := constr:(args_of_prod_with_length (tProd (mkNamed "x") (tRel 8) (tProd (mkNamed "x") (tRel 13) ( tProd (mkNamed "x") (tRel 21) (tProd  (mkNamed "x") (tRel 33)
( tRel 10 ))) )) 0 ) in pose x as aopex ; unfold args_of_prod_with_length in aopex  ; unfold remove_n in aopex ; unfold map_iter in aopex ; unfold tr_rev in aopex ; simpl in aopex.
Abort. 

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
unfold args_of_prod_with_length in galenex  ; unfold remove_n in galenex ; unfold map_iter in galenex ; simpl in galenex.
Abort.  *)

(* get_indu_app_to_params t n = tApp t [tRel (n-1) ; .... ; tRel 0]
   tail-recursive
*)
Definition get_indu_app_to_params (t : term) (n : nat) := 
  let fix aux n acc :=
   match n with
   | 0 => acc 
   | S n => aux n ((tRel n)::acc)
   end
in tApp t (tr_rev (aux n [])). 


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
(* \TODO total_arg_ctors n'est utilisé que dans Ltac get_eliminators_st_return sur list_args_len. Une info est sans doute calculée deux fois. 
On peut s'en doute s'en débarrasser 
*)

(* mkProd [A1 ; .... ; An ] t = tProd "x" A1. ... tProd "x" An. t  *)
Fixpoint mkProd_rec (l : list term) (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd (mkNamed "x")  x t)
end.
(* \TODO mkProd_rec n'est utilisée que dans get_eliminators_st_return, mais deux fois sur la même ligne
Voir si on peut éliminer ou facto du code.
*)

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



(* gets each elimination function applied to the parameters, the default and the term *)
(* get_elim_applied [(p0 , d0 ); ... ; (pn , dn)] [A1 ; ... ; Ak ]
     = [ tApp p0 [ A1 ; ... ; Ak ; tRel d0 ; tRel0 ] 
     ; ... ; tApp pn [A1 ; ... ; An ; tRel dn ; tRel 0]]*)
Fixpoint get_elim_applied (list_tVar : list (term * nat)) (lpars : list term) :=
match list_tVar with
| nil => nil
| (elim, db) :: xs => (tApp elim (lpars ++ [tRel db; tRel 0])) :: get_elim_applied xs lpars
end.
(* \TODO comprendre pq ici le default est Rel 0 et pas Rel 1, ou alors c'est tRel db ?  *)
(* n'est utilisée que dans get_eliminators_one_ctor_return_aux sur list_elims *)



(* get_list_of_holes n = [hole ; ... ; hole] (n occurrences)
   tail-recursive *)
Definition get_list_of_holes (n : nat) :=
  let fix aux n acc := 
  match n with
  | 0 => acc 
  | S n => aux n (hole :: acc)
end in aux n [].



(* get_list_ctors_tConstruct_applied I k n := [tApp C0 hole_n ; ... ; tApp Ck hole_n ]
  where C0, ..., Ck are the constructors of I
  k should be the number of ctors of I
  n the number of parameters of I
*)
(* tail recursive *)
Definition get_list_ctors_tConstruct_applied (I : term) (n : nat) (p : nat) :=
let l := get_list_of_holes p in
match I with
| tInd indu inst => let fix aux n acc  := match n with
          | 0 => acc
          | S m => aux m ((tApp (tConstruct indu m inst) l) :: acc )
          end in aux n []
| _ => []
end.
(* \TODO : remove tApp when n = 0 *)


(**  mkOr [A1_reif ; ... ; An_reif] produce the reification of A1 \/ ... \/ A_n
    tail-recursive **)
Definition mkOr (l : list term) := 
  let l' := tr_rev l in 
  match l' with
  | [] => impossible_term_reif 
  | x0 :: l0 => 
  let fix aux l acc :=
match l with
| [] => impossible_term_reif
| [ x ] => tApp or_reif (x :: [acc]) 
| x :: xs => aux xs (tApp or_reif (x :: [acc]))
end in aux l0 x0
end.




MetaCoq Quote Definition S_reif := S. 
MetaCoq Quote Definition O_reif := O.


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




(***********************************)

(***** tests Pierre  (à transférer)      *********)

(***********************************)

(* i : numéro de la projection *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, i est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)
(* ty_default *)

Ltac get_list_args_len I_rec na :=
  let I_rec_term := eval compute in (I_rec.2) in
  let opt := eval compute in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?p, ?ty_pars) =>
  let list_ty := eval compute in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval compute in (get_args_list_with_length list_ty p)
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

(* list_args := val compute in (split (list_args0)).1   *)

Ltac get_ty_arg_constr_quote I na:=  
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_ty_arg_constr  I_rec  na.



Ltac get_info0 I_rec na := (* \TODO remove *)
  let I_rec_term := eval compute in (I_rec.2) in
  let opt := eval compute in (get_info_params_inductive I_rec_term I_rec.1) in 
  match opt with 
  | Some (?p, ?ty_pars) =>
  let list_ty := eval compute in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval compute in (get_args_list_with_length list_ty p) in 
  let list_args := eval compute in (split list_args_len).1 in 
  pose list_args as na end .


Ltac get_info0_quote I na := (* \TODO remove *)
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_info0 I_rec  na ; compute in na.



Ltac get_info I_rec na :=
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
  let total_args := eval compute in (total_arg_ctors list_args_len) in
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted p (total_args + 1))) in
  let I_app := eval compute in (get_indu_app_to_params I_rec_term p) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
  let x := constr:((((((((p,ty_pars),list_ty),
list_args),total_args),list_of_pars_rel),I_app),I_indu)) 
  in pose x as na 
end  
end.


Ltac get_info_quote I na := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_info I_rec  na ; compute in na.

 
(* list_of_pars_rel is also called lpars *)
 


Ltac get_info2 I_rec na :=
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
  let total_args := eval compute in (total_arg_ctors list_args_len) in
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted p (total_args + 1))) in
  let I_app := eval compute in (get_indu_app_to_params I_rec_term p) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
  let x := constr:(((((((list_args_len,list_args),list_ty_default0),list_ty_default),k),list_ctors_reif),list_of_pars_rel))
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
pose list_info.1.1.1.1.1.1.1 as list_p.  hnf in list_p. 
let truc := metacoq_get_value (tmQuote list) in pose truc as list_reif.
(* let na := fresh "na" in get_ind_param list na ; pose na.1 as list_indu . 
 match constr:(na) with | (?indu,_) => pose indu as bid end.*)
Fail let x := (get_one_eliminator_return list list_ty_pars 
list_I_app list_reif (* list_ty_default *) list_indu list_p 2 (*list_nbproj *) 
2 (*k*) list_list_args   list_return_ty  list_nb_args_prev list total_args )
in pose x as truc.
Abort.

(* get_one_eliminator_return 
I ty_pars I_app ty_default I_indu p i k 
list_args return_ty nb_args_previous_construct total_args *)

(* \TODO rename this function*)
Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu p list_args total_args lpars list_ctors_reif nb list_eq :=
match n with
| 0 => constr:(list_eq)
| S ?n' => let prod := eval compute in (nth n' list_args (nil, 0)) in
           let i := eval compute in (prod.2) in 
           let c_reif := eval compute in (nth n' list_ctors_reif impossible_term_reif) in
           let nb_args_previous_construct := eval compute in (nb - i) 
in constr:((i,nb_args_previous_construct))
end.

(***********************************)

(*****    fin tests    *************)

(***********************************)





(*  mkLam I_app (lift0 1  ty_default) seems to compute a return type. Of what ? *)
(*  -> ty_default   *)

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
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted p (total_args + 1))) in
  let I_app := eval compute in (get_indu_app_to_params I_rec_term p) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st k na ty_pars I_app I_indu p list_args_len total_args list_of_pars_rel list_ctors_reif total_args (@nil term) in 
(* le 7ème arg de get_eliminators_aux_st est list_args_len, que l'on obtient dans get_info *)
                      let t := eval compute in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "KIKOOO"%string ; binder_relevance := Relevant |} 
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


Definition ret_ty_proj lA (* la longueur est-elle un param ou doit-elle être calculée ? *)
  := let fix aux l k acc := 
    match l with
    | [] => acc 
    | A :: l => aux l (S k) ((unlift k A) :: acc)
    end in tr_rev (aux lA 0 []).


Ltac get_my_bluts t na := 
  (* let _ := match goal with  _ => idtac end in *)
  let indmind := fresh "indmind" in pose_blut t indmind ; 
  lazymatch eval compute in indmind with
  | (?induu,?mind) => 
    lazymatch eval hnf in induu with
    | (?indu, ?u) =>
    let pparams := constr:(get_params_from_mind mind) in
    lazymatch eval hnf in pparams with 
    | (?p,?lA) =>
    lazymatch eval hnf in pparams with
    | (?p, ?lA) => let oind := constr:(hd nat_oind mind.(ind_bodies)) in
     let gct :=
    constr:(get_ctors_and_types_i indu p 1 0 u  oind) 
   in  lazymatch eval hnf in gct with 
    | (?lBfA,?ln) => lazymatch eval hnf in lBfA with
      | (?lBf,?llA) =>  lazymatch eval cbv in lBf with
        | (?lB,?lf) =>   let llAtrunc := constr:(tr_map (remove_n p) llA) in  let x :=
        constr:((((((((llAtrunc,lB),lf),llA),ln),lA),p)))   in pose x as na ; let trunctruc := constr:(tr_map ret_ty_proj llAtrunc) in pose trunctruc as y ;  clear indmind
        end
      end
    end
    end
  end end end
  .       
   
  

  Goal False.
  let indmind := fresh "indmind" in pose_blut list indmind. clear indmind.
  get_my_bluts list ik ; compute in ik ; compute in y.  
pose [[];
[tRel 0;
tApp
  (tInd
     {|
       inductive_mind :=
         (MPfile ["Datatypes"; "Init"; "Coq"], "list");
       inductive_ind := 0
     |} []) [tRel 1]]] as machin.


  (*  let x := get_my_bluts list ik in pose x as kikoo.*)
  Abort.

(* 
let t_reif := eval compute in (I_rec.2) in
let pparams :=  
let opt_plA := eval compute in (get_info_params_inductive t_reif I_rec.1) in 
match opt_plA with 
| Some (?p, ?lA) =>
 (**  let gct := eval compute in (get_ctors_and_types_i ) *)
  let list_ty := eval compute in (list_types_of_each_constructor I_rec) in 
  let list_args_len := eval compute in (get_args_list_with_length list_ty p) in 
  let list_args := eval compute in (split list_args_len).1 in 
  let list_ty_default0 := eval compute in (tr_flatten list_args) in
  let list_ty_default := eval compute in (lift_rec_rev list_ty_default0) in 
  let k := eval compute in (Datatypes.length list_args) in
  let list_ctors_reif := eval compute in (get_list_ctors_tConstruct_applied t_reif k p) in 
  let total_args := eval compute in (total_arg_ctors list_args_len) 
  in
  (* idtac total_args *)
 (*   \Q pq idtac total_args fait planter le prog ? *) 
  let list_of_pars_rel := eval compute in ((get_list_of_rel_lifted p (total_args + 1))) in
  let I_app := eval compute in (get_indu_app_to_params t_reif p) in
  let I_lifted := eval compute in (lift (total_args) 0 I_app) in
        match t_reif with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st k na lA I_app I_indu p list_args_len total_args list_of_pars_rel list_ctors_reif total_args (@nil term) in 
(* le 7ème arg de get_eliminators_aux_st est list_args_len, que l'on obtient dans get_info *)
                      let t := eval compute in (mkProd_rec lA (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
let nb_intros := eval compute in (p + total_args) in 
 assert (Helim : u') by (prove_by_destruct_varn nb_intros)
 end in Helim
        | _ => fail
| None => fail
end
end.*)




 
Ltac get_eliminators_st_return_quote I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
get_eliminators_st_return I_rec I.



Ltac get_eliminators_st I :=
let st := get_eliminators_st_return_quote I in idtac.



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
