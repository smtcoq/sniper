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
Require Import definitions.
Require Import expand.
Require Import elimination_pattern_matching.
Require Import elimination_polymorphism.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.

Require Import SMTCoq.SMTCoq.


Definition get_nth_constructor (I : term) (n : nat) : term := 
let g := get_info_inductive I in match g with 
  | None => impossible_term_reif
  | Some (ind, inst) => tConstruct ind n inst
end. 


Definition mkApp (u : term) (l : list term) :=
tApp u l.


Ltac get_inhabitant t := 
let t_reif_rec := metacoq_get_value (tmQuoteRec t) in 
let p := eval cbv in (no_app t_reif_rec.2) in
let t_reif_no_app := eval cbv in p.1 in
let params := eval cbv in p.2 in
let opt1 := eval cbv in 
(find_index_constructor_of_arity_zero (get_constructors_inductive t_reif_no_app (t_reif_rec.1))) in
let nb := remove_option opt1 in 
let construct_reif := eval cbv in (mkApp (get_nth_constructor t_reif_no_app nb) params) in
construct_reif.

Ltac find_inhabitant t := 
let construct_reif := get_inhabitant t in
let construct0 := metacoq_get_value (tmUnquote construct_reif) in 
let construct := eval cbv in construct0.(my_projT2) in
exact construct.


Ltac find_inhabitant_context t := 
first[ find_inhabitant | constructor ; assumption | apply Inh | epose (inhab := ?[t_evar] : t)]. 

Ltac find_inh t :=
match goal with
| H : t |- _ => H
| _ => let H := fresh in let _ := match goal with _ => assert (H : t) by find_inhabitant_context t end in H
end.

Section test_inhabitants.
Variable A : Type. 
Goal list False.
let c := (get_inhabitant nat) in pose c.
find_inhabitant_context (list False).
Qed.

Goal nat.
find_inhabitant nat. Qed.


Goal (list A). 
find_inhabitant (list A). 
Qed.

Goal (list False). 
exact (@nil False). Qed. 

End test_inhabitants.

Definition mkLam Ty t := match Ty with 
| tSort _ => tLambda {| binder_name := nNamed "A"%string ; binder_relevance := Relevant |} Ty t
| _ => tLambda {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} Ty t
end.


Definition get_return_type (indu_app_to_params : term) (domain : term) := 
mkLam indu_app_to_params (lift 1 0 domain).

Definition codomain_nbconstruct (list_ty_construct : list (list term)) (nbconstruct : nat) (nbproj : nat) :=
nth nbproj (nth nbconstruct list_ty_construct nil) impossible_term_reif. 


Definition get_return_type_nbconstruct (indu_app_to_params : term) (codomain : term) :=
get_return_type indu_app_to_params codomain.


Definition get_proj (n : nat) (l_ty : list term) := 
let k := Datatypes.length l_ty in 
let fix aux l t :=
match l with 
| nil => t
| x :: xs => aux xs (mkLam x t) 
end in aux l_ty (tRel (k - n)).

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

Definition branch (l0 : list term) (nbproj : nat) (nbconstruct : nat) (n : nat) (default : term) :=
let len := Datatypes.length l0 in 
if Nat.eqb n nbconstruct then 
let fix aux l acc :=
match l with 
| [] => acc 
| y :: ys => aux ys (mkLam hole acc)
end
in aux l0 (tRel (len - nbproj))
else
let fix aux' l acc := match l with 
      | [] => acc
      | y :: ys => aux' ys (mkLam hole acc)
      end
in aux' l0 default.

Definition mkCase_eliminator (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (default : term) (return_type : term) := 
let fix aux (I : inductive) (npars: nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (default : term) (return_type : term) (acc: list (nat × term)) (acc_nat : nat) :=
match ty_arg_constr with 
| [] => tCase (I, npars, Relevant) return_type (tRel 0) (List.rev acc)
| x :: xs => aux I npars nbproj nbconstruct xs default return_type 
((acc_nat, branch x nbproj nbconstruct acc_nat default)::acc) (acc_nat + 1)
end
in aux I npars nbproj nbconstruct ty_arg_constr default return_type [] 0. 


Definition proj_one_constructor (i : term) (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (default : term) (return_type : term) := 
mkLam i (mkCase_eliminator I npars nbproj nbconstruct ty_arg_constr default return_type). 

Definition proj_one_constructor_params (ty_params : list term) (i : term) (I : inductive) (npars : nat) (nbproj : nat) 
(nbconstruct : nat) (ty_arg_constr : list (list term)) (default : term) (return_type : term) :=
let fix aux ty_params acc :=
match ty_params with 
| nil => acc
| x :: xs => aux xs (mkLam x acc)
end in aux ty_params (proj_one_constructor i I npars nbproj nbconstruct ty_arg_constr default return_type).

(** version with default = tRel 1 **)

Definition branch_default_var (l0 : list term) (nbproj : nat) (nbconstruct : nat) (n : nat) :=
let len := Datatypes.length l0 in 
let l := List.map (lift (len + 1) 0) l0 in
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
in aux' l (tRel 1).

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


Definition proj_one_constructor_default_var (i : term) (ty_default : term) (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) := mkLam ty_default
(mkLam (lift 1 0 i) (mkCase_eliminator_default_var I npars nbproj nbconstruct ty_arg_constr return_type)).



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

Ltac get_eliminator nbconstruct nbproj I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
let I_rec_term := eval cbv in (I_rec.2) in
let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args := eval cbv in (rev (get_args_list list_ty npars)) in 
  let ty_default := eval cbv in (codomain_nbconstruct list_args (nbconstruct - 1) (nbproj - 1) ) in 
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let return_ty := eval cbv in (lift 2 0 (get_return_type_nbconstruct I_app ty_default)) in
  (* lift 2 0 because we quantify over two new variables: the default and the inductive we match on *)
  
  match I_rec_term with
  | tInd ?I_indu _ => let p := eval cbv in (proj_one_constructor_params_default_var ty_pars I_app ty_default I_indu npars nbproj (nbconstruct - 1) (rev_list_map list_args) return_ty) in
                    let u := metacoq_get_value (tmUnquote p) in
                    let x := eval cbv in u.(my_projT2) in
                    let name := fresh "proj_" I in
                    pose (name := x)
  | _ => fail
| None => fail
end
end.

Ltac get_one_eliminator I ty_pars I_app ty_default I_indu npars nbproj nbconstruct list_args return_ty :=
let p := eval cbv in (proj_one_constructor_params_default_var ty_pars I_app ty_default I_indu npars nbproj (nbconstruct - 1) (rev_list_map list_args) return_ty) in
let u := metacoq_get_value (tmUnquote p) in
let x := eval cbv in u.(my_projT2) in
let name := fresh "proj_" I in
pose (name := x).


Ltac get_eliminators_one_constructor n I ty_pars I_app I_indu npars nbconstruct list_args :=
match n with
| 0 => idtac
| S ?n' =>  let ty_default := eval cbv in (codomain_nbconstruct list_args (nbconstruct - 1) n' ) in 
            let return_ty := eval cbv in (lift 2 0 (get_return_type_nbconstruct I_app ty_default)) in
            get_one_eliminator I ty_pars I_app ty_default I_indu npars n nbconstruct list_args return_ty ; get_eliminators_one_constructor n'
            I ty_pars I_app I_indu npars nbconstruct list_args
end.

Ltac get_eliminators_aux n I ty_pars I_app I_indu npars list_args :=
match n with
| 0 => idtac 
| S ?n' => let nbproj := eval cbv in (Datatypes.length (nth n' list_args nil)) in 
          get_eliminators_one_constructor nbproj I ty_pars I_app I_indu npars n list_args ;
          get_eliminators_aux n' I ty_pars I_app I_indu npars list_args
end.
              


Ltac get_eliminators I := 
let I_rec := metacoq_get_value (tmQuoteRec I) in
let I_rec_term := eval cbv in (I_rec.2) in
let opt := eval cbv in (get_info_params_inductive I_rec_term I_rec.1) in 
match opt with 
| Some (?npars, ?ty_pars) =>
  let list_ty := eval cbv in (list_types_of_each_constructor I_rec) in 
  let list_args := eval cbv in (rev (get_args_list list_ty npars)) in 
  let nbconstruct := eval cbv in (Datatypes.length list_args) in 
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
        match I_rec_term with
        | tInd ?I_indu _ => 
                      get_eliminators_aux nbconstruct I ty_pars I_app I_indu npars list_args 
        | _ => fail
| None => fail
end
end.


MetaCoq Quote Definition or_reif := Logic.or.

MetaCoq Quote Definition eq_reif := @eq.


Fixpoint mkOr (l : list term) := 
match l with
| nil => impossible_term_reif
| [ x ] => x
| cons x xs => tApp or_reif [x ; mkOr xs]
end.

Ltac get_one_eliminator_return I ty_pars I_app ty_default I_indu npars nbproj nbconstruct list_args return_ty nb_args_previous_construct total_args :=
let p := eval cbv in (proj_one_constructor_params_default_var ty_pars I_app ty_default I_indu npars nbproj (nbconstruct - 1) (rev_list_map list_args) return_ty) in
let u := metacoq_get_value (tmUnquote p) in 
let x := eval cbv in u.(my_projT2) in
let name := fresh "proj_" I in let _ := match goal with _ =>
pose (name := x) ; let H0 := get_def_cont name in expand_hyp_cont H0 ltac:(fun H => 
eliminate_pattern_matching_cont H (nbconstruct -1) ltac:(fun H => instantiate_tuple_terms_goal H)) ; clear H0 end in
let elim := metacoq_get_value (tmQuote name) in 
let db := eval cbv in (total_args + 1 - nb_args_previous_construct - nbproj) in
constr:((elim, db)).

Ltac get_eliminators_one_constructor_return_aux n I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif list_elims :=
match n with
| 0 => let elim_app := eval cbv in (get_elim_applied list_elims lpars) in
       let get_equ := eval cbv in (get_equality c_reif (tRel 0) elim_app) in get_equ
| S ?n' =>  let ty_default := eval cbv in (codomain_nbconstruct list_args (nbconstruct - 1) n' ) in 
            let return_ty := eval cbv in (lift 2 0 (get_return_type_nbconstruct I_app ty_default)) in
            let x := get_one_eliminator_return I ty_pars I_app ty_default I_indu npars n nbconstruct list_args return_ty nb_args_previous_construct total_args in 
            get_eliminators_one_constructor_return_aux n' I ty_pars I_app I_indu npars nbconstruct list_args nb_args_previous_construct total_args lpars c_reif  (x :: list_elims)
end.

Ltac get_eliminators_one_constructor_return n I ty_pars I_app I_indu npars nbconstruct list_args0 nb_args_previous_construct total_args lpars c_reif :=
let list_args := eval cbv in (split (list_args0)).1 in
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
          get_eliminators_aux_st n' I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb_args_previous_construct constr:(x::list_eq)
end.

Ltac prove_by_blind_destruct := 
let x := fresh in 
intro x ; try (destruct x ; auto) ; prove_by_blind_destruct.

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
  let total_args := eval cbv in (total_arg_constructors list_args_len) in
  let list_of_pars_rel := eval cbv in ((get_list_of_rel_lifted npars (total_args + 1))) in
  let I_app := eval cbv in (get_indu_app_to_params I_rec_term npars) in
  let I_lifted := eval cbv in (lift (total_args) 0 I_app) in
        match I_rec_term with
        | tInd ?I_indu _ =>
                      let x := get_eliminators_aux_st nbconstruct na ty_pars I_app I_indu npars list_args_len total_args list_of_pars_rel list_constructors_reif total_args (@nil term) in 
                      let t := eval cbv in (mkProd_rec ty_pars (mkProd_rec list_ty_default (tProd {| binder_name := nNamed "x"%string ; binder_relevance := Relevant |} 
    I_lifted (mkOr x)))) in
                      let u := metacoq_get_value (tmUnquote t) in 
                      let u' := eval hnf in (u.(my_projT2)) in let Helim := fresh in let _ := match goal with _ =>
assert (Helim : u') by (prove_by_blind_destruct) end in Helim
        | _ => fail
| None => fail
end
end.

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
get_eliminators nat.
clear.
get_eliminators list.
clear.
get_eliminator 2 1 Ind_test.
clear.
get_eliminators Ind_test.
clear.
get_eliminators Ind_test2.
Abort.


Goal False.
get_eliminator 2 1 nat.
get_eliminator 2 1 list.
get_eliminator 2 2 list.
Abort. 

Goal False.
get_eliminators_st nat. clear.
get_eliminators_st list. clear.
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


Ltac instantiate_inhab H :=
let T := type of H in 
match T with 
| forall (y : ?A), forall (z : ?B), _ => try (let inh := find_inh A in
let H' := instantiate_ident H inh in instantiate_inhab H' ; clear H)
| _ => idtac
end.

Ltac instantiate_tuple_terms_inhab H t1 t2 := match t1 with
| (?x, ?t1') => try (let H' := instantiate_ident H x in
instantiate_tuple_terms_inhab H' t2 t2) ; try (instantiate_tuple_terms_inhab H t1' t2)
| unit =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => first [constr_eq A Type ; clear H | instantiate_inhab H]
            | _ => idtac
            end
end.

Ltac instantiate_tuple_terms_goal_inhab H := let t0 := return_tuple_subterms_of_type_type in 
let t := eval cbv in t0 in instantiate_tuple_terms_inhab H t t.

Ltac get_eliminators_st_default I := 
let H' := get_eliminators_st_return I in
instantiate_tuple_terms_goal_inhab H'.

Ltac get_eliminators_st_default_quote I := 
let H' := get_eliminators_st_return_quote I in
instantiate_tuple_terms_goal_inhab H'.

Section tests_default.

Variable A : Type.
Variable a : A.

Goal nat -> A -> False.
get_eliminators_st_default_quote list. clear -a.
get_eliminators_st_default_quote Ind_test. clear -a.
get_eliminators_st_default_quote Ind_test2. clear -a.
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


MetaCoq Quote Definition bool_reif := bool. 
MetaCoq Quote Definition Z_reif := Z.
MetaCoq Quote Definition nat_reif := nat.


Definition get_ind_of_prod_no_dup_default t := 
get_ind_of_prod_no_dup t [bool_reif ; Z_reif; nat_reif ; eq_reif] [].

Ltac elims_on_list l := 
match l with 
| nil => idtac 
| cons ?x ?xs => let u := metacoq_get_value (tmUnquote x) in 
                 let I := eval hnf in (u.(my_projT2)) in
                 get_eliminators_st_default_quote I ; elims_on_list xs
end.

Ltac get_eliminators_in_goal := match goal with 
| |- ?T => let T_reif := metacoq_get_value (tmQuote T) in 
          let l := eval cbv in (get_ind_of_prod_no_dup_default T_reif) in
          elims_on_list l
end.

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

Definition prod_types := (Z, bool, nat).


Ltac get_eliminators_in_variables := 
let t := vars in 
let rec tac_rec v tuple :=
match v with
| (?v1, ?t') => let T := type of v1 in first [ let U := type of T in constr_eq U Prop ; tac_rec t' tuple |
                let I := get_head T in 
                try (is_not_in_tuple tuple I  ;
                get_eliminators_st_default_quote I) ; try (tac_rec t' (tuple, I)) ]
| _ => idtac
end
in let prod_types0 := eval cbv in prod_types in tac_rec t prod_types0.













