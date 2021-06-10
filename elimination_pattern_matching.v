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


Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import utilities.
Require Import definitions.
Require Import elimination_fixpoints.
Require Import expand.
Require Import List.






(* find the bodies of an inductive simply quoted *)
Fixpoint get_decl_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => None 
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then let loind := ind_bodies mind in Some loind else get_decl_inductive I e'
                                  | _ => get_decl_inductive I e'
                               end)    
    end
end
| _ => None
end.

(* find the number of parameters of an inductive simply quoted *)
Fixpoint get_npar_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => 0
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then ind_npars mind else get_npar_inductive I e'
                                  | _ => get_npar_inductive I e'
                               end)    
    end
end
| _ => 0
end.


(* get the type of a constructor *)
Definition get_type_constructor (c : term):=
match c with
| tConstruct ind _ _ => let kn := ind.(inductive_mind) in 
tInd {| inductive_mind := kn ; inductive_ind := 0 |} []
| _ => unit_reif
end.




(* warning : flattened terms only : returns a pair of a term and the list to which it is applied *)
Definition no_app t := match t with
| tApp u l => (u, l)
| _ => (t, [])
end.



(* Implements beta reduction *)
Fixpoint typing_prod_list (T : term) (args : list term) := 
match T with
| tProd _ A U => match args with 
        | nil => T
        | x :: xs => typing_prod_list (subst10 x U) xs
        end
| _ => T
end.

(* As the constructor contains a free variable to represent the inductive type, this fonction substitutes the given 
inductive type and the parameters in the list of the type of the constructors *)
Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (p : term × (list term)) :=
let T := p.1 in 
let args := p.2 in
match l with 
| nil => nil
| ((_, Ty), _):: l' => (typing_prod_list (subst10 T Ty) args) :: (subst_type_constructor_list l' p)
end.

(* Given a term recursively quoted, gives the list of the type of each of its constructor *)
Definition list_types_of_each_constructor t :=
let v := (no_app t.2) in (* the inductive not applied to its parameters and the list of its parameters *)
let x := get_decl_inductive v.1 t.1 in (* the first inductive declaration in a mutual inductive block  *)
match x with
| Some y => match y with 
          | nil => nil
          | cons y' _ => let z := y'.(ind_ctors) in let u := 
subst_type_constructor_list z v in u
          end
| None => nil
end.


(* Does the same, but does not handle parameters *)
Definition list_types_of_each_constructor_no_subst t :=
let v := (no_app t.2) in (* the inductive not applied to its parameters and the list of its parameters *)
let x := get_decl_inductive v.1 t.1 in (* the first inductive declaration in a mutual inductive block  *)
match x with
| Some y => match y with 
          | nil => nil
          | cons y' _ => let z := y'.(ind_ctors) in List.map (fun p => subst10 v.1 p.1.2) z
          end
| None => nil
end.


Fixpoint codomain (t : term) := match t with 
| tProd _ _ u => codomain u 
| _ => t 
end.




(* Build the list of constructors and their types applied to the parameters *)
Definition build_ctor_ty_ctor_applied_to_parameters (args_in_statement : list term) (p : term * term) := let ctor := p.1 in let ty_ctor := p.2 in 
let ty_args := (no_app (codomain ty_ctor)).2
in let fix aux args_in_statement ty_args ctor ty_ctor := match args_in_statement, ty_args with
| nil, _ => (ctor, ty_ctor)
| _, nil => (ctor, ty_ctor)
| x_in_statement :: args_in_statement', x_in_ty :: ty_args' =>  match x_in_ty with 
        | tRel k => aux args_in_statement' ty_args' (tApp ctor [x_in_statement]) (tApp ty_ctor [x_in_statement])
        | _ => aux args_in_statement' ty_args' ctor ty_ctor
        end 
end
in aux args_in_statement ty_args ctor ty_ctor.
        



Definition get_info_inductive (I : term) := 
let p := no_app I in match p.1 with
| tInd ind inst => Some (ind, inst)
| _ => None
end.

Definition get_info_inductive_args (I : term) := 
let p := no_app I in match p.1 with
| tInd ind inst => Some ((ind, inst), p.2)
| _ => None
end.

Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => ((get_list_of_rel n) ++ [tRel n])%list (* n *)
end.


(* gets the list of constructors applied to their parameters
 given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct_applied I n := 
let I' := get_info_inductive_args I in match I' with
| Some J => let ind := J.1.1 in let inst := J.1.2 in let args := J.2 in let
fix aux n' ind' inst' args :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst' args) ++ [tApp (tConstruct ind' m inst') args]
end
in aux n J.1.1 J.1.2 J.2
| None => []
end.

(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1 in let inst := J.2 in let 
fix aux n' ind' inst' :=
match n' with 
| 0 => []
| S m =>  ((aux m ind' inst') ++ [tConstruct ind' m inst'])%list
end
in aux n J.1 J.2
| None => []
end.


Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].



Definition get_env (T: term) (n  : nat) := 
let fix aux T n acc := 
match (T, n) with
| (tProd _ A t, 0) => ((acc, t), A)
| (tProd _ A t, S n') => aux t n' (A::acc)
| _ => ((acc, T), T)
end
in aux T n [].




Fixpoint prenex_quantif_list (l : list term) (t : term):= 
match l with
| [] => t 
| x :: xs => prenex_quantif_list xs (mkProd x t)
end.

Fixpoint remove_elem (n : nat) (l : list term) := match l, n with
| [], _ => []
| _, 0 => l
| x :: xs, S m => remove_elem m xs
end.


Definition list_of_args (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
(* | tApp t l => let n := Datatypes.length l in remove_elem n 
(rev (aux acc t)) (* we need to remove the n first elements applied in order to avoid quantifying over them *) *)
| _ => acc
end in aux [] t.




Definition prenex_quantif_list_ctor (c : term) (l : list term) (l' : list term) (E : term) :=
(* c is the constructor reified, l is the list of the type of its arguments, l' is the list of the 
type of the prenex quantification in the hypothesis, E is the environment *)
let n := Datatypes.length l in
prenex_quantif_list l' (prenex_quantif_list l (subst [tApp (lift n 0 c) (rev (get_list_of_rel n))] 0 (lift n 1 E))).

Definition get_equalities (E : term) (l_ctors_and_ty_ctors : list (term * term))  (l_ty : list term) := 

let fix aux (E : term) l_ctors_and_ty_ctors (l_ty : list term) acc :=
match l_ctors_and_ty_ctors  with
| nil => acc
| (x, y):: xs => aux E xs l_ty
((prenex_quantif_list_ctor x (list_of_args y) l_ty E) :: acc)
end
in aux E l_ctors_and_ty_ctors l_ty [].


Ltac eliminate_pattern_matching H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) 
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct_applied A n) in 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
 unquote_list list_of_hyp ; prove_hypothesis H )] ; clear H.


Section tests.


Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.
Definition min1' := min1.

Definition min1'' := min1'.

Definition min1''' := min1''.


MetaCoq Quote Definition hyp_cons_reif := ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).


Goal ((forall (A: Type) (x : A) (l : list A) (n : nat), hd x l = match l with 
| [] => x 
| y :: ys => y
end) -> True).
Proof.
intros H. 
eliminate_pattern_matching H.
expand_fun min1.
expand_fun hd.
eliminate_pattern_matching H2.
eliminate_pattern_matching H.

Abort.

Goal ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_pattern_matching H')). assumption.
Qed.


Goal ((forall (A: Type) (l : list A), 
@List.length A l = match l with
| nil => 0
| y :: xs => length xs + 1
end) -> True).
intro H.
eliminate_pattern_matching H.
exact I. 
Qed.


Goal ((forall (H : Type) (H0 : list H),
     #|H0| =
     (fix length (l : list H) : nat :=
        match l with
        | [] => 0
        | _ :: l' => S (length l')
        end) H0) -> True).
intro H.
eliminate_fix_hyp H.
eliminate_pattern_matching H0.
Abort.

End tests.

















