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
Require Import String.
Require Import ZArith.

(** Quoted useful terms **)

MetaCoq Quote Definition unit_reif := unit.

MetaCoq Quote Definition or_reif := Logic.or.

MetaCoq Quote Definition eq_reif := @eq.

MetaCoq Quote Definition bool_reif := bool. 

MetaCoq Quote Definition Z_reif := Z.

MetaCoq Quote Definition nat_reif := nat.

Inductive impossible_term :=.
MetaCoq Quote Definition impossible_term_reif := impossible_term.





(** Tail-recursive (actually linear) version of List.rev **)

Definition tr_rev {A : Type} (l : list A) :=
  let fix aux l acc :=
  match l with
  | [] => acc 
  | x :: l => aux l (x :: acc ) end
  in aux l []. 


(** Tail-recursive (actually linear) version of flatten **)
Definition tr_flatten {A : Type} (l : list (list A)) :=
  let fix aux l acc :=
  match l with
  | [] => acc 
  | l0 :: l => aux l (rev_append l0 acc)
  end in tr_rev (aux l []).




(** tr_revmap f [a1 ; ... ; an ] = [f an ; .... ; f a1 ]
 tail-recursive (actually linear)
**)
Definition tr_revmap {A B : Type } ( f : A -> B) (l : list A) :=
  let fix aux l acc :=
  match l with
  | [] => acc 
  | x :: l => aux l (f x :: acc ) end
  in aux l [].


(** Tail-recursive (actually linear) version of List.map 
    Sometimes, cannot replace List.map, because Coq cannot guess the decreasing argument
**)

Definition tr_map {A B : Type} (f: A -> B) (l : list A) :=
  let l0 := tr_rev l in 
  let fix aux l acc :=
  match l with
  | [] => acc 
  | x :: l => aux l (f x :: acc ) end
  in aux l0 [].



(** Functions to build MetaCoq terms **)


(*  declaring variables   *)
Open Scope string_scope.

Definition mkNamed s := ({| binder_name := nNamed (s%string); binder_relevance := Relevant |} : aname).
Definition mkNAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.


Definition mkNamedtry := mkNamed (("B"%string) : ident).

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkProd T u :=
tProd mkNAnon T u.

Definition mkLam Ty t := match Ty with 
| tSort _ => tLambda (mkNamed "A") Ty t
| _ => tLambda (mkNamed "x") Ty t
end.



Definition mkProdName na T u := (* \TODO use mkProdName in files *)
tProd (mkNamed na) T u.

Close Scope string_scope.

Definition mkApp (u : term) (l : list term) :=
tApp u l.

Definition mkApp_singl t u :=
mkApp t [u].

Fixpoint get_constructors_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => None 
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then let loind := ind_bodies mind in let list_ctors_opt := match loind with 
| nil => None
| x :: xs => Some (x.(ind_ctors))
end in list_ctors_opt else get_constructors_inductive I e'
                                  | _ => get_constructors_inductive I e'
                               end)    
    end
end
| _ => None
end.



(* Get the pair of the number of parameters of an inductive and the list of their types *)
Fixpoint get_info_params_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => None 
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then let prod := (ind_npars mind, tr_map (fun x => x.(decl_type)) (ind_params mind)) in Some prod else get_info_params_inductive I e'
                                  | _ => get_info_params_inductive I e'
                               end)    
    end
end
| _ => None
end.



(** computes the list of one_inductive_body's in a term I which is a reified inductive **)
(* \TODO should problably also test the equality between paths, not only on the names *)
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



Definition no_prod (t: term) := match t with 
  | tProd _ _ _ => false 
  | _ => true
end.

Fixpoint no_prod_after_params (t : term) (p : nat) := match t with
   | tProd _ _ u => match p with 
                   | 0 => false 
                   | S n' => no_prod_after_params u n'
                  end
  | _ => true
end.
 
Definition find_index_constructor_of_arity_zero (o : option (list ((ident × term) × nat))) := match o with
  | None => None
  | Some l => let fix aux l' acc := 
      match l' with 
        | nil => None
        | x :: xs => if Nat.eqb (x.2) 0 then (Some acc) else aux xs (acc + 1)
      end in aux l 0
  end.

Definition no_app t := match t with
| tApp u l => (u, l)
| _ => (t, [])
end.

Definition get_info_inductive (I : term) := 
let p := no_app I in match p.1 with
| tInd ind inst => Some (ind, inst)
| _ => None
end.

Ltac remove_option o := match o with
| Some ?x => constr:(x)
| None => fail "None"
end.

Definition get_nth_constructor (I : term) (n : nat) : term := 
let g := get_info_inductive I in match g with 
  | None => impossible_term_reif
  | Some (ind, inst) => tConstruct ind n inst
end. 

Definition mkApp_list (u : term) (l : list term) :=
tApp u l.


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
(* \TMP
 | cons y' _ => let z := y'.(ind_ctors) in let u := 
subst_type_constructor_list z v in u
*)


Fixpoint get_decl (e : global_env) := match e with 
| [] => []
| x :: e' => match (snd x) with
      | ConstantDecl u => match u.(cst_body) with
            | Some v => v :: get_decl e'
            | None => get_decl e'
            end
      | InductiveDecl u => get_decl e'
      end
end.

(* Check is a MetaCoq term is a sort which is not Prop *)
Definition is_type (t : term) := match t with
                                 | tSort s => negb (Universe.is_prop s)
                                 |_ => false
                                  end.

(* Get the nb of construcors of a reified inductive type if we have the reified global environment *)
Definition get_nb_constructors i Σ := 
match i with 
| tInd indu _ => match lookup_env Σ indu.(inductive_mind) with
                | Some (InductiveDecl decl) => match ind_bodies decl with 
                          | nil => 0
                          | x :: _ => Datatypes.length (ind_ctors x)
                          end
                | _ => 0
end
| _ => 0
end.


(** Generic tactics **) 

Ltac prove_hypothesis H :=
repeat match goal with
  | H' := ?x : ?P |- _ =>  lazymatch P with 
                | Prop => let def := fresh in assert (def : x) by 
(intros; rewrite H; auto) ;  clear H'
          end
end.

Ltac get_head x := lazymatch x with ?x _ => get_head x | _ => x end.

Ltac get_tail x := 
let rec get_tail_aux x p := 
lazymatch x with ?y ?z => get_tail_aux y (z, p) | _ => p end
in get_tail_aux x impossible_term.

(* [inverse_tactic tactic] succceds when [tactic] fails, and the other way round *)
Ltac inverse_tactic tactic := try (tactic; fail 1).

(* [constr_neq t u] fails if and only if [t] and [u] are convertible *)
Ltac constr_neq t u := inverse_tactic ltac:(constr_eq t u).

Ltac is_not_in_tuple p z := 
lazymatch constr:(p) with
| (?x, ?y) => is_not_in_tuple constr:(x) z ; is_not_in_tuple constr:(y) z
| _ => constr_neq p z 
end.

Ltac notHyp T  :=
repeat match goal with
  | [H : _ |- _] => let U := type of H in constr_eq U T ; fail 2
end.

(* A tactic version of if/else *)
Ltac if_else_ltac tac1 tac2 b := lazymatch b with
  | true => tac1
  | false => tac2
end.

(* Returns the tuple of hypothesis in a local context *)
Ltac hyps := 
match goal with
| H : _ |- _ => let _ := match goal with _ => let T := type of H in let U := type of T in
constr_eq U Prop ; revert H end in let acc := hyps in 
let _ := match goal with _ => intro H end in constr:((H, acc))
| _ => constr:(impossible_term)
end.

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] => let U := type of X in constr_eq U Prop ;
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

(** Tactics to work on quoted MetaCoq terms **)

Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.

Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t) ltac:(fun x => (pose  x as idn))).

(* Allows to use MetaCoq without continuations *)
Ltac metacoq_get_value p :=
  let id := fresh in
  let _ := match goal with _ => run_template_program p
  (fun t => pose (id := t)) end in
  let x := eval cbv delta [id] in id in
  let _ := match goal with _ => clear id end in
  x.

(* Examples for metacoq_get_value *)
Goal True.
let x := metacoq_get_value (tmQuoteRec bool) in pose x.
let x := metacoq_get_value (tmQuote bool) in pose x.
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquote x) in pose y.
let x := metacoq_get_value (tmQuote 0) in let y := metacoq_get_value (tmUnquoteTyped nat x) in pose y.
Abort.

Ltac get_nb_constructors_tac i id :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => let n := 
eval cbv in (get_nb_constructors i_reif_rec.2 i_reif_rec.1) in
pose (id := n)).

(*********************)
(* \TODO temporary inserts before putting order into auxiliary functions 
         These functions should be removed from interp_alg_types *)

Definition dom_list_f ( B  :  term) (n : nat)  := 
  (* takes a type B := Prod A1 ... An . B'  and outputs (B,[A1; ... ; An]), at least if no dependencies *)
  (* does not handle debruijn indices *)
  let fix dlaux B n acc :=
  match n with
  | 0 => (B,tr_rev acc) 
  | S n => match B with
          | tProd na A B' =>  dlaux B' n (A :: acc)
          | _ => (B,[]) (* this case shouldn't happen *)
          end            
  end
  in dlaux B n [].

Locate subst10.

Definition switch_inductive ( indu : inductive) (i : nat) :=
  match indu with 
  | {| inductive_mind := kn ; inductive_ind := k |} => {| inductive_mind := kn ; inductive_ind := i |}
end.





Definition debruijn0 (indu : inductive) (n : nat) (u : Instance.t ) (B : term) :=
  let fix aux1 k acc :=
    match k with
    | 0 => acc 
    | S k => aux1 k  ((tInd (switch_inductive indu k) u):: acc) 
    end in
  let oind_list := tr_rev (aux1 n [] )
  in  subst0 oind_list B .



(***********************)

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
(* global_env × term -> list term *)
(* \TODO compare list_types_of_each_constructor and the 3rd proj of get_ctors_and_types_i *)




(** get_list_of_rel_lifted n l = [ tRel (n + l -1)) ; tRel (n + l -2 ) ; ... ; tRel l]
   (list of length n)
   linear 
**)
Definition get_list_of_rel_lifted (n l : nat) :=
  let  fix aux n  k acc  :=
  match n with
   | 0 => acc 
   | S n => aux n  (S k) ((tRel k)::acc)
   end
   in aux n  l [].
  


(* Reifies a term and calls is_type *)
Ltac is_type_quote t := let t' := eval hnf in t in let T :=
metacoq_get_value (tmQuote t') in if_else_ltac idtac fail ltac:(eval compute in (is_type T)).


Ltac is_type_quote_bool t := let t' := eval hnf in t in let T :=
metacoq_get_value (tmQuote t') in constr:(is_type T).

Fixpoint list_of_subterms (t: term) : list term := match t with
| tLambda _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tProd _ Ty u => t :: (list_of_subterms Ty) ++ (list_of_subterms u)
| tLetIn _ u v w => t :: (list_of_subterms u) ++ (list_of_subterms v) ++ (list_of_subterms w)
| tCast t1 _ t2 => t :: (list_of_subterms t1) ++ (list_of_subterms t2)
| tApp u l => t :: (list_of_subterms u) ++ (List.flat_map list_of_subterms l)
| tCase _ t1 t2 l => t:: (list_of_subterms t1) ++ (list_of_subterms t2) ++ 
(List.flat_map (fun x => list_of_subterms (snd x)) l)
| tFix l _  => t :: (List.flat_map (fun x => list_of_subterms (x.(dbody))) l)
| tCoFix l _ => t :: (List.flat_map (fun x => list_of_subterms (x.(dbody))) l)
| _ => [t]
end.

Definition filter_closed (l: list term) := List.filter (closedn 0) l.


Ltac get_list_of_closed_subterms t := let t_reif := metacoq_get_value (tmQuote t) in 
let l := eval cbv in (filter_closed (list_of_subterms t_reif)) in l. 

Ltac return_unquote_tuple_terms l := let rec aux l acc :=
match constr:(l) with
| nil => constr:(acc)
| cons ?x ?xs => 
  let y := metacoq_get_value (tmUnquote x) in 
  let u := constr:(y.(my_projT2)) in 
  let w := eval hnf in u in
  let T := type of w in 
  let b0 := ltac:(is_type_quote_bool T) in 
  let b := eval hnf in b0 in
    match b with 
    | true => (aux xs (pair w acc)) 
    | false => aux xs acc
    end
end
in aux l impossible_term.

Ltac return_tuple_subterms_of_type_type := match goal with
|- ?x => let l0 := (get_list_of_closed_subterms x) in let l := eval cbv in l0 in return_unquote_tuple_terms l
end.

Goal forall (A: Type) (x:nat) (y: bool) (z : list A), y = y -> z=z -> x = x.
let t := return_tuple_subterms_of_type_type in pose t.
Abort.

Goal forall (A : Type) (l : list A), Datatypes.length l = 0 -> l = nil.
let t := return_tuple_subterms_of_type_type in pose t.
Abort.


