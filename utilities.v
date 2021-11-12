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
Require Import MetaCoq.Template.All.

Require Import String. 

MetaCoq Quote Definition unit_reif := unit.

Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).


Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.

Ltac prove_hypothesis H :=
repeat match goal with
  | H' := ?x : ?P |- _ =>  lazymatch P with 
                | Prop => let def := fresh in assert (def : x) by 
(intros; rewrite H; auto) ;  clear H'
          end
end.


(* [inverse_tactic tactic] succceds when [tactic] fails, and the other way round *)
Ltac inverse_tactic tactic := try (tactic; fail 1).

(* [constr_neq t u] fails if and only if [t] and [u] are convertible *)
Ltac constr_neq t u := inverse_tactic ltac:(constr_eq t u).


Ltac is_not_in_tuple p z := 
lazymatch constr:(p) with
| (?x, ?y) => is_not_in_tuple constr:(x) z ; is_not_in_tuple constr:(y) z
| _ => constr_neq p z 
end.


(* Nothing about inductives for now *)
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


Ltac rec_quote_term t idn := (run_template_program (tmQuoteRec t) ltac:(fun x => (pose  x as idn))).



MetaCoq Quote Definition eq_reif := Eval cbn in @eq.

Ltac notHyp T  :=
repeat match goal with
  | [H : _ |- _] => let U := type of H in constr_eq U T ; fail 2
end.

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkProd T u :=
tProd {| binder_name := nAnon; binder_relevance := Relevant |} T u.

Definition mkProdName na T u :=
tProd {| binder_name := nNamed na ; binder_relevance := Relevant |} T u.

Definition mkApp t u :=
tApp t [u].

(* A tactic version of if/else *)
Ltac if_else_ltac tac1 tac2 b := lazymatch b with
  | true => tac1
  | false => tac2
end.

(* Check is a MetaCoq term is a sort which is not Prop *)
Definition is_type (t : term) := match t with
                                 | tSort s => negb (Universe.is_prop s)
                                 |_ => false
                                  end.



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

Ltac get_nb_constructors_tac i id :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => let n := 
eval cbv in (get_nb_constructors i_reif_rec.2 i_reif_rec.1) in
pose (id := n)).

(* Returns the tuple of hypothesis in a local context *)
Ltac hyps := 
match goal with
| H : _ |- _ => let _ := match goal with _ => let T := type of H in let U := type of T in
constr_eq U Prop ; revert H end in let acc := hyps in 
let _ := match goal with _ => intro H end in constr:((H, acc))
| _ => constr:(unit)
end.

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
ident na.2) then let prod := (ind_npars mind, List.map (fun x => x.(decl_type)) (ind_params mind)) in Some prod else get_info_params_inductive I e'
                                  | _ => get_info_params_inductive I e'
                               end)    
    end
end
| _ => None
end.

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

Fixpoint no_prod_after_params (t : term) (npars : nat) := match t with
   | tProd _ _ u => match npars with 
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

Inductive impossible_term :=.
MetaCoq Quote Definition impossible_term_reif := impossible_term.

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

Definition get_list_of_rel (n : nat) :=  let fix aux n k acc :=
match n with 
| 0 => acc
| S n' => aux n' (k + 1) ((tRel k) :: acc)
end in aux n 0 nil.

Definition get_list_of_rel_lifted (n l : nat) := let fix aux n k acc :=
match n with 
| 0 => acc
| S n' => aux n' (k + 1) ((tRel (k + l)) :: acc)
end in aux n 0 nil.


Fixpoint flatten_aux {A} (l : list (list A)) (acc : list A) := 
match l with 
| nil => acc
| x :: xs => let fix aux l acc' := match l with
              | nil => acc'
              | y :: ys => aux ys (acc' ++ [y]) end in
              flatten_aux xs (acc ++ (aux x []))
end.

Definition flatten {A} (l : list (list A)) := flatten_aux l  [].


