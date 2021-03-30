Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.

Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

MetaCoq Quote Definition unit_reif := unit.

MetaCoq Quote Definition eq_reif := Eval cbn in @eq.

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

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



Definition get_type_constructor (c : term):=
match c with
| tConstruct ind _ _ => let kn := ind.(inductive_mind) in 
tInd {| inductive_mind := kn ; inductive_ind := 0 |} []
| _ => unit_reif
end.



(* does not work for mutual inductives *)
Ltac list_ctors_and_types I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval compute in y.(ind_ctors) in pose z
| None => fail
end).


(*  in the type of the constructor we need to susbtitute the free variables by the corresponding inductive type *)

Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (T : term) :=
match l with 
| nil => nil
| ((_, Ty), _):: l' => (subst10 T Ty) :: (subst_type_constructor_list l' T)
end.


Ltac list_types_of_ctors I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval cbv in y.(ind_ctors) in 
let v := eval cbv in t.2 in let u := eval cbv in (subst_type_constructor_list z v) in
pose u
| None => fail 1
end).


Definition list_types_of_each_constructor t :=
let x := get_decl_inductive t.2 t.1 in match x with
| Some y => match y with 
          | nil => nil
          | cons y' l => let z := y'.(ind_ctors) in let v := t.2 in let u := 
subst_type_constructor_list z v in u
          end
| None => nil
end.


Definition get_info_inductive (I : term) := 
match I with
| tInd ind inst => Some (ind, inst)
| _ => None
end.


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => (get_list_of_rel n) ++ [tRel n]
end.


Fixpoint get_term_applied_aux (c : term) (T : term) (acc : list term) 
 :=
(* the constructor reified c and its type, acc is the type of each arguments *)
match T with 
| tProd _ Ty Ty' => ((get_term_applied_aux c Ty' (Ty :: acc)).1, 
(get_term_applied_aux c Ty' (Ty :: acc)).2)
| _ => let n := (List.length acc) in if Nat.eqb n 0 then (c, acc) else
 (tApp c (get_list_of_rel (List.length acc)), acc)
end.

Definition get_term_applied (c : term) (T : term) := get_term_applied_aux c T [].


Definition get_term_applied_eq (c : term) (I : term) (type_of_c : term) (t' : term)
 := mkEq I (get_term_applied c type_of_c).1 t'.

Definition get_fun_with_constructor_applied_eq (f_reif : term) (c : term) (codomain : term)
(type_of_c : term) (t' : term) :=
mkEq codomain (tApp f_reif [(get_term_applied c type_of_c).1]) t'.

Fixpoint produce_trivial_eq (c : term) (type_of_c : term) 
(type_of_args : list term) (I : term) := match type_of_args with
| [] => get_term_applied_eq c I type_of_c (get_term_applied c type_of_c).1
| x :: xs => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (produce_trivial_eq c type_of_c
xs I)
end.



Definition produce_eq_tcase (f_reif : term) (c : term) (type_of_c : term) (codomain : term) 
(I : term) (case : term) := 
(*here, case is the case suitable for the given constructor c *)
let type_of_args := (get_term_applied c type_of_c).2 in 
let fix aux (f_reif : term) (c : term) (type_of_c : term) codomain (I : term) (case : term) (type_of_args : list term)
:= match type_of_args with
| [] => get_fun_with_constructor_applied_eq f_reif c codomain type_of_c (get_term_applied case type_of_c).1
| x :: xs => tProd {| binder_name := nAnon; binder_relevance := Relevant |} x (aux f_reif c type_of_c codomain I case xs)
end
in aux f_reif c type_of_c codomain I case type_of_args.


(* find the right case of a tCase given its index *)
Fixpoint find_tCase (n : nat) (t : term) := match t with
| tLambda _ _ t' => find_tCase n t'
| tCase _ _ _ l => (nth n l (0, unit_reif)).2
| _ => unit_reif
end.

Definition find_index_constructor (c : term) :=
match c with
| tConstruct _ n _ => n
| _ => 0
end.


Ltac produce_eq_tCase f c := let f_unfold := eval unfold f in f in match type of f with
| ?A -> ?B => quote_term A (fun I => quote_term B (fun codomain => 
 let type_of_c := type of c in quote_term c (fun c =>
quote_term type_of_c (fun type_of_c =>
quote_term f (fun f_reif => quote_term f_unfold (fun f_unfold_reif => 
let n := eval cbv in (find_index_constructor c) in let case := eval cbv in 
(find_tCase n f_unfold_reif) in
let x := eval cbv in (produce_eq_tcase f_reif c type_of_c codomain I case) in 
run_template_program (tmUnquote x) ltac:(fun x => let z := eval hnf in x.(my_projT2) in let H := fresh in
assert z as H ; simpl ; try reflexivity)
))))))
| _ => fail
end.


(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1 in let inst := J.2 in let fix aux n' ind' inst' :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst') ++ [tConstruct ind' m inst']
end
in aux n J.1 J.2
| None => []
end.

Fixpoint find_list_tCase (t : term) := match t with
| tLambda _ _ t' => find_list_tCase t'
| tCase _ _ _ l => List.map snd l
| _ => []
end.

Definition eliminate_pattern_matching (f : term) (codomain : term) (I_rec : program) 
(case : list term) := 
let I := I_rec.2 in 
let l := list_types_of_each_constructor I_rec in let n := length l in
let l' := get_list_ctors_tConstruct I n in
let fix aux f codomain l l' case I  :=
match (l , (l', case)) with
| (nil, _) | (_ , (_, nil)) | (_, (nil, _)) => nil
| (x :: xs, (y :: ys, z :: zs)) => aux f codomain xs ys zs I ++ 
[ produce_eq_tcase f y x codomain I z]
end
in aux f codomain l l' case I.


Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.


Ltac produce_eq_tCase_fun f := 
match type of f with
| ?A -> ?B => quote_term B (fun codomain => 
let f_unfold := eval unfold f in f in quote_term f_unfold (fun f_unfold_reif =>
let l := eval cbv in (find_list_tCase f_unfold_reif) in
run_template_program (tmQuoteRec A) (fun I_rec => quote_term f (fun f => 
let list := eval cbv in (eliminate_pattern_matching f codomain I_rec l) in unquote_list list))))
| _ => fail 1
end.

Definition get_fst_arg t := 
match t with
| tApp _ l => match l with 
              | nil => unit_reif
              | x :: xs => x
              end
| _ => unit_reif
end.

Definition get_snd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ]=> unit_reif
              | _ :: (y :: xs) => y
              end
| _ => unit_reif
end.

Definition get_thrd_arg t := 
match t with
| tApp _ l => match l with 
              | [] | [ _ ] | [_ ; _ ]=> unit_reif
              | _ :: (y :: ( z :: xs)) => z
              end
| _ => unit_reif
end.


Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].

Fixpoint remove_forall t := match t with
| tProd _ _ u => remove_forall u
| _ => t
end.


Ltac unquote_requote_rec t :=
run_template_program (tmUnquote t) (fun t => 
let x:= eval hnf in t.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun t => idtac t)).



Definition erase_forall (H : term) := match H with
| tProd _ Ty t => (Ty, t)
| _ => (unit_reif, unit_reif)
end.

Definition head (t : term) :=
match t with 
| tApp x y => x 
| _ => unit_reif 
end.



(* Simplification : H must be of the form forall x, f x = match x with ... *)
Ltac produce_eq_tCase_hyp H := 

let T := type of H in 
quote_term T (fun T => 
let eq := eval cbv in (erase_forall T).2 in 
let Ind := eval cbv in (erase_forall T).1 in 
run_template_program (tmUnquote Ind) (fun Ind => 
let x:= eval hnf in Ind.(my_projT2) in run_template_program (tmQuoteRec x) 
ltac:(fun I_rec =>  
let f_fold := eval cbv in (head (get_snd_arg eq)) in
let f_unfold_reif := eval cbv in (get_thrd_arg eq) in
let codomain := eval cbv in (get_fst_arg eq) in 
let l := eval cbv in (find_list_tCase f_unfold_reif) in
let list := eval cbv in (eliminate_pattern_matching f_fold codomain I_rec l) in unquote_list list))).


Ltac prove_hypothesis :=
 match goal with
  | H := ?x : ?P |- _ => lazymatch P with 
                | id _ => fail 
                | Prop => assert x by (try reflexivity) ; change P with (id P) in H ; clear H
             end
          end.

(* when a hypothesis is of type id Q, replaces it by Q *)
Ltac eliminate_id :=
  match goal with
    | H : ?P |- _ =>
      lazymatch P with
        | id ?Q => change P with Q in H
        | _ => fail
  end
end.

Ltac eliminate_pattern_matching_ind f :=
produce_eq_tCase_fun f ; repeat prove_hypothesis ; repeat eliminate_id.

Ltac eliminate_pattern_matching_hyp H :=
 produce_eq_tCase_hyp H ; repeat prove_hypothesis ; repeat eliminate_id.










