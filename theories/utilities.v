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


MetaCoq Quote Definition and_reif := Logic.and.


MetaCoq Quote Definition True_reif := True.

MetaCoq Quote Definition False_reif := False.

MetaCoq Quote Definition eq_reif := @eq.

MetaCoq Quote Definition bool_reif := bool. 

MetaCoq Quote Definition Z_reif := Z.

MetaCoq Quote Definition nat_reif := nat.

Inductive impossible_term :=.
MetaCoq Quote Definition impossible_term_reif := impossible_term.

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


(** Tail-recursive (actually linear) version of List.length **)
Definition leng {A : Type} (l : list A ) :=
  let fix aux l acc :=
  match l with
  | [] => acc
  | _ :: l0 => aux l0 (S acc) 
  end
  in aux l 0.


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

(** rec_acc_add [n_1 ; .... ; n_c ] = [n ]
**)
Definition rev_acc_add l :=
let fix aux l s acc :=
match l with
  | [] => acc
  | x :: l => let s' := x+s in aux l s'  (s' :: acc)
end in aux l 0 [].

Goal False.
let x := constr:(rev_acc_add [2 ; 3 ; 8]) in pose x as kik ; compute in kik.
Abort.



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


(* mkProd [A1 ; .... ; An ] t = tProd _ An. ... tProd _ A1. t   (reverts list) *)
(* warning: t should have been previously lifted if necessary*)
Fixpoint mkProd_rec (l : list term)  (t: term) := 
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd (mkNamed "x")  x t)
end.


(* same thing but one provides a name for the bound variables *)
Fixpoint mkProd_rec_n (na : ident) (l : list term)  (t: term) := 
(* warning: t should have been previously lifted *)
match l with 
| [] => t 
| x :: xs => mkProd_rec_n na xs (tProd (mkNamed na)  x t)
end.



(** mkLam [A1 ; .... ; An ] t = Lam "x/A" An. ... tProd "x/A" A1. t   (reverts list) **)
(** tail-recursive **)
(* warning: t should have been previously lifted if necessary*)
Fixpoint mkLam_rec (l : list term)  (t: term) := 
match l with 
| [] => t 
| x :: xs => mkLam_rec xs (mkLam x t)
end.


Close Scope string_scope.


Definition mkImpl A B := tProd mkNAnon A (lift0 1 B). 


Definition mkNot (A :term) := mkImpl A False_reif.

Definition mkAnd (A B : term) := tApp and_reif [A ; B]. 

Definition mkOr (A B : term) := tApp or_reif [A ; B].


(** mkAnd_n [A1_reif ; ... ; An_reif ] = 
    the reification of (A1 /\ A2) /\ ... An) (associates to the left **)
(** tail-recursive (actually linear) *)
Definition mkAnd_n (l : list term) :=
  match l with
  | [] => True_reif
  | t0 :: l0 => 
  let fix aux l acc := match l with
  | [] => acc
  | t :: l => aux l (tApp and_reif (acc :: [t])) 
  end
  in aux l0 t0
  end.


(**  mkOr_n0 [A1_reif ; ... ; An_reif] produce the reification of(...(An \/ (A_{n-1}) ... A_2) \/ A_1)..)
     i.e. reverts list and associates to the *left* (better for SMTLib) **)
(**     tail-recursive **)
Definition mkOr_n (l : list term) :=
  match l with
  | [] => True_reif
  | t0 :: l0 => 
    let fix aux l acc := match l with
    | [] => acc
    | t :: l => aux l (tApp or_reif (acc :: [t])) 
    end
    in aux l0 t0
  end.

Definition mkApp (u : term) (l : list term) :=
tApp u l.

Definition mkApp_singl t u :=
mkApp t [u].




(* get_params_from_mind mind = (p , P) 
  where p is the number of parameters of mind and lP the list of the parameters types *in order*
  (note that mind.(ind_params)) stores the types in *reverse* order
*)
(* \TODO it would be perhaps better to recover the types of the parameters in the reverse order  *)
Definition get_params_from_mind mind :=
  let p := mind.(ind_npars) in 
  let l0 := tr_revmap (fun d => d.(decl_type)) mind.(ind_params)
in (p, l0).
(* \TODO maybe use this tactic in fo_prop_of_cons_tac *)


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

(* no_prod* do not seem to be used --> \TODO remove   *)
Fixpoint no_prod_after_params (t : term) (p : nat) := match t with
   | tProd _ _ u => match p with 
                   | 0 => false 
                   | S n' => no_prod_after_params u n'
                  end
  | _ => true
end.
 
(* does not seem to be used anywhere ---> \TODO remove *)
Definition find_index_constructor_of_arity_zero (o : option (list ((ident × term) × nat))) := match o with
  | None => None
  | Some l => let fix aux l' acc := 
      match l' with 
        | nil => None
        | x :: xs => if Nat.eqb (x.2) 0 then (Some acc) else aux xs (acc + 1)
      end in aux l 0
  end.

(* \TODO 
1) give a better name
2) see if it is really useful
*)
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
| None => fail "failure remove_option"
end.

Definition get_nth_constructor (I : term) (n : nat) : term := 
let g := get_info_inductive I in match g with 
  | None => impossible_term_reif
  | Some (ind, inst) => tConstruct ind n inst
end. 

(* \TODO : not useful --> remove *)
Definition mkApp_list (u : term) (l : list term) :=
tApp u l.


(* Implements beta reduction *)
(* \TODO : not used --> remove *)
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
(* \seems inefficient, and better handled by debruijn0 --> remove \TODO *)
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

Ltac generalize_dependent_tuple p := 
lazymatch constr:(p) with
| (?x, ?y) => generalize_dependent_tuple constr:(x) ; generalize_dependent_tuple constr:(y)
| impossible_term => idtac
| ?x => try (generalize dependent x)
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


(* given an 'inductive' and i, the rank of an inductive body, 
  outputs the 'inductive' associated to the same inductive type, whose rank is i 
*)
Definition switch_inductive ( indu : inductive) (i : nat) :=
  match indu with 
  | {| inductive_mind := kn ; inductive_ind := k |} => {| inductive_mind := kn ; inductive_ind := i |}
end.

(** in an inductive type I, the type of the constructors use de Bruijn indices to denote the inductive bodies of I.
For instance, for I = list, which has a unique inductive body, the type of :: is represented with: 
cons_type_decl := tProd "A" Type_reif (tProd _ (tRel 0) (tProd _ (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2])))
where the 1st occurrence of Rel 2 and the occurrence of Rel 3 represent the type list
See the term list_oind in aux_fun_tests.v.
Then if B is the type of the constructor as it is reified in the inductive type I, debruijn0 .... B outputs the real type of the constructor
e.g. debruijn0 (list_indu) 1 [] cons_type_decl gives
   tProd "A" Type_reif (tProd _ (tRel 0) (tProd _ (tApp list_reif [tRel 1]) (tApp list_reif [tRel 2])
   i.e. the reification forall (A: Type), A -> list A -> list A 
   where list_reif is the reification for list
**) 
(** tail-recursive **)
Definition debruijn0 (indu : inductive) (no : nat) (u : Instance.t ) (B : term) :=
  let fix aux1 k acc :=
    match k with
    | 0 => acc 
    | S k => aux1 k  ((tInd (switch_inductive indu k) u):: acc) 
    end in
  let oind_list := tr_rev (aux1 no [] )
  in  subst0 oind_list B .



(***********************)



(** Rel_list n l = [ tRel (n + l -1)) ; tRel (n + l -2 ) ; ... ; tRel l]
   (list of length n)
**) (** linear **)
Definition Rel_list (n l : nat) :=
  let  fix aux n  k acc  :=
  match n with
   | 0 => acc 
   | S n => aux n  (S k) ((tRel k)::acc)
   end
   in aux n l [].




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

(* To reason on size of terms *)

Definition list_size :=
fun {A : Type} (size : A -> nat) =>
fix list_size (l : list A) : nat :=
  match l with
  | [] => 0
  | a :: v => S (size a + list_size v)
  end.

Definition def_size := 
fun (size : term -> nat) (x : def term) =>
size (dtype x) + size (dbody x).

Definition mfixpoint_size := 
fun (size : term -> nat) (l : mfixpoint term) =>
list_size (def_size size) l.


Fixpoint size (t : term) :=
match t with
| tEvar _ args => S (list_size size args)
| tProd _ A B => S (size A + size B)
| tLambda _ T M => S (size T + size M)
| tLetIn _ b t0 b' => S (size b + size t0 + size b')
| tApp u l => S (size u + (List.fold_left (fun acc x => size x + acc) l 0))
| tCase _ p c brs => S (size p + size c + list_size
           (fun x : nat * term =>
            size x.2) brs)
| tProj _ c => S (size c)
| tFix mfix _ | tCoFix mfix _ => S (mfixpoint_size size mfix)
| _ => 1
end.

