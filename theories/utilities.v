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

From MetaCoq Require Import All. 
Require Import List.
Import ListNotations.
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

Inductive default :=.
MetaCoq Quote Definition default_reif := default.


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


Definition mkNamedtry := mkNamed (("B"%bs) : ident).

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkProd T u :=
tProd mkNAnon T u.

Definition mkLam Ty t := match Ty with 
| tSort _ => tLambda (mkNamed "A"%bs) Ty t
| _ => tLambda (mkNamed "x"%bs) Ty t
end.



Definition mkProdName na T u := (* \TODO use mkProdName in files *)
tProd (mkNamed na) T u.


(* mkProd [A1 ; .... ; An ] t = tProd _ An. ... tProd _ A1. t   (reverts list) *)
(* warning: t should have been previously lifted if necessary*)
Fixpoint mkProd_rec (l : list term)  (t: term) := 
match l with 
| [] => t 
| x :: xs => mkProd_rec xs (tProd (mkNamed "x"%bs)  x t)
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


Definition default_error_kn := (MPfile [], "error"%bs).

Definition kername_term (t : term) :=
match t with
| tConst kn _ => kn
| tInd indu insts => indu.(inductive_mind)
| _ => default_error_kn
end.

Definition lookup (e : global_env) (i : term) :=
let decls := e.(declarations) in
let kn := kername_term i in
let fix aux decls kn := 
match decls with
| (kn', gdecl) :: decls' => if eq_kername kn kn' then Some gdecl else aux decls' kn
| [] => None
end in aux decls kn.


Definition info_inductive (e : global_env) (i : term) :=
let res := lookup e i in 
match res with
| Some (ConstantDecl _) => None
| Some (InductiveDecl mind) => Some mind
| None => None
end.

Definition default_body :=
{|
               ind_name := "default"%bs;
               ind_indices := [];
               ind_sort := Universe.of_levels (inl PropLevel.lProp);
               ind_type :=
                 tSort (Universe.of_levels (inl PropLevel.lProp));
               ind_kelim := IntoAny;
               ind_ctors := [];
               ind_projs := [];
               ind_relevance := Relevant
             |}.


(** if I is a nonmutual inductive, returns the pair between the number of its parameters 
and the list of its constructor bodies **)
Definition info_nonmutual_inductive (e : global_env) (i : term) :=
let res := info_inductive e i in
match res with
| Some mind =>  (mind.(ind_npars), (hd default_body mind.(ind_bodies)).(ind_ctors))
| None => (0, [])
end.


Definition no_prod (t: term) := match t with 
  | tProd _ _ _ => false 
  | _ => true
end.

Definition dest_app t := match t with
| tApp u l => (u, l)
| _ => (t, [])
end.

Definition get_info_inductive (I : term) := 
let p := dest_app I in match p.1 with
| tInd ind inst => Some (ind, inst)
| _ => None
end.

Ltac remove_option o := match o with
| Some ?x => constr:(x)
| None => fail "failure remove_option"
end.

Definition get_nth_constructor (I : term) (n : nat) : term := 
let g := get_info_inductive I in match g with 
  | None => default_reif
  | Some (ind, inst) => tConstruct ind n inst
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

Fixpoint get_type_constructors (l : list constructor_body) :=
match l with
| [] => nil
| x :: xs => cstr_type x :: get_type_constructors xs
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
in get_tail_aux x default.

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
| default => idtac
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
| _ => constr:(default)
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
