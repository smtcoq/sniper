From MetaCoq.Template Require Import All.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Lia.
From SMTCoq Require Import SMTCoq.
Require Import add_hypothesis_on_parameters.
Require Import compdec_plugin.
Require Import linearize_plugin.
Require Import utilities.
Import MCMonadNotation.

Unset MetaCoq Strict Unquote Universe Mode.

(** Auxiliaries functions *)

Definition all_type_to_fresh := fun t =>
match t with
| tSort s => if negb (is_prop s) then tSort (sType fresh_universe) else t
| _ => t
end.

Definition get_args_inductive_fresh_types (e : global_env) (i : term) :=
let res := get_args_inductive e i in 
List.map all_type_to_fresh res.

Definition params_inductive (e : global_env) (i : term) :=
let info := info_inductive e i in
match info with
| None => []
| Some inf => rev (List.map (fun x => all_type_to_fresh (x.(decl_type))) inf.(ind_params))
end. 

Definition get_type_of_args_of_each_constructor (e : global_env) (i: term) :=
let res := info_nonmutual_inductive e i in
let npars := res.1 in
let constructors := res.2 in
let fix aux constructors :=
match constructors with
| [] => []
| c :: cs => let c' := c.(cstr_args) in
  let fix aux' c nb_lift :=
    match c with 
   | arg :: args => subst1 i nb_lift arg.(decl_type) :: aux' args (nb_lift - 1)
 (* i should be applied to its parameters *)
   | [] => []
   end in aux' c' (npars + Datatypes.length c' - 1) :: aux cs 
end
in aux constructors.

Definition types_of_args_ctors (e : global_env_ext) (i : term) :=
let res := info_nonmutual_inductive e.1 i in rev (
match res with
| (npars, ctors) => 
let fix aux npars ctors :=
  match ctors with
  | [] => []
  | c :: cs =>(*  let cargs := c.(cstr_args) in List.map (fun x => try_infer e cargs x.(decl_type)) cargs
:: aux npars cs *) let cargs := c.(cstr_args) in 
               let nb_args := Datatypes.length cargs in
               (mapi (fun n x => subst1 i (npars + nb_args - (S n)) x.(decl_type)) cargs) :: (aux npars cs)
  end in  (aux npars ctors)
end).


Definition list_ctors_applied_to_params 
(e : global_env)
(I : term) 
(lpars : list term) :=
let res := info_nonmutual_inductive e I in
let constructors := res.2 in
let nb_construct := Datatypes.length constructors in
match I with
| tInd ind inst => let fix aux ind inst lpars nb_construct :=
      match nb_construct with
    | S n' => tApp (tConstruct ind n' inst) lpars :: aux ind inst lpars n'
    | 0 => nil 
    end in aux ind inst lpars nb_construct
| _ => []
end.


(** Unfication algorithm **)

Inductive option_unif (A : Type) : Type :=
| failure : option_unif A
| continue : nat -> term -> option_unif A
| some : A -> option_unif A.

Arguments some {A} a.
Arguments failure {A}.
Arguments continue {A}.

Definition mapping := list (nat * nat).

Fixpoint replace_in_mapping (i j : nat) (m : mapping) :=
match m with
| [] => [(i, j)]
| (i', j') :: m' => if Nat.eqb i i' then (i', j) :: m' else 
(i', j') :: (replace_in_mapping i j m')
end.

Definition add_variable_in_mapping (i j : nat) (m : option_unif mapping) :=
match m with
| failure => failure 
| continue db t => continue db t
| some m' => 
(* if in_mapping i j m' =? 0 then some ((i, j) :: m') else 
if in_mapping i j m' =? 1 then some m' else
if in_mapping i j m' =? 2 then failure else some ((i, j) :: m')  *)
some (replace_in_mapping i j m')
end.

Fixpoint lift_mapping (nb_lift : nat) (m : mapping) :=
match m with
| (i, j) :: m' => (i + nb_lift, j) :: lift_mapping nb_lift m'
| [] => []
end.

Definition dumb_term := tVar "dumb_term"%bs.

Fixpoint list_of_dumb_term (n : nat) :=
match n with
| 0 => []
| S n' => dumb_term :: list_of_dumb_term n'
end.

(* Giving two terms constitued only of applications and variables, 
we try to unify them and return a mapping of De Brujin indexes.
We have three cases:
- the terms are not unifiable, we return a failure
- the terms are partially unifiable, we return the constructor continue 
and the De Brujin index of the variable which should be matched on 
- the terms are unifiable: we return the mapping of De Brujin indexes
This mapping will be useful to know on which variables the premises of a constructor should 
be applied 
In order to avoid the problem of parameters, we introduce holes (= dumb_term) in our terms *)

Fixpoint unify_aux (t1 t2 : term) (m : mapping) (fuel : nat) : option_unif mapping :=
match fuel with
| S n' =>
  match t1, t2 with
  | tRel i, tRel j => add_variable_in_mapping i j (some m)
  | tRel i, t => continue i t (* the unification is not finished : we need to pattern match on the variable of De Brujin
index i *)
  | tApp u1 [], u2 => unify_aux u1 u2 m n'
  | tApp u1 l, tRel _ => if (List.forallb (fun x => eqb_term x dumb_term) l) then unify_aux u1 t2 m n' else failure
  | tApp u1 l1, tApp u2 l2 => if eqb_term u1 u2 then unify_list_aux l1 l2 m n' else failure
  | tConstruct _ _ _, tRel _ => some m
  | _, _ =>  if eqb_term t1 t2 then (some m) else 
             if eqb_term t1 dumb_term then some m else failure
  end
| 0 => failure
end
with unify_list_aux (l1 l2 : list term) (m : mapping) (fuel : nat) : option_unif mapping :=
match fuel with
| S n' => 
  match l1, l2 with
  | x1 :: x1s, x2 :: x2s => let res := unify_aux x1 x2 m n' in
    match res with
    | failure => failure
    | continue db t => continue db t
    | some m' => unify_list_aux x1s x2s m' n'
    end
  | [], [] => some m
  | _, _ => failure
end
| 0 => failure
end.

Definition unify_mapping (t1 t2 : term) (m : mapping) := 
if eqb_term t1 t2 then some m else
let fuel := size t1 + size t2 in unify_aux t1 t2 m fuel.

Definition unify (t1 t2 : term) := 
let fuel := size t1 + size t2 in unify_aux t1 t2 [] fuel.

Fixpoint ex_list_bool {A : Type} (P : A -> bool) (l : list A) :=
match l with
| [] => false
| x :: xs => P x || ex_list_bool P xs
end. 

Definition get_fix_bodies (l : list (def term)) : list term :=
List.map (fun x => x.(dbody)) l. 

(* Returns true if the De Brujin index i occurs in t *)
Fixpoint contains_fuel (i : nat) (t : term) (fuel : nat) {struct fuel}:=
 match fuel with
 | 0 => false
 | S n =>
     match t with
     | tRel j => i =? j
     | tEvar n0 l =>  contains_fuel_list i l n
     | tCast u _ v =>  contains_fuel i u n ||  contains_fuel i v n
     | tProd _ Ty u | tLambda _ Ty u =>
          contains_fuel i Ty n ||  contains_fuel (S i) u n
     | tLetIn _ def Ty bod =>
          contains_fuel i Ty n ||  contains_fuel i def n ||  contains_fuel (S i) bod n
     | tApp u l =>  contains_fuel i u n ||  contains_fuel_list i l n
     | tCase _ _ trm br =>  contains_fuel i trm n ||  contains_fuel_branch i br n
     | tProj _ u =>  contains_fuel i u n
     | tFix fixs n' | tCoFix fixs n' => 
          let bods := get_fix_bodies fixs in
          let u := nth n' bods <% default %> in 
          contains_fuel i u n
     | _ => false 
     end
 end
with contains_fuel_list (i : nat) (l : list term) (fuel : nat) {struct fuel}:=
match fuel with
  | 0 => false
  | S n =>
    match l with
    | [] => false
    | x :: xs =>  contains_fuel i x n ||  contains_fuel_list i xs n
    end
  end
with contains_fuel_branch (i : nat) (l : list (branch term)) (fuel : nat) :=
match fuel with
  | 0 => false
  | S n =>
    match l with
    | [] => false
    | x :: xs =>  contains_fuel i x.(bbody) n ||  contains_fuel_branch i xs n
    end
end.


Fixpoint unify_list_mapping
(t: term) 
(pcs : list term) 
(ms : list mapping) : option (list (option_unif mapping)) :=
match pcs, ms with
  | [], [] => Some []
  | pc :: pcs, m :: ms => 
      let opt := unify_list_mapping t pcs ms in 
        match opt with
          | None => None
          | Some x => Some (unify_mapping t pc m :: x)
        end
  | _, _ => None
end.

Definition unifs_all_some (ms : list (option_unif mapping)) :=
List.forallb (fun x => match x with | some _ => true | _ => false end) ms.

Definition unifs_fst_some (ms : list (option_unif mapping)) :=
  match ms with
    | [] => false
    | x :: _ => (match x with some _ => true | _ => false end)
  end. 

Definition head_becomes_last {A : Type} (l : list A) :=
  match l with
    | [] => [] 
    | x :: xs => xs ++ [x]
  end.

Definition unifs_contains_failure (ms : list (option_unif mapping)) :=
List.existsb (fun x => match x with | failure => true | _ => false end) ms.

Fixpoint replace_mappings 
(ms : list mapping)
(lunif : list (option_unif mapping)) :=
match ms, lunif with
| m :: ms, (some m') :: lunif => m' :: replace_mappings ms lunif
| m :: ms, _ :: lunif => m :: replace_mappings ms lunif
| [], [] => []
| _, _ => []
end.

Definition contains (i : nat) (t : term) :=
let fuel := size t in 
contains_fuel i t fuel.

(** Informations contained in constructors, useful 
to get premises, conclusions and to initialize mappings *)


Record cstr_info : Type := mkCstr_info
{ 
  db_parameters : list nat; (* the de brujin indexes of parameters of the inductive type,
starting from the latest introduced *)
  premises : list term; (* the premises : all the conditions of type Prop *)
  conclusion : term (* the conclusion : should be the inductive applied to its arguments *)
}.

Fixpoint unlift_dbs (l : list nat) (t : term) :=
match l with
| [] => t
| x :: xs => subst1 (tVar "wrong_substitution"%bs) x (unlift_dbs xs t)
end.

(* Transforms the type of a constructor (parameters already introduced) 
into a record cstr_info *) 
Fixpoint find_cstr_info_aux
(dbpars : list nat) (* the db indexes of the parameters *)
(npars : nat) (* the number of parameters already introduced *)
(t : term) (* the term we analyse *)
(l : list term) (* the conclusion *)
(dbs : list nat) (* the db indexes corresponding to the non dependent hypothesis: we want to consider that
they are not introduced by an arrow because in the pattern matching, we will perform a boolean disjunction on all the hypotheses*)
 :=
match t with 
| tProd na Ty u => 
if Nat.eqb npars 0 then 
  if contains 0 u then 
    find_cstr_info_aux (List.map S dbpars) 0 u (List.map (fun x => lift 1 0 x) l) (List.map S dbs)
  else find_cstr_info_aux dbpars npars u ((unlift_dbs dbs Ty) :: l) (0::List.map S dbs)
else find_cstr_info_aux (0 :: List.map S dbpars) (npars - 1) u l (List.map S dbs)
(* here, t is a non dependent product so Ty should be considered as a premise *)
| _ => {| 
      db_parameters := dbpars; 
      premises := l;
      conclusion := unlift_dbs dbs t |}
end.

Definition find_cstr_info (npars : nat) (t : term) :=
find_cstr_info_aux [] npars t [] [].

Fixpoint find_mapping i m :=
match m with
| (j, k) :: m' => if i =? k then j else find_mapping i m'
| [] => i
end.

(* as we have strong hypothesis about the form
of the premises, t should be composed only of applications of constants, inductives or 
global variables and de brujin indexes *) 
Fixpoint replace_variables_fuel (t : term) (m : mapping) (fuel : nat) :=
match fuel with
| 0 => t
| S n =>
   match t with
   | tApp u v => tApp (replace_variables_fuel u m n) (replace_variables_list v m n)
   | tRel i => tRel (find_mapping i m)
   | _ => t
   end
end
with replace_variables_list (l : list term) (m : mapping) (fuel : nat) :=
match fuel with
| 0 => l
| S n =>
  match l with
  | [] => []
  | x :: xs => replace_variables_fuel x m n :: replace_variables_list xs m n
  end
end.


Definition replace_variables (t : term) (m : mapping) :=
let fuel := size t in 
replace_variables_fuel t m fuel. 
(* for debugging only !!  
let p := List.split m in
let l1 := List.map (fun x => tRel x) p.1 in
let l2 := List.map (fun x => tRel x) p.2 in
tApp (tVar "failure, the mapping is") 
(l1 ++ l2++ [tApp (tVar "term is") [(* replace_variables_fuel t m fuel *) t]]) *)

Fixpoint find_in_list_of_triple x (l : list (term*term*term)) :=
match l with
| [] => None
| (t1, t2, prf) :: xs => if eqb_term x t1 then Some t2 else find_in_list_of_triple x xs
end.

Definition get_boolean_reif (t: term) (l : list (term*term*term)) 
(* l is the list of terms that should be 
replaced with their boolean equivalent, we have (t1, t2, t1 <-> t2) *)
:= match t with
| tApp u [x ; y ; z] => if eqb_term <% @eq %> u 
                    then if eqb_term <%true%> z then y else t else t
| tApp u l1 => match find_in_list_of_triple u l with None => tApp u l1 | Some u' => tApp u' l1 end
| _ => t (* TODO : handle negation *)
end.

Definition return_premises (premises : list term) (m : mapping) (l : list (term*term*term)) := 
let fix aux prem m :=
match prem with
| pr :: prs => replace_variables (get_boolean_reif pr l) m :: aux prs m
| [] => []
end
in aux premises m.

Fixpoint build_orb (l : list term) :=
match l with
| [] => <% true %>
| [x] => x
| x :: xs => tApp <% orb %> [x ; build_orb xs]
end.

Fixpoint build_andb (l : list term) :=
match l with
| [] => <% true %>
| [x] => x
| x :: xs => tApp <% andb %> [x ; build_andb xs]
end.

Definition pos_tRels (l : list term) :=
  let fix aux l n :=
  match l with
    | x :: xs => 
        match x with
          | tRel i => (n - 1, i) :: aux xs (n - 1)      
          | _ => aux xs (n -1)
        end 
    | [] => []
    end in aux l (length l).


(* (* the information found about the constructor *)
(db_parameters : list nat)
(premises : list term)
(conclusion : term) => then, the conclusion is splitted to get patterns_conslusion *)

Definition split_conclusion (c: cstr_info) :  nat * (list term) * (list term) :=
let npars := Datatypes.length c.(db_parameters) in
let t := c.(conclusion) in (* the conclusion is the inductive applied to its arguments *)
match t with
| tApp (tRel n) l => let l' := List.skipn npars l in (n, List.firstn npars l, l')
| _ => (0,  [], [])
end.

Fixpoint build_list_of_vars (n : nat) :=
match n with
| 0 => []
| S n' => n' :: build_list_of_vars n' 
end.

Fixpoint only_variables (l : list term) : list nat :=
match l with
| (tRel n) :: xs => n :: only_variables xs
| _ :: xs => only_variables xs 
| [] => []
end.

(* lift 1 0 the first term, lift 2 0 the second term, ..., lift n 0 the nth term *)
Definition lift_list_ty (l : list term) :=
let fix aux l n :=
match l with
| [] => []
| x :: xs => lift n 0 x :: aux xs (S n) 
end 
in aux l 1. 

Record init_mapping :=
{ 
  ty_vars : list term;
  init_vars : list nat;
  mappings : list mapping;
  init_premises : list (list term);
  patterns : list (list term) }.

Definition transpose_aux {A: Type} (L : list (list A)) (n : nat) (a : A) : list A :=
  List.map (fun x => nth n x a) L. 

Fixpoint transpose_aux1 {A : Type} (L : list (list A)) (a : A) (n : nat) : list (list A) :=
  match n with
    | 0 => []
    | S n' => transpose_aux1 L a n' ++ [transpose_aux L n' a]
  end.

Definition transpose {A : Type} (L : list (list A)) a := 
  transpose_aux1 L a (length (hd [] L)).


Definition initial_mappings_aux 
(e : global_env)
(I : term)
(npars_args : nat) 
:=
let info := info_nonmutual_inductive e I in
let npars := info.1 in
let ctors := info.2 in
let ctors_type := List.map cstr_type ctors in
let nb_args := nb_args_inductive e I - npars in
let npars_vars := npars - npars_args in 
let initial_vars := build_list_of_vars nb_args in
let db_pars_fix := List.map (fun x => nb_args + x) (build_list_of_vars npars_vars) in
let db_fix_fix := nb_args + npars_vars in
let ty_vars := lift_list_ty (get_args_inductive_fresh_types e I) in
  let fix aux ctors_type :=
    match ctors_type with
      | c :: cs => 
          let info := find_cstr_info npars c in
          let res := split_conclusion info in
          let db_fix_rel := res.1.1 in (* the DB index of the fixpoint in the conclusion of the inductive *)
          let pars_rel := res.1.2 in (* the parameters in the conclusion of the inductive *)
          let db_pars_rel := only_variables pars_rel in (* the DB indexes of the parameters *)
          let patterns_conclusion := (split_conclusion info).2 in
          let mapping_vars := pos_tRels patterns_conclusion in
          let premises := premises info in
          let res := aux cs in
          (((db_fix_fix, db_fix_rel) :: (combine db_pars_fix db_pars_rel) ++ mapping_vars ) :: res.1.1, premises :: res.1.2, patterns_conclusion :: res.2)
      | [] => ([], [], [])
    end
  in 
  let res := aux ctors_type in
  {| ty_vars := ty_vars ; init_vars := initial_vars ; mappings := res.1.1; init_premises := res.1.2; patterns :=  transpose res.2 default_reif |}.



Definition initial_mappings 
(e : global_env)
(I : term)
:=
match I with
  | tApp I' l => initial_mappings_aux e I' (Datatypes.length l)
  | _ => initial_mappings_aux e I 0
end.

Fixpoint list_of_holes (n : nat) :=
match n with
| 0 => []
| S n' => hole :: list_of_holes n'
end.

Definition mknAnon := {| binder_name := nAnon ; binder_relevance := Relevant |}.

Fixpoint list_aname (n : nat) :=
match n with
| 0 => []
| S n' => mknAnon :: list_aname n'
end.

Fixpoint head_term (t : term) :=
match t with
| tApp u l => head_term u
| _ => t
end.

Definition tail_term (t : term) :=
match t with
| tApp u l => l
| _ => []
end.

Definition build_case_info_and_pterm (env : global_env) (I : term) :=
let npars := (info_nonmutual_inductive env I).1 in
let indu :=
match I with
| tInd ind _ => ind
| _ => {|
    inductive_mind := (MPfile ["generate_fix"%bs], "default"%bs);
    inductive_ind := 0
  |}
end in 
({| ci_ind := indu ; ci_npar := npars; ci_relevance := Relevant |},
{| puinst := [];  
pparams := list_of_holes npars; 
pcontext := [mknAnon]; (* as clause (should not be a problem) *)
preturn := <% bool %> |}).

Definition apply_term (t : term) (n : nat) :=
let l := List.map (fun x => tRel x) (build_list_of_vars n)
in match t with
| tApp u l' => tApp u (l'++l)
| _ => tApp t l
end.

(* Debugging functions *)

Definition print_mapping_in_term_failure m :=
let p := List.split m in
let l1 := List.map (fun x => tRel x) p.1 in
let l2 := List.map (fun x => tRel x) p.2 in
tApp (tVar "failure, the mapping is"%bs) (l1 ++ l2).

Definition print_mapping_in_term_success m l :=
let p := List.split m in
let l1 := List.map (fun x => tRel x) p.1 in
let l2 := List.map (fun x => tRel x) p.2 in
tApp (tVar "sucess, the mapping is"%bs) (l1 ++ l2 ++ l).

Definition print_unif_failed_in_term t1 t2 :=
tApp (tVar "error unification between"%bs) [t1; t2].

Definition print_mapping_in_term_continue m n t :=
let p := List.split m in
let l1 := List.map (fun x => tRel x) p.1 in
let l2 := List.map (fun x => tRel x) p.2 in
tApp (tVar "continue, the mapping is"%bs) (l1 ++ l2 ++ [tApp (tVar "we should match"%bs)  [tRel n]] ++
[tApp (tVar "the new pattern is"%bs)  [t]]).


(* Variable toto : bool.

Variable toto2 : list nat.

Variable toto3 : bool -> bool.

Variable toto4 : list nat -> bool.

Definition toto_reif := <% toto %>. *)

Definition fail := false. 

Fixpoint cstr_handler_list
(e : global_env) (* the global envronment to look for information about inductives *)
(vars : list nat) (* the variables that we will pattern match on initialized with tRels only *)
(ty_vars : list term) (* the inductive type of each variable *)
(premises : list (list term)) (* the premises: need to be true whenever the unification is done *)
(patterns_conclusion : list (list term)) (* the unification is made between the variables and the patterns *)
(ms : list mapping) (* the initial mapping of variables *)
(ldec : list (term*term*term)) (* a list of inductive predicates and their boolean translation *)
(fuel : nat) (* some fuel *)
: term := 
match fuel with
| 0 => tVar "no_fuel_in_cstr_handler_list"%bs
| S fuel' => 
 match vars, patterns_conclusion, ty_vars with
| v :: vs, pcs :: pcss, ty :: tys => 
    match pcs with 
      | _ :: _ => 
          let opt := unify_list_mapping (tRel v) pcs ms in
          match opt with 
            | None => default_reif (* should not happen : the mappings is of the same size as pc => one mapping for constructor *)
            | Some lunif => 
                let ms' := replace_mappings ms lunif in
                let b := unifs_all_some lunif in
                if andb b (negb (is_empty pcss)) then cstr_handler_list e vs tys premises pcss ms' ldec fuel'
                else if b then build_andb (return_premises (hd [] premises) (hd [] ms') ldec)
                else if unifs_fst_some lunif then 
                let new_tys := head_becomes_last ty_vars in 
                let new_vars := head_becomes_last vars in
                let new_patterns := head_becomes_last patterns_conclusion in
                cstr_handler_list e new_vars new_tys premises new_patterns ms' ldec fuel' 
                else build_pattern_list e v ty pcs vars ty_vars premises (pcs :: pcss) ms' ldec fuel'
          end
      | [] => <% false %> (* this case happens when there is no constructor in the inductive *)
    end
| [], [], [] => let l := List.combine premises ms in 
    build_orb (List.map (fun x => build_andb (return_premises x.1 x.2 ldec)) l)
| _, _, _ =>  let l := List.combine premises ms in 
    build_orb (List.map (fun x => build_andb (return_premises x.1 x.2 ldec)) l)
end
end
with
build_pattern_list
(e : global_env) (* the global envronment to look for information about inductives *)
(var : nat) (* the variable we match on *)
(I : term) (* the inductive type corresponding to the variable we match on *) 
(ts: list term) (* the terms to unify *)
(vars : list nat) (* the variables that we will pattern match initialized with tRels only *)
(ty_vars : list term) (* the inductive type of each variable *)
(premises : list (list term)) (* the premises: need to be true whenever the unification is done *)
(patterns_conclusion : list (list term)) (* the rest of the patterns *)
(ms : list mapping) (* the initial mapping of variables *)
(ldec : list (term*term*term)) (* a list of inductive predicates and their boolean translation *)
(fuel : nat) (* some fuel *) : term
:= 
let I' := head_term I in
let lpars0 := tail_term I in 
let npars := Datatypes.length lpars0 in
let lpars := list_of_dumb_term npars in
let p := build_case_info_and_pterm e I' in
let ci := p.1 in
let pt := p.2 in
let args := get_type_of_args_of_each_constructor e I' in
let list_constructors := rev (list_ctors_applied_to_params e I' lpars) in
let fix build_branch_list e vars ty_vars ts premises patterns_conclusion ms args list_constructors fuel {struct fuel} :=
match fuel with
| 0 => [{| bcontext := 
[{| binder_name := nNamed "error not enough fuel"%bs ; binder_relevance := Relevant |}]; bbody := default_reif |}]
| S fuel' =>
match args, list_constructors with
| lty :: ltys, c :: cs => 
  let len := Datatypes.length lty in
  let cstr_applied := apply_term c len in
  let new_mappings := List.map (fun x => lift_mapping len x) ms in
  {| bcontext := list_aname len ; bbody := 
  let fix aux new_mappings ts premises patterns_conclusion :=
  match new_mappings, ts with
    | [], [] => <% false %>
    | new_mapping :: new_mappings', t :: ts' => 
        match unify_mapping cstr_applied t new_mapping with 
          | continue n' pc' => (* we need to continue to match the variable n' against pc' *)
                    let ty_n' := nth (len-1-n') lty default_reif in
                    let l := build_list_of_vars len in
                    let new_vars := l++(List.map (fun x => x + len) vars) in
                    let new_tys := lty++List.map (fun x => lift len 0 x) ty_vars in
                    let pcs' := replace_head pc' ts in
                    build_pattern_list e n' ty_n' pcs' new_vars new_tys premises patterns_conclusion new_mappings ldec fuel'
          | failure => (* failure : we need to try another constructor for this variable so we remove the premises of the first constructor  *)
              <% fail %>
          | some m' =>
                if is_empty patterns_conclusion then (* no more patterns to match so we should if other constructors can match *)
                  let new_vars :=  List.map (fun x => x + len) vars in
                  let new_tys := List.map (fun x => lift len 0 x) ty_vars in
                  let res := aux new_mappings' ts' (tl premises) patterns_conclusion in
                  let res2 := build_andb (return_premises (hd [] premises) m' ldec) in
                  if orb (eqb_term res <% false %>) (eqb_term res <% fail %>) then res2
                  else if orb (eqb_term res <%true %>) (eqb_term res2 <%true%>) then <% true %>
                  else tApp <% orb %> [res2; res ]
                else (* the other variables of the first constructor have to match *)
                  let new_vars :=  List.map (fun x => x + len) vars in
                  let new_tys := List.map (fun x => lift len 0 x) ty_vars in
                  let new_patterns := List.map (fun x => [hd default_reif x]) patterns_conclusion in (* we are commited to the first constructor now *)
                  let res := cstr_handler_list e (tl new_vars) (tl new_tys) [hd [] premises] (tl new_patterns) [m'] ldec fuel' in
                  let res2 := aux new_mappings' ts' (tl premises) (List.map (fun x => tl x) patterns_conclusion) in
                  if eqb_term res <% false %> then 
                    res2 
                  else if orb (eqb_term res2 <% false %>) (eqb_term res2 <% fail %>)  then res
                  else if orb (eqb_term res <%true %>) (eqb_term res2 <%true%>) then <% true %> else tApp <% orb %> [res ; res2]
                
          end 
    | _, _ => default_reif (* should not happen : as many mappings as terms *)
  end 
  in let res := aux new_mappings ts premises patterns_conclusion in
if eqb_term res <% fail %> then 
let res2 := 
aux (tl new_mappings) (tl ts) (tl premises) (List.map (fun x => tl x) patterns_conclusion)
in if eqb_term res2 <%fail %> then <% false %> else res2
else res |} ::
    build_branch_list e vars ty_vars ts premises patterns_conclusion ms ltys cs fuel' 
| [], [] => []
| _, _ => (* should not happen *) [{| bcontext := 
[{| binder_name := nNamed "error"%bs ; binder_relevance := Relevant |}]; bbody := default_reif |}]
end 
end in 
tCase ci pt (tRel var) 
 (build_branch_list e vars ty_vars ts premises patterns_conclusion ms args list_constructors fuel).

Fixpoint mkLambda (l : list term) (t : term) :=
match l with
| [] => t
| x :: xs => tLambda mknAnon x (mkLambda xs t)
end.

Fixpoint mkProd (l : list term) (t : term) :=
match l with
| [] => t
| x :: xs => tProd mknAnon x (mkProd xs t)
end.

Fixpoint ctors_type (l : list constructor_body) := 
match l with
| [] => []
| x :: xs => x.(cstr_type) :: ctors_type xs
end.


(* initialize the function cstr_handler_list *)
Definition call_cstr_handler_list 
(e : global_env) 
(I : term)
(ldec : list (term*term*term)) :=
let im := initial_mappings e I in
cstr_handler_list e (init_vars im) (rev (ty_vars im)) (init_premises im) (patterns im) (mappings im) ldec 1000.

Definition build_fixpoint_aux
(recarg : nat) (* the recusive argument to build the fixpoint *)
(t : term) (* the big match *)
na (* a name for the fixpoint *)
(lty : list term) (* the list of types of the arguments (already lifted) *) :=
let ty := mkProd lty <% bool %> in
(tFix 
[{| dname := {| binder_name := nNamed (na++"_decidable")%bs ; binder_relevance := Relevant |} ;
dtype := ty ;
dbody := mkLambda lty t ;
rarg := recarg |}] 0, ty).


Definition build_fixpoint_aux2 
(e : global_env) (* the global envronment to look for information about inductives *)
(I : term) 
(ldec : list (term*term*term))
(recarg : nat) :=
let na := find_name_gref I in
let lty := rev (get_args_inductive_fresh_types e I) in
let typars := params_inductive e I in
let tys_to_bind := typars ++ lty in
let res := call_cstr_handler_list e I ldec in
build_fixpoint_aux recarg res na tys_to_bind.

(** Functions to compute the recursive argument **) 

Fixpoint find_candidates_db_for_decreasing_args_term_aux 
(e: global_env) 
(t : term) (* is the term is a constructor applied to its argument, then all the 
de brujin indexes which are not parameters we encounter may be candidates for 
representing a decreasing argument *) 
(fuel : nat)
:=
match fuel with
| 0 => None
| S fuel' =>
  match t with
  | tApp (tConstruct Ind n inst) l => 
    let npars := Datatypes.length (params_inductive e (tInd Ind inst)) in
    let l' := List.skipn npars l in
    Some (find_candidates_db_for_decreasing_args_list e l' fuel')
  | tRel n => None
  | _ => None
  end
end
with find_candidates_db_for_decreasing_args_list 
(e: global_env) 
(l : list term) 
(fuel: nat) : list nat
:=
match fuel with
| 0 => []
| S fuel' =>
  match l with
  | [] => []
  | x :: xs => match x with
          | tRel n => [n] ++ find_candidates_db_for_decreasing_args_list e xs fuel'
          | _ => let opt := find_candidates_db_for_decreasing_args_term_aux e x fuel' in
          match opt with
          | None => find_candidates_db_for_decreasing_args_list e xs fuel'
          | Some l => l ++ find_candidates_db_for_decreasing_args_list e xs fuel'
          end
     end
  end
end.

Definition find_candidates_db_for_decreasing_args_conclusion 
(e: global_env)
(t : term) :=
let fuel := size t in
match t with
| tApp (tRel _) l => List.fold_left (fun acc (x : term) => let res := find_candidates_db_for_decreasing_args_term_aux e x fuel
                      in match res with
                      | None => acc
                      | Some x => x ++ acc end) l []
| _ => []
end.

(* each premise of the forme our inductive applied to its arguments
will have candidates for decreasing args
we find the de brujin indexes and their position 
If the premise is not recursive, should return none *)
Definition find_candidates_db_for_decreasing_args_premise
(e: global_env)
(t : term)
(npars : nat)
:=
match t with
| tApp (tRel _) l =>
  let l' := List.skipn npars l in
  let fix aux l len :=
    match l with
    | [] => []
    | x :: xs => match x with
          | tRel n => (n, len+npars) :: aux xs (S len)
          | _ => aux xs (S len)
          end
    end in Some (aux l' 0)
| _ => None
end.


(* Returns false when all the premises are not recursive *)
Definition find_candidates_db_for_decreasing_args_premises 
(e: global_env)
(l : list term)
(npars : nat) :=
let fix aux e l npars b :=
match l with
| [] => ([], b)
| x :: xs => match (find_candidates_db_for_decreasing_args_premise e x npars) with
            | None => aux e xs npars b
            | Some x => let res := aux e xs npars true in (x++res.1, res.2)
            end
end in aux e l npars false.


Fixpoint search_list (l1 : list nat) (l2 : list (nat*nat)) :=
match l1 with
| [] => []
| x :: xs => let fix aux x l2 :=
              match l2 with
              | [] => []
              | p :: ps => let y := p.1 in 
                           let z := p.2 in 
                           if Nat.eqb x y then z :: aux x ps
                           else aux x ps
             end in aux x l2 ++ search_list xs l2
end.

Definition find_decreasing_arg_one_constructor 
(e: global_env)
(premises : list term)
(npars : nat) 
(t : term)
:= 
let (result, b) := find_candidates_db_for_decreasing_args_premises e premises npars in
let lrel := find_candidates_db_for_decreasing_args_conclusion e t in
match b with
| false => (Some [], false) (* not recursive *)
| true => let res := search_list lrel result in
          (Some res, true)
end. 

Fixpoint is_in_all_lists (x: nat) (l : list (list nat)) :=
match l with
| [] => true
| l' :: ls => let fix aux x l' := match l' with
              | [] => false
              | y :: ys => Nat.eqb x y || aux x ys
            end in aux x l' && is_in_all_lists x ls
end.

Definition find_common_term_in_list_of_list (l : list (list nat)) 
:=
match l with
| [] => None
| l' :: ls => let fix aux l' ls :=
             match l' with
            | x :: xs => if is_in_all_lists x ls then Some x else aux xs ls
            | [] => None end in aux (rev l') ls
end. 

Definition find_decreasing_arg
(e: global_env)
(I : term) :=
let info := info_nonmutual_inductive e I in
let npars := info.1 in 
let ctors := info.2 in
let ctors_ty := ctors_type ctors in
let fix aux e I npars ctors_ty :=
match ctors_ty with
| [] => []
| c :: cs => let info := find_cstr_info npars c in 
             let prem := premises info in
             let ccl := conclusion info in
             let result := find_decreasing_arg_one_constructor e prem npars ccl in 
             let opt := result.1 in
             let b := result.2 in
             match b with
            | false => aux e I npars cs
            | true => match opt with | None => aux e I npars cs | Some l => l :: aux e I npars cs end
            end 
end
in find_common_term_in_list_of_list (aux e I npars ctors_ty).

(* compute find_decreasing_arg e even_reif_rec.1 even_reif_rec.2.  *)

Notation tmWait := (tmMsg ""%bs).

Definition Indu_name_decidable t :=
match t with
| tInd indu _ => match (inductive_mind indu) with (kn, id) => id^"_decidable" end
| _ => "fresh_ident"%bs
end.

Definition build_fixpoint_auto {A: Type}
(t : A) 
(l : list (term*term*term)) :=
p <- tmQuoteRec t ;;
let indu := p.2 in 
let name := Indu_name_decidable indu in
let genv := p.1 in
let recarg := find_decreasing_arg genv indu in
match recarg with
| Some n => let fixp := build_fixpoint_aux2 genv indu l n in
            let fixp_trm := fixp.1 in
            fresh <- tmFreshName name ;;
            tmMkDefinition fresh fixp_trm
| None => tmFail "cannot find the recursive argument automatically, you should try 
    build_fixpoint_recarg instead"%bs
end.


Definition build_fixpoint_recarg {A : Type}
(t : A)
(l : list (term*term*term))
(n : nat) 
:=
p <- tmQuoteRec t ;;
let indu := p.2 in 
let genv := p.1 in
let name := Indu_name_decidable indu in
fresh <- tmFreshName name ;; 
let fixp := build_fixpoint_aux2 genv indu l n in
let fixp_trm := fixp.1 in
tmMkDefinition fresh fixp_trm.


Definition linearize_and_fixpoint_auto 
{A : Type}
(t : A)  
(l : list (term*term*term))
:=
res0 <- tmQuoteRec t ;; 
genv <- tmEval all res0.1 ;;
t' <- tmEval all res0.2 ;;
name_indu_linear <- linearize_from_mind_entry t' ;; 
curmodpath <- tmCurrentModPath tt ;;
let name_indu := (curmodpath, name_indu_linear) in
let indu := tInd {| inductive_mind := name_indu ;
                  inductive_ind := 0 |} [] in
mind <- tmQuoteInductive name_indu ;;
let new_gdecl := (name_indu, (InductiveDecl mind)) :: (declarations genv ) in 
let new_genv := {| universes := universes genv ; declarations := new_gdecl ; retroknowledge :=
retroknowledge genv |} in
let name := Indu_name_decidable indu in
let recarg := find_decreasing_arg new_genv indu in 
let npars := Datatypes.length (params_inductive new_genv indu) in
npars' <- tmEval all npars ;;
match recarg with
| Some n => fresh <- tmFreshName name ;; 
            n' <- tmEval all n ;;
            let fixp := build_fixpoint_aux2 new_genv indu l n in
            let fixp_ty := fixp.2 in
            let fixp_trm := fixp.1 in  trm_print <- tmEval all fixp_trm ;;
            tmMkDefinition fresh fixp_trm ;;
            tmReturn (t, fresh, n', npars', fixp_trm, genv) 
| None => tmFail "cannot find the recursive argument automatically, you should try 
    build_fixpoint_recarg instead"%bs
end.

Section test.

Inductive member : nat -> list nat -> Prop :=
| MemMatch : forall xs n n', eqb_of_compdec Nat_compdec n n' = true -> member n (n'::xs)
| MemRecur : forall xs n n',
    member n xs -> member n (n'::xs).

Inductive even : nat -> Prop :=
even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).

Inductive smallernat : list nat -> list nat -> Prop :=
| cons1 : forall l', smallernat [] l'
| cons2 : forall l l' x x', smallernat l l' -> smallernat (x :: l) (x' :: l').

MetaCoq Run (build_fixpoint_auto member []).   

MetaCoq Run (build_fixpoint_auto (Add_linear) []). 

MetaCoq Run (build_fixpoint_auto even []).

MetaCoq Run (linearize_and_fixpoint_auto (smallernat) []).

MetaCoq Run (linearize_and_fixpoint_auto (add) []). 

MetaCoq Run (build_fixpoint_recarg even [] 0).

MetaCoq Run (build_fixpoint_auto (@smaller) []).

Inductive member' (B: Type) : B -> list B -> Prop :=
| MemMatch' : forall xs n, member' B n (n::xs)
| MemRecur' : forall xs n n',
    member' B n xs -> member' B n (n'::xs).

MetaCoq Run (linearize_and_fixpoint_auto member' []).

End test.

Section test2.


Inductive Add_linear' (A : Type) (HA : CompDec A) (a : A) : list A -> list A -> Prop :=
    Add_head : forall (x : A) (l l' : list A), eqb_of_compdec list_compdec l l' = true -> 
eqb_of_compdec HA x a = true -> Add_linear' A HA a l (x :: l')
  | Add_cons : forall (x y : A) (l l' : list A), eqb_of_compdec HA x y = true ->
               Add_linear' A HA a l l' -> Add_linear' A HA a (x :: l) (y :: l').

MetaCoq Run (build_fixpoint_auto (@Add_linear') []).

Variable A : Type.
Variable HA : CompDec A.
Variable a : A.

Inductive Add_linear2 : list A -> list A -> Prop :=
    Add_head2 : forall (x : A) (l l' : list A), eqb_of_compdec (@list_compdec A HA) l l' = true -> 
eqb_of_compdec HA x a = true -> Add_linear2 l (x :: l')
  | Add_cons2 : forall (l l' : list A) (x y : A), eqb_of_compdec HA x y = true ->
               Add_linear2 l l' -> Add_linear2 (x :: l) (y :: l').

Inductive smaller2 : list nat -> list nat -> Prop :=
    sm_nil2 : forall l : list nat, smaller2 [] l
  | sm_cons2 : forall (x x' : nat) (l l' : list nat),
              smaller2 l l' -> smaller2 (x :: l) (x' :: l').


MetaCoq Run (build_fixpoint_auto (@smaller2) []).

MetaCoq Run (build_fixpoint_auto (@Add_linear2) []). 

End test2.

Section test3.

Variable eqblistnat : list nat -> list nat -> bool.

Inductive elt_list :=
 |Nil : elt_list
 |Cons : Z -> Z -> elt_list -> elt_list.

Inductive Inv_elt_list : Z -> elt_list -> Prop :=
 | invNil  : forall b, Inv_elt_list b Nil
 | invCons : forall (a b  j: Z) (q : elt_list),
     (j <= a)%Z -> (a <= b)%Z ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

MetaCoq Run (build_fixpoint_auto (Inv_elt_list) [(<%Z.le%>, <%Z.leb%>, <%Zle_is_le_bool%>)]). 

Inductive smaller_Z : list Z -> list Z -> Prop :=
| sm_nil_Z : forall l, smaller_Z [] l
| sm_cons_Z : forall x x' l l', smaller_Z l l' -> smaller_Z (x :: l) (x' :: l').

MetaCoq Run (build_fixpoint_auto (smaller_Z) []).

Inductive lset : list nat -> Prop :=
| Empty : lset []
| Conss : forall n xs,
           negb (member_decidable n xs) = true ->
           lset xs ->
           lset (n::xs).
MetaCoq Run (build_fixpoint_recarg lset [] 0). 

End test3.





