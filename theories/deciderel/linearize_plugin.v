From MetaCoq.Template Require Import All.
Import MCMonadNotation.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Bool.
From SMTCoq Require Import SMTCoq.
Require Import add_hypothesis_on_parameters.
Require Import compdec_plugin.
Require Import utilities.
Unset MetaCoq Strict Unquote Universe Mode.

(** Replacement of variables **) 

Fixpoint measure_replace_occurences (t : term) : nat :=
match t with
| tApp u l => (Datatypes.length l)*(List.fold_left (fun x y => x + measure_replace_occurences y) l 0)
| tProd _ u v => S (measure_replace_occurences u + measure_replace_occurences v)
| _ => 1
end.

(* In a term t made of products, variables and applications only, we replace the nth occurence of the variable i 
by the i-th term of the list l *)
Fixpoint replace_occurences_aux (i: nat) (l : list term) (t : term) (fuel : nat) (nb_lift : nat) (npars : nat) : term*(list term) :=
match fuel with
  | 0 => (default_reif, [])
  | S n => 
    match t with
    | tApp u l0 => replace_occurences_ignore_params i u l0 l n nb_lift npars
    | tRel j => if i =? j then (hd default_reif l, tl l)
      else ((lift (2*nb_lift) i (tRel j)), l)
    | tProd Na Ty u => let Ty' := (lift (2*nb_lift) i Ty)in 
        let u' := (replace_occurences_aux (i+1) (List.map (lift 1 0) l) u n nb_lift npars).1 in
        (tProd Na Ty' u', l)
    | _ => (t, l)
    end
end
with
replace_occurences_list (i: nat) (l : list term) (l' : list term) (fuel : nat) (nb_lift: nat) (npars : nat) : (list term)*(list term) :=
 match fuel with
    | 0 => ([], [])
    | S n =>
        match l' with
        | [] => ([], l)
        | x' :: xs' => 
          let p := replace_occurences_aux i l x' n nb_lift npars in
          let p' := replace_occurences_list i p.2 xs' n nb_lift npars in
          ((p.1 :: p'.1), p'.2)
        end
end
with replace_occurences_ignore_params 
(i: nat) (u : term) (l : list term) (l' : list term) (fuel : nat) (nb_lift: nat) (npars : nat) : term*(list term) :=
match fuel with
| 0 => (default_reif, [])
| S fuel =>
match u with
| tRel j => let u' := (lift (2*nb_lift) i (tRel j)) in
let lpars := List.firstn npars l in
let lpars_lifted :=  List.map (fun x => (lift (2*nb_lift) 0 x)) lpars in
let largs := List.skipn npars l in
let result := replace_occurences_list i l' largs fuel nb_lift npars in
(tApp u' (lpars_lifted ++ result.1), result.2)
| _ => let u' := (lift (2*nb_lift) i u) in let p := replace_occurences_list i l' l fuel nb_lift npars in (tApp u' p.1, p.2)
end
end.

Definition replace_occurences i l t npars := 
let nb_lift := (Datatypes.length l -1) in
let fuel := measure_replace_occurences t in
(replace_occurences_aux i l t fuel nb_lift npars).1.

Definition replace_occurences_pars i l t npars := 
let nb_lift := (Datatypes.length l) in
let fuel := measure_replace_occurences t in
(replace_occurences_aux i l t fuel nb_lift npars).1.

(* In a term of the form P1 -> ... -> Pn, with all of the Pi made of constants, variables and applications only,
we compute the maximum number of occurences of the variable n in each of the Pi *)
Definition compute_occurences_max (n : nat) (t : term) : nat := 
let fix aux n t occurs := 
match t with
| tProd _ Ty u => (aux (n+1) u 0)
(* We lift the variable n each time we compute under a forall, we do not consider the negative occurences: we 
want to linearize only the conclusion of the term *)
| tApp u l => List.fold_left (fun acc x => acc + aux n x 0) l occurs
(* We suppose that the application is flattened and that our variable is not a function, so it does not occurs in u *)
| tRel i => if i =? n then 1 else 0
| _ => 0 (* To simplify, we do not consider other kind of terms *)
end in aux n t 0.

(* The same function but we ignore the parameters in the application *)
Definition compute_occurences_max_parameters (n npars : nat) (t : term) : nat := 
let fuel := size t in
let fix aux n npars t occurs fuel :=
match fuel with
| 0 => 0
| S fuel' => 
match t with
| tProd _ Ty u => aux (n+1) npars u 0 fuel'
| tApp u l => 
    match u with
    | tRel _ => let l' :=  (List.skipn npars l) in List.fold_left (fun acc x => acc + aux n npars x 0 fuel') l' occurs
    | _ => List.fold_left (fun acc x => acc + aux n npars x 0 fuel') l occurs
    end 
| tRel i => if i =? n then 1 else 0
| _ => 0 
end 
end in aux n npars t 0 fuel.


(** 2: Generation of equalities **) 

MetaCoq Quote Definition eq_reif := @eq.

MetaCoq Quote Definition bool_reif := bool. 

MetaCoq Quote Definition true_reif := true. 

MetaCoq Quote Definition eqb_of_compdec_reif := @eqb_of_compdec.


(** Functions to build MetaCoq terms **)

Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].

Definition mkCompdecEq (B HB t1 t2 : term) := tApp eqb_of_compdec_reif [B ; HB ; t1 ; t2].

Definition dest_app_list (t : term) : term* (list term) :=
match t with
| tApp u v => (u, v)
| _ => (t, [])
end.

Fixpoint search_list_of_compdecs_fuel
(l : list term) (lc : list (term*term)) (n : nat) {struct n} :=
match n with
| 0 => []
| S n' =>
match l with
| [] => []
| x :: xs => search_compdec_fuel x lc n' :: search_list_of_compdecs_fuel xs lc n'
end 
end
with
search_compdec_fuel (Ty : term) (l : list (term*term)) (n : nat) : term :=
match n with
| 0 => tVar "no more fuel"%bs
| S n' =>
match l with
| [] => match Ty with
      | tRel n => tRel (n-1)
      | _ => tVar "the type is not a variable"%bs 
      end
| x :: xs => if eqb_term Ty x.2 then x.1 
            else
             let (u, v) := dest_app_list Ty in
if eqb_term u x.2 then match x.1 with
    | tApp u _ => tApp u (v ++ (search_list_of_compdecs_fuel v l n'))
    | _ => x.1
end else
search_compdec_fuel Ty xs n'
end
end.

Definition search_compdec (Ty : term) (l : list (term*term)) :=
let fuel := 
match Ty with
| tApp u v => ((Datatypes.length v) * (Datatypes.length l))%nat
| _ => Datatypes.length l
end in search_compdec_fuel Ty l (fuel + 1000).


(* Generates the equalities 
eqb_of_compdec Ty comp (tRel n) (tRel (n-1)) = true
...
eqb_of_compdec Ty comp (tRel (2*n-1)) (tRel (n-1)) = true *)
Definition gen_compdec_eq Ty comp n :=
let fix aux x Ty comp n1 n2 :=
match n1 with
| 0 => []
| S n1' => mkEq bool_reif (mkCompdecEq Ty comp x (tRel n2)) true_reif :: aux (lift 1 0 x) (lift 1 0 Ty) (lift 1 0 comp) n1' n2
end 
in aux (tRel (n-1)) Ty comp (n-1) (n-2).

Fixpoint mkList (t: term) (n : nat) :=
match n with
| 0 => []
| S n => t :: (mkList (lift 1 0 t) n)
end.

Definition mkProd T u :=
tProd {| binder_name := nAnon; binder_relevance := Relevant |} T u.

Fixpoint mkProd_list_no_lift_aux (t : term) (l : list term) (n : nat) : term := 
match n with
| 0 => t
| S n => 
match l with
| [] => t 
| x :: xs =>
 mkProd x (mkProd_list_no_lift_aux t xs n)
end
end.


Fixpoint get_list_of_rel (n1 n2 : nat) := 
match n1 with
| 0 => []
| S n' => (tRel n2) :: get_list_of_rel n' (n2 -1)
end.

Definition mkProd_list_no_lift t l := let n := Datatypes.length l in
mkProd_list_no_lift_aux t l n.

Fixpoint linearize_aux_compdec (t : term) (n: nat) (lcomp : list (term*term)) (npars : nat) : term :=
match n with
| 0 => default_reif
| S m =>
match t with
| tProd Na Ty u => let occ := (compute_occurences_max 0 u) in
 if Nat.ltb 1 occ then (* we compute the new term only if the quantified variable occurs in the rest of the term *)
let len := (occ - 1) in
let l0 := get_list_of_rel occ (2*len) in 
let res := (replace_occurences 0 l0 u npars) in 
let comp := search_compdec Ty lcomp in
let l_eq := gen_compdec_eq (lift occ 0 Ty) (lift occ 0 comp) occ in
let l2 := mkList (lift 1 0 Ty) len in
tProd Na Ty (mkProd_list_no_lift (mkProd_list_no_lift (linearize_aux_compdec res m lcomp npars) l_eq) l2)
else tProd Na Ty (linearize_aux_compdec u m (List.map (fun x => (lift 1 0 x.1, lift 1 0 x.2)) lcomp) npars)
| _ => t 
end
end.

Fixpoint fuel_linearize t  := match t with
| tProd _ u v => fuel_linearize u + fuel_linearize v + 1
| _ => 1
end.

Definition linearize_compdec (t : term) lcomp := let fuel := fuel_linearize t in linearize_aux_compdec t fuel
lcomp.


Fixpoint gen_compdec_eq_params_aux Ty lcomp nb_eq nbvar var_eq :=
let comp := search_compdec Ty lcomp in
match nb_eq with
| 0 => []
| S nb_eq => mkEq bool_reif (mkCompdecEq Ty comp (tRel nbvar) (tRel var_eq)) true_reif ::
gen_compdec_eq_params_aux (lift 1 0 Ty) lcomp nb_eq (S nbvar) (S var_eq)
end.

Fixpoint get_list_of_rel2 (n1 n2 : nat) := 
match n1 with
| 0 => []
| S n' => (tRel n2) :: get_list_of_rel2 n' (S n2)
end.

(*

Fixpoint replace_occurences_aux (i: nat) (l : list term) (t : term) (fuel : nat) (nb_lift : nat) (npars : nat) *)

Definition linearize_parameter_compdec  (lcomp : list (term*term)) (t: term) (Typars : list term) (npars : nat) :=
let fix aux lcomp t Typars npars nb_lift_reccall nb_reccall l_types := 
match Typars with
| [] => match l_types with
        | [] => t
        | _:: _ => mkProd_list_no_lift t l_types
        end
| Ty :: xs => let actual_par := Datatypes.length xs in
let occ := compute_occurences_max_parameters (nb_reccall+nb_lift_reccall) npars t in
if Nat.ltb 0 occ then (* tProd na Ty (linearize_parameter_compdec_aux Σ lcomp u npars') *)
let l0 := get_list_of_rel2 occ (occ + nb_lift_reccall) in
let res := replace_occurences_pars (nb_reccall+nb_lift_reccall) l0 t npars in
let Ty_lifted := (lift (S actual_par) 0 Ty) in
let comp := search_compdec Ty_lifted lcomp in
let l_eq := gen_compdec_eq_params_aux (lift occ 0 Ty_lifted) lcomp occ (occ+nb_reccall) 0 in
let l2 := mkList Ty_lifted occ in
let new_types := List.map (fun x => lift (2*occ) nb_reccall x) l_types in
let l' := l2++l_eq++new_types in
aux lcomp res xs npars ((2*occ+nb_lift_reccall)%nat)
(S nb_reccall) l'
else aux lcomp t xs npars nb_lift_reccall (S nb_reccall) l_types
end
in aux lcomp t (rev Typars) npars 0 0 [].

(*(tApp (tRel 8)
                                                [tRel 7; tRel 6; 
                                                tRel 5; tRel 4; 
                                                tRel 3; tRel 1]) *)

Definition test_pars := (tApp (tRel 4)
                                    [tRel 3; tRel 2; 
                                    tRel 1; tRel 0; 
                                    tRel 1; tRel 0]).



(* Compute linearize_parameter_compdec s [] test_pars [impossible_term_reif] 4.
Compute compute_occurences_max_parameters s 3 4 (tApp (tRel 6) [tRel 5; tRel 4; tRel 3; tRel 2; tRel 3; tRel 1]).
Compute get_list_of_rel2 1 2.
Compute linearize_parameter_compdec s [] test_pars [impossible_term_reif; impossible_term_reif] 4. *)




(* Fixpoint list_pars_to_linearize Σ (l : list context_decl) := 
match l with
| [] => []
| x :: xs => let Ty := x.(decl_type) in 
        match x.(decl_type) with
        | tSort s => list_pars_to_linearize xs
        | tApp u l => if eqb_term (trans Σ u) <% CompDec %> then list_pars_to_linearize xs else (Ty, x.(decl_name)) :: list_pars_to_linearize xs
        | _  => (Ty, x.(decl_name)) :: list_pars_to_linearize xs 
        end
end. *)

Definition app_or_not (t : term) (n : nat):=
match n with
| 0 => t
| S n => tApp t [] (* we apply t to an empty list because t needs instances in the function search_compdec *)
end.

(* The list l whose elements are of the form (trm, Ty) are such as
trm is the proof of CompDec Ty or the proof of forall A1, ..., An, CompDec A1-> ... -> CompDec An -> Compdec (Ty A1 .. An), 
n is the number of parameters of Ty. We will then instantiate the lemma with each (tRel u) in ascending order *)
Fixpoint inst_parametric_compdec_hypothesis (l : list (term*term*nat)) : list (term*term) :=
match l with
| [] => []
| x :: xs => let y := app_or_not x.1.1 x.2 in (y, x.1.2) :: inst_parametric_compdec_hypothesis xs 
end.

Fixpoint list_pars_to_linearize2 (l : list context_decl) := 
match l with
| [] => []
| x :: xs => let Ty := decl_type x in match Ty with
        | tSort s  => list_pars_to_linearize2 xs
        | tApp u l => if eqb_term u <% CompDec %>  then list_pars_to_linearize2 xs else x :: list_pars_to_linearize2 xs
        | _ => x :: list_pars_to_linearize2 xs
        end
end. 

(* if the term is (tRel 0) (t1 ; ..., tk), we should remove the first nb_shift 
arguments because this nb_shift computes the difference of Db indexes between 
a polymorphic and a monomorphic version *)
Fixpoint eliminate_first_nargs (t : term) (nb_shift : nat) :=
match t with
| tProd na ty u => tProd na (eliminate_first_nargs ty nb_shift) (eliminate_first_nargs u nb_shift)
| tApp (tRel j) v => tApp (tRel j) (List.skipn nb_shift v)
| _ => t
end.

Fixpoint nb_occ_db_index (l : list term) (n : nat) (fuel : nat) :=
match fuel with
| 0 => 0
| S fuel' =>
match l with
| [] => 0
| x :: xs => match x with
        | tRel j => if Nat.eqb j n then (S (nb_occ_db_index xs n fuel')) else nb_occ_db_index xs n fuel'
        | tApp u l' => nb_occ_db_index l' n fuel' 
        | _ => nb_occ_db_index xs n fuel'
        end
end
end.

Fixpoint contains_nat_above_two (l : list nat) :=
match l with
| [] => false
| x :: xs => if Nat.leb 2 x then true else contains_nat_above_two xs
end.
(* warning: handles terms with no parameters only (or instantiated ones)
say if a term should be linearized or not, in order to avoid unecessary computations *) 

Fixpoint linearizable_term (t : term) (db_indexes : list nat) :=
match t with
| tProd na Ty u =>  if linearizable_term Ty db_indexes then true else 
linearizable_term u (0 :: (List.map S db_indexes))
| tApp x l => let lnat := List.map (fun x => nb_occ_db_index l x (list_size size l)) db_indexes in 
contains_nat_above_two lnat
| tRel j => false   
| _ => false
end.

Fixpoint linearizable_list_term (l : list term) : bool :=
match l with
| [] => false
| x :: xs => linearizable_term x [] || linearizable_list_term xs
end.

Definition linearize_oind_entry (oinde : one_inductive_entry) 
(params : list context_decl) (* list of params not instantiated: obtained by getting the mind entry *)
(lpars : list term) (* list of params instantiated (given by the user) *)
(npars : nat) 
list_compdecs 
(new_name : ident)
:=
let nb_shift := Datatypes.length lpars in
let new_arity := (subst lpars (npars - nb_shift) oinde.(mind_entry_arity)) in
let params2 := list_pars_to_linearize2 params in
let new_consnames := List.map (fun x => x^"_linear") oinde.(mind_entry_consnames) in
let lc := oinde.(mind_entry_lc) in
let b := linearizable_list_term lc in 
let new_lc := 
if b then
if nb_shift =? 0 then
List.map (fun x => linearize_parameter_compdec list_compdecs
(linearize_compdec x list_compdecs npars) (List.map (fun x => x.(decl_type)) params2) npars) lc
else
List.map (fun x => eliminate_first_nargs (linearize_parameter_compdec list_compdecs
(linearize_compdec (subst lpars (npars - nb_shift) x) list_compdecs npars) (List.map (fun x => x.(decl_type)) params2) npars) nb_shift)
 lc
else lc
in (
{| mind_entry_typename := new_name;
    mind_entry_arity := new_arity ;
    mind_entry_consnames := new_consnames;
    mind_entry_lc := new_lc 
|}, b). 

Definition remove_lastn {A : Type} (n : nat) (l : list A) :=
rev (List.skipn n (rev l)).

Definition replace_params (m : mutual_inductive_entry) (lpars : list term) :=
let c := mind_entry_params m in
let len := Datatypes.length lpars in
match len with
| 0 => c
| S n =>
let c' := remove_lastn len c in
let fix aux c l :=
match c with
| [] => []
| x:: xs => {|
               decl_name :=
                 decl_name x ;
               decl_body := decl_body x ;
               decl_type := subst lpars 0 (decl_type x)
             |} :: aux xs lpars
end in aux c' (rev lpars)
end.

Fixpoint contains_true (l : list bool) :=
match l with
| [] => false
| x :: xs => x || contains_true xs
end.

(* Warning: because of the only one ident, does not work for mutuals *)
Definition linearize_oind_entry_list (l : list one_inductive_entry) (params : list context_decl) lpars npars
list_compdecs new_name : (list one_inductive_entry)*bool :=
let interm_res :=
List.map (fun x => linearize_oind_entry x params lpars npars list_compdecs new_name) l
in let l1 := (split interm_res).1 
in let l2 := (split interm_res).2 in 
(l1, contains_true l2).

Definition linearize_from_mind_entry (t: term) :=  
t <- monadic_compdec_inductive t ;;
let list_compdecs := t.1.1 in 
let lpars := t.1.2 in 
let mind_entry := t.2 in (* the user may have given an term with parameters instantiated *)
let npars := List.length (mind_entry_params mind_entry) in
params <- tmEval all (replace_params mind_entry lpars) ;; 
new_compdecs <- tmEval all (inst_parametric_compdec_hypothesis list_compdecs) ;;
params_to_linearize <- tmEval all (list_pars_to_linearize2 params) ;; 
match mind_entry.(mind_entry_inds) with
| [] => tmFail "empty entry"%bs
| [x] => new_name <- tmFreshName (x.(mind_entry_typename)^"_linear") ;;
res <- tmEval all (linearize_oind_entry_list mind_entry.(mind_entry_inds) params_to_linearize lpars npars new_compdecs new_name) ;;
b <- tmEval all res.2 ;;
match b with
| true =>
let entry :=
{| 
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := params;
  mind_entry_inds := res.1;
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|} in tmMkInductive true entry ;; tmReturn new_name
| false => tmReturn x.(mind_entry_typename)
end
| _ :: _ => tmFail "mutuals not supported"%bs
end.

Section tests.


Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).


MetaCoq Run (tmQuote (@Add Z) >>= 
linearize_from_mind_entry).

Inductive smaller {A : Type} : list A -> list A -> Prop :=
| sm_nil : forall l, smaller nil l
| sm_cons : forall l l' x x', smaller l l' -> smaller (x :: l) (x' :: l').

MetaCoq Run (tmQuote (@smaller Z) >>= 
linearize_from_mind_entry).

Inductive elt_list :=
 |Nil : elt_list
 |Cons : Z -> Z -> elt_list -> elt_list.

Inductive Inv_elt_list : Z -> elt_list -> Prop :=
 | invNil  : forall b, Inv_elt_list b Nil
 | invCons : forall (a b  j: Z) (q : elt_list),
     (j <= a)%Z -> (a <= b)%Z ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

Inductive test3occ : nat -> nat -> nat -> Prop :=
| test3occ_constructor : forall n, test3occ n n n.

MetaCoq Run (tmQuote test3occ >>= 
linearize_from_mind_entry).

Inductive test4occ : nat -> nat -> nat -> nat -> Prop :=
| test4occ_constructor : forall n, test4occ n n n n.

MetaCoq Run (tmQuote test4occ >>= 
linearize_from_mind_entry).

Inductive test22occ : nat -> nat -> nat -> nat -> Prop :=
| test22occ_constructor : forall n k, test22occ 1 2 3 k -> test22occ n n k k.

MetaCoq Run (tmQuote test22occ >>= 
linearize_from_mind_entry).

Inductive test_poly_param (A: Type) : list A -> list A -> list A -> Prop :=
| test2poly : forall (l: list A), test_poly_param A l l l.

MetaCoq Run (tmQuote test_poly_param >>= 
linearize_from_mind_entry). 

Inductive test2pars (A : Type) (a b : A) : A -> A -> Prop :=
| test2pars_constructor :
test2pars A a b a b.

Inductive test2pars_linear (A : Type) (HA : CompDec A) (a b : A) : A -> A -> Prop :=
|test2pars_constructor_linear : forall x, x = a -> 
forall y, y = b -> test2pars_linear A HA a b x y.

Inductive test2pars2 (A : Type) (HA : CompDec A) (a b : A) : A -> A -> Prop :=
| test2pars_constructor2 :
test2pars2 A HA a b a b.

(* MetaCoq Quote Recursively Definition entry_test := test2pars2.

MetaCoq Quote Recursively Definition goal_test := test2pars_linear. *)

Inductive bar : nat -> nat -> nat -> nat -> Prop :=
| barc : forall n k, bar k n k n.

MetaCoq Run (tmQuote bar >>= 
linearize_from_mind_entry). 

MetaCoq Run (tmQuote (@test2pars) >>= 
linearize_from_mind_entry). 

(* Linearization in functions *) 
Inductive square : nat -> nat -> Prop :=
| IsSquare : forall n, square n (n*n).

MetaCoq Run (tmQuote square >>= 
linearize_from_mind_entry).

Inductive foo : nat -> nat -> Prop :=
| fooc : forall n, foo n n -> foo n n.

MetaCoq Run (tmQuote foo >>= 
linearize_from_mind_entry). 

End tests.






