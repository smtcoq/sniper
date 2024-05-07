From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Unsafe.

Ltac2 Type 'a ref := 'a Init.ref.

Ltac2 ref (v : 'a) : 'a ref := { contents := v}.
Ltac2 get (r : 'a ref) : 'a := r.(contents).
Ltac2 set (r : 'a ref) (v : 'a) : unit := r.(contents) := v.

Ltac2 update (r : 'a ref) (f : 'a -> 'a) : unit :=
  r.(contents) := f (r.(contents)).

Ltac2 Type refs := [ .. ].

Ltac2 is_type_or_set (c: constr) :=
  match kind c with
    | Sort s => Bool.and (Bool.neg (equal c 'Prop)) (Bool.neg (equal c 'SProp))
    | _ => false
  end.

(* Ltac2 Eval is_type_or_set 'Set.
Ltac2 Eval is_type_or_set 'Type.
Ltac2 Eval is_type_or_set 'nat.
Ltac2 Eval is_type_or_set 'Prop.
Ltac2 Eval is_type_or_set 'SProp. *)

(* A state is a two-fields record in which the first field 
contains pairs between a type and a context for this type, 
the second field contains pairs between a hypothesis and 
a context for the first type variable used in the hypothesis *)

Ltac2 Type instantiation_state :=
  { types_inst : (constr*constr) list;
    hyps_inst : (constr*constr) list }.

Definition wildcard := true.

Ltac2 Type refs ::= [ ISR (instantiation_state ref) ].

(* subterms_nary_app of c, but if a subterm is
of the form f a1 ... ak, the only subterms_nary_app considered are the subterms_nary_app 
of f and of each of the ais, but not the partial 
applications (f a1), (f a1 a2) etc. *)
Ltac2 rec subterms_nary_app (c : constr) : constr list :=
  match kind c with
    | Rel _ => [c]
    | Var _ => [c]
    | Meta _ => [c]
    | Evar _ ca =>
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in List.append [c] res'
    | Sort _ => [c]
    | Cast c1 _ c2 => List.append [c] (List.append (subterms_nary_app c1) (subterms_nary_app c2))
    | Prod bd c2 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms_nary_app c1) (subterms_nary_app c2))
    | Lambda bd c2 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms_nary_app c1) (subterms_nary_app c2))
    | LetIn bd c2 c3 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms_nary_app c1) (List.append (subterms_nary_app c2) (subterms_nary_app c3)))
    | App c1 ca => 
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in 
        List.append [c] (List.append (subterms_nary_app c1) res')
    | Constant _ _ => [c]
    | Ind _ _ => [c]
    | Constructor _ _ => [c]
    | Case _ c1 _ c2 ca => 
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in 
        List.append [c] (List.append (List.append (subterms_nary_app c1) (subterms_nary_app c2)) res')
    | Fix _ _ ba ca => 
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in 
        let l' := Array.to_list ba in
        let res1 := List.map (fun x => subterms_nary_app (Binder.type x)) l' in
        let res1' := List.flatten res1 in
        List.append [c] (List.append res' res1')
    | CoFix _ ba ca =>
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in 
        let l' := Array.to_list ba in
        let res1 := List.map (fun x => subterms_nary_app (Binder.type x)) l' in
        let res1' := List.flatten res1 in
        List.append [c] (List.append res' res1')
    | Proj _ c1 => List.append [c] (subterms_nary_app c1)
    | Uint63 _ => [c]
    | Float _ => [c]
    | Array _ ca c1 c2 => 
        let l := Array.to_list ca in
        let res := List.map subterms_nary_app l in
        let res' := List.flatten res in 
        List.append [c] (List.append (List.append (subterms_nary_app c1) (subterms_nary_app c2)) res')
  end.

(* Ltac2 Eval subterms_nary_app '(forall (A: Type) (x: A), @eq A x x). *)

(* TODO factorize because defined in triggers_tactics.v *)

Ltac2 rec codomain_not_prop_aux (c: constr) :=
  match kind c with
  | Prod bi c' => codomain_not_prop_aux c'
  | App x1 arr => codomain_not_prop_aux x1
  | _ => if equal c 'Prop then false else true
  end.

Ltac2 codomain_not_prop (c: constr) := codomain_not_prop_aux (type c).

Ltac2 is_inductive_codomain_not_prop_applied (c: constr) :=
  match kind c with
    | App c' ca => Bool.and (is_ind c') (codomain_not_prop c')
    | _ => false
  end.

(* Ltac2 Eval is_inductive_codomain_not_prop_applied '(list nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied '(eq nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied 'bool. *)

Ltac2 transform_into_contexts (c: constr) := ().
 
Ltac2 find_context_hyp_aux (c: constr) :=
  let subs := subterms_nary_app c in
  let subsindu := List.filter is_inductive_codomain_not_prop_applied subs in
  let subsindurel := 
    List.filter (fun x => 
      match kind x with
        | App c' ca => Array.mem equal (make (Rel 1)) ca
        | _ => false
      end) subsindu in
  List.map transform_into_contexts subsindurel.


(* We suppose that h : forall (A: Type), P A 
- Look at all the subterms_nary_app of h containing A
- Filter the inductives applied 
- return the list of contexts (parameters replaced by either wildcards 
or lambda-abstraction on A)
*)

Ltac2 find_context_hyp (h: constr) :=
  match kind (type h) with
    | Prod bd c2 =>
        let c1 := Binder.type bd in 
        if is_type_or_set c1 then find_context_hyp_aux c2
        else []
    | _ => []
  end.
        
  





