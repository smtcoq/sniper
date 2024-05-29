From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Printf.
Import Unsafe.

Ltac2 rec print_constr_list (l : constr list) :=
  match l with
    | [] => ()
    | x :: xs => printf "%t \n" x ; print_constr_list xs
  end.

Ltac2 Type 'a ref := 'a Init.ref.

Ltac2 ref (v : 'a) : 'a ref := { contents := v}.
Ltac2 get (r : 'a ref) : 'a := r.(contents).
Ltac2 setref (r : 'a ref) (v : 'a) : unit := r.(contents) := v.

Ltac2 update (r : 'a ref) (f : 'a -> 'a) : unit :=
  r.(contents) := f (r.(contents)).


Ltac2 Type exn ::= [ Wrong_context ].

Ltac2 Type exn ::= [ Wrong_reference ].

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

(* For this transformation, 
a state is a two-fields record in which the first field 
contains a list of pairs between a type and a context for this type, 
the second field contains a list of pairs between a hypothesis and 
a context for the first type variable used in the hypothesis *)

Ltac2 Type instantiation_state :=
  { hyps_inst : (constr * constr list) list;
    types_inst : (constr * constr list) list
     }.

Definition wildcard := nat.

Definition type_variable := nat.

Ltac2 Type refs ::= [ ISR (instantiation_state ref) ].

Ltac2 inst_state_printer is :=
  let hi := is.(hyps_inst) in
  let ti := is.(types_inst) in
  printf "hyps inst:";
  List.iter (fun (x, y) => printf "hypothesis: %t" x ;
    List.iter (fun z => printf "context: %t" z) y) hi ;
  printf "types inst:" ;
  List.iter (fun (x, y) => printf "type: %t" x ;
    List.iter (fun z => printf "context: %t" z) y) ti.


Ltac2 isr_printer isr :=
  match isr with
    | ISR is =>
        inst_state_printer (is.(contents))
    | _ => Control.throw Wrong_reference
  end.

(* subterms of c, but if a subterm is
of the form f a1 ... ak, the only subterms considered are the subterms
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

(* 
Not possible to quote ill-typed terms, but possible to build them:
Ltac2 Eval (let c := make (App 'nat (Array.of_list ['nat])) in equal c 'nat). *)

(* Ltac2 Eval is_inductive_codomain_not_prop_applied '(list nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied '(eq nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied 'bool. *)

(* if c is not closed we change it into a hole *)

Ltac2 change_into_wildcards (c: constr) :=
if is_closed c then c else 'wildcard.

Ltac2 transform_into_context (c: constr) :=
  match kind c with
    | App c ca => make (App c (Array.map change_into_wildcards ca))
    | _ => Control.throw Wrong_context
  end.
 
Ltac2 find_context_hyp_aux (c: constr) :=
  let c' := substnl ['type_variable] 0 c in
  let subs := subterms_nary_app c' in
  let subsindu := List.filter is_inductive_codomain_not_prop_applied subs in
  let subsindurel := 
    List.filter (fun x => 
      match kind x with
        | App c' ca => Array.mem equal 'type_variable ca
        | _ => false
      end) subsindu in
  List.map transform_into_context subsindurel.


(* We suppose that h : forall (A: Type), P A 
- Look at all the subterms of h containing A
- Filter the inductives applied 
- return the list of contexts (parameters replaced by either wildcards 
or a term called type_variable which represents A)
*)

Ltac2 find_context_hyp (h: constr) :=
  match kind (type h) with
    | Prod bd c2 =>
        let c1 := Binder.type bd in 
        if is_type_or_set c1 then 
        (h, List.nodup equal (find_context_hyp_aux c2))
        else (h, [])
    | _ => (h, [])
  end.


(*Tests :
Require Import List. 

Axiom toto : forall (A: Type) (l : list (list A)) (x : prod A nat), l = l /\ x = x.

Ltac2 Eval find_context_hyp 'toto.
Ltac2 Eval find_context_hyp 'app_nil_r.
Ltac2 Eval find_context_hyp 'surjective_pairing. *)

Ltac2 list_context_types (c : constr) :=
  match kind c with
    | App c0 ca => 
        let ca' := (Array.map change_into_wildcards ca) in
        Array.to_list (Array.mapi 
                        (fun i x => 
                            let ca'' := Array.copy ca' in 
                            Array.set ca'' i 'type_variable ;
                          (x, make (App c0 ca''))) ca')
    | _ => Control.throw Wrong_context
  end.

Ltac2 find_context_types_aux (c : constr) :=
  let subs := subterms_nary_app c in
  let subsindu := List.filter is_inductive_codomain_not_prop_applied subs in
  let res := 
  List.nodup 
    (fun a b => 
      let (a1, a2) := a in
      let (b1, b2) := b in
      Bool.and (equal a1 b1) (equal a2 b2))
    (List.flatten (List.map list_context_types subsindu)) in
  List.filter (fun (x, y) => Bool.neg (equal x 'wildcard)) res.

Ltac2 rec reorder_context_types_aux  (c : constr) (l : (constr*constr) list) :=
  match l with
    | [] => (c, [])
    | (x, y) :: xs => 
        let (_, res) := reorder_context_types_aux c xs in
        if equal x c then (c, y :: res) 
        else (c, res)
  end.

Ltac2 equal_key_value :=
  (fun a b => 
    let (a1, a2) := a in
    let (b1, b2) := b in
    Bool.and (equal a1 b1) (List.equal equal a2 b2)). 

Ltac2 reorder_context_types (l : (constr*constr) list) := 
 List.nodup equal_key_value (List.map (fun (x, _) => reorder_context_types_aux x l) l).

Ltac2 find_context_types c := reorder_context_types (find_context_types_aux c). 

(*Tests : 
Require Import List. 

Axiom toto : forall (l : list (list nat)) (x : prod bool nat), l = l /\ x = x.
Axiom tutu : forall (A: Type) (l : list (list nat)) (x : prod A nat), l = l /\ x = x.

Ltac2 Eval find_context_types (type 'toto).
Ltac2 Eval find_context_types (type 'tutu).
Ltac2 Eval find_context_types (type 'surjective_pairing). *)

Ltac2 pose_proof_return_term (h: constr) :=
  let fresh_id := Fresh.in_goal ident:(H_inst) in
  pose ($fresh_id := $h) ;
  ltac1:(H_inst |- clearbody H_inst) (Ltac1.of_ident fresh_id) ; Control.hyp fresh_id. 

(* Goal ((forall (x : nat), x = x) -> False).
intros H_inst.
let x := pose_proof 'H_inst in printf "%t" x. Abort. *)

Ltac2 specialize_hyp
  (h : constr)
  (ty : constr) :=
    match! type h with
      | forall (A: Type), _ => 
          let h' := pose_proof_return_term h in
          specialize ($h' $ty)
      | _ => ()
    end. 

(* 
Goal ((forall (B : Type), B = B) -> False).
intros H_inst.
specialize_hyp 'H_inst 'nat.
specialize_hyp 'H_inst 'bool.
specialize_hyp 'H_inst 'unit.
specialize_hyp 'H_inst1 'nat.
Abort. *)

Ltac2 rec context_equal c1 c2 :=
  if equal c1 'wildcard then true
    else if equal c2 'wildcard then true
      else if
        match kind c1, kind c2 with
          | App c3 ca, App c4 cb =>
              let la := Array.to_list ca in
              let lb := Array.to_list cb in
              Bool.and (equal c3 c4) (List.equal context_equal la lb)
          | _ => false
        end then true
  else equal c1 c2.

(* Tests *)

Ltac2 Eval context_equal '(type_variable * wildcard)%type '(type_variable * nat)%type.

Ltac2 might_specialize_hyp 
  (h : constr) (* the hypothesis that might be specialized *)
  (ctx_h : constr) (* the context in which its type variable lies *)
  (ty : constr) (* the type *)
  (ctx_ty : constr) (* the context in which the type lies *)
    := if context_equal ctx_h ctx_ty then specialize_hyp h ty else ().

(* (constr * constr list) list *)

Ltac2 might_specialize_hyp_list 
  (h : constr) (* the hypothesis that might be specialized *)
  (ctx_h : constr) (* the context in which its type variable lies *)
  (ty : constr) (* the type *)
  (ctxs_ty : constr list) (* the context in which the type lies *)
    := List.iter (might_specialize_hyp h ctx_h ty) ctxs_ty.


Ltac2 might_specialize_hyp_list_list 
  (h : constr) (* the hypothesis that might be specialized *)
  (ctxs_h : constr list) (* the contexts in which its type variable lies *)
  (ctxs_ty : (constr * constr list) list ) (* the type * the contexts in which the type lies *)
    := List.iter (fun (x, y) => List.iter (fun ctx_h => might_specialize_hyp_list h ctx_h x y) ctxs_h) ctxs_ty.
 

Ltac2 instantiate_state isr :=
  match isr with
    | ISR is => 
        let state := get is in
        let hyp_ctx_l := state.(hyps_inst) in
        let ty_ctx_l := state.(types_inst) in
        List.iter (fun (x, y) => might_specialize_hyp_list_list x y ty_ctx_l) hyp_ctx_l
    | _ => Control.throw Wrong_reference
  end.

Ltac2 is_polymorphic (c: constr) :=
  match kind c with
    | Prod bd _ => let ty := Binder.type bd in is_type_or_set ty
    | _ => false
  end.

Ltac2 rec poly_hyps_of_type_prop_as_terms (hs: (ident*(constr option)*constr) list) :=
  match hs with
    | (id, opt, ty) :: hs' => 
        match opt with
          | Some _ => poly_hyps_of_type_prop_as_terms hs'
          | None => 
              if Bool.and (equal (type ty) 'Prop) (is_polymorphic ty) then 
                Control.hyp id :: poly_hyps_of_type_prop_as_terms hs'
              else poly_hyps_of_type_prop_as_terms hs'
        end
    | [] => []
  end.

Ltac2 rec hyps_as_terms (hs: (ident*(constr option)*constr) list) :=
  List.map (fun (x, y, z) => Control.hyp x) hs.

Ltac2 compute_init_state () :=
  let hyps := Control.hyps () in
  let g := Control.goal () in
  let hyps_constr := poly_hyps_of_type_prop_as_terms hyps in
  let hyps_constr' := hyps_as_terms hyps in
  let context_hyps := List.map (fun x => find_context_hyp x) hyps_constr in
  let context_types := 
    List.append 
      (List.fold_left (fun acc x => List.append (find_context_types (type x)) acc) hyps_constr' [])
      (find_context_types g) in
  {
   hyps_inst := context_hyps;
   types_inst := context_types 
  }.

Ltac2 init_state (isr : refs) :=
let s := compute_init_state () in 
  match isr with
    | ISR is =>
        setref is s
    | _ => Control.throw Wrong_reference
  end.

Section tests.

Goal (forall (A: Type) (x: list A), x = x) -> (forall (x: list nat), x = x).
intros H.
let ref := ISR (ref (compute_init_state ())) in instantiate_state ref.
Abort.

Lemma test_clever_instances : forall (A B C D E : Type) (l : list A) (l' : list B)
(p : C * D) (p' : D*E), l = l -> l' = l' -> p = p -> (forall (A : Type) (x : A), x= x)
-> (forall (A : Type) (l : list A), l = l) -> (forall (A B : Type) (p : A *B), p =p ) ->
p' = p'.
intros.
let ref := ISR (ref (compute_init_state ())) in instantiate_state ref.
let ref := ISR (ref (compute_init_state ())) in instantiate_state ref.
Abort.






