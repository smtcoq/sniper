Require Import utilities.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Printf.
Import Unsafe.
From MetaCoq.Template Require Import All.
From MetaCoq.Common Require Import config.

(* Number of parameters of the inductive corresponding to a
given constructor *) 

Ltac npars c :=
  let c_quoted := metacoq_get_value (tmQuoteRec c) in
  let c_term := eval cbv in c_quoted.2 in
    match c_term with
      | tConstruct ?ind _  ?inst => 
        let info := eval cbv in (info_nonmutual_inductive c_quoted.1 (tInd ind inst)) in 
          match info with
            | (?n, _) => pose n
            | _ => fail ind
          end
      | _ => fail "not a constructor"
     end.

Ltac2 rec nat_to_int (n : constr) :=
  match! n with
    | 0 => 0
    | S ?x => Int.add 1 (nat_to_int x)
  end.

Ltac2 npars_of_constructor c :=
  let c := Ltac1.of_constr c in
  ltac1:(c |- npars c) c ;
  let hs := Control.hyps () in 
  let (id, n_def, ty) := List.last hs in
    match n_def with
      | None => Control.throw (Invalid_argument None)
      | Some n => clear $id ; nat_to_int n
    end.

(*
Goal False.
let x := npars '(@nil) in printf "%i" x.
let x := npars '(@pair) in printf "%i" x.
let x := npars 'List.Add_head in printf "%i" x.
Abort. *)

Ltac2 rec print_constr_list (l : constr list) :=
  match l with
    | [] => printf "empty list"
    | x :: xs => printf "%t" x ; print_constr_list xs
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

Ltac2 contexts_printer c := 
  List.iter (fun (x, y) => printf "term: %t" x ;
  List.iter (fun z => printf "context: %t" z) y) c.

Ltac2 inst_state_printer is :=
  let hi := is.(hyps_inst) in
  let ti := is.(types_inst) in
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

(* if c is not closed we change it into a hole *)

Ltac2 change_into_wildcards (c: constr) :=
if is_closed c then c else 'wildcard.

Ltac2 transform_into_context (c: constr) :=
  match kind c with
    | App c ca => let x := 
          Unsafe.make (App c (Array.map change_into_wildcards ca)) in 
           x
    | _ => Control.throw Wrong_context
  end.
(* 
replaces a constructor c t1 ... tk with  
I t1 ... tl with l is the nb of parameters of I and 
I is the inductive whose constructor is c *)

Ltac2 replace_by_inductive (c : constr) := 
  match kind c with
    | App c' ca => 
        if is_constructor c' then 
          let la := Array.to_list ca in
          let la' := List.firstn (npars_of_constructor c') la in
          let ca' := Array.of_list la' in
          let res := transform_into_context (make (App c' ca')) in
          type res
        else c 
    | _ => c
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
    | App c' ca => 
          match kind c' with
            | Rel _ => false
            | _ => Bool.and (is_ind c') (codomain_not_prop c')
          end
    | _ => false
  end.

(* 
Not possible to quote ill-typed terms, but possible to build them:
Ltac2 Eval (let c := make (App 'nat (Array.of_list ['nat])) in equal c 'nat). *)

(* Ltac2 Eval is_inductive_codomain_not_prop_applied '(list nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied '(eq nat).
Ltac2 Eval is_inductive_codomain_not_prop_applied 'bool. *)
 
Ltac2 find_context_hyp_aux (c: constr) :=
  let c' := substnl ['type_variable] 0 c in
  let subsnary := subterms_nary_app c' in
  let subs := List.map replace_by_inductive subsnary in
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
                          (x, Unsafe.make (App c0 ca''))) ca')
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

Ltac2 rec hyp_is_dup_aux (id : ident) (ty : constr) hs :=
  match hs with
    | (id', _, ty') :: xs => Bool.or (Bool.and (equal ty ty') (Bool.neg (Ident.equal id id'))) (hyp_is_dup_aux id ty xs)
    | _ => false
  end.

Ltac2 hyp_is_dup (id : ident) (h : constr) :=
  hyp_is_dup_aux id (type h) (Control.hyps ()).

Ltac2 rec hyp_is_dup_aux2 (ty : constr) hs :=
  match hs with
    | (id', _, ty') :: xs => Bool.or (equal ty ty') (hyp_is_dup_aux2 ty xs)
    | _ => false
  end.

Ltac2 hyp_is_dup2 (ty : constr) :=
  hyp_is_dup_aux2 ty (Control.hyps ()).

Ltac2 specialize_hyp 
  (h : constr) 
  (tyi : constr) :=
    let ty_h := type h in
    match kind ty_h with
      | Prod bd a =>
          let ty := Binder.type bd in
          if is_type_or_set ty then
            if hyp_is_dup2 (substnl [tyi] 0 a) then () 
            else let h' := pose_proof_return_term h in
          specialize ($h' $tyi)
          else ()
      | _ => ()
    end.
     

(* Ltac2 specialize_hyp
  (h : constr)
  (ty : constr) :=
    match! type h with
      | forall (A: Type), _ => 
          let h' := pose_proof_return_term h in
          specialize ($h' $ty) ;
            match kind h' with
              | Var id => if (hyp_is_dup id h') then clear $id else ()
              | _ => ()
            end
      | _ => () 
    end. *)

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

(* Ltac2 Eval context_equal '(type_variable * wildcard)%type '(type_variable * nat)%type. *)

Ltac2 might_specialize_hyp 
  (h : constr) (* the hypothesis that might be specialized *)
  (ctx_h : constr) (* the context in which its type variable lies *)
  (ty : constr) (* the type *)
  (ctx_ty : constr) (* the context in which the type lies *)
    := if context_equal ctx_h ctx_ty then specialize_hyp h ty else
    ().

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

Ltac2 is_empty l :=
  match l with
   | [] => true
   | _ => false
  end.
 

Ltac2 instantiate_state isr :=
  match isr with
    | ISR is => 
        let state := get is in
        let hyp_ctx_l := state.(hyps_inst) in 
        if is_empty hyp_ctx_l then () else
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

(* TODO
(* Specific instantiation considering only the new hypothesis
containing a concrete type of type Type or Set *)
Ltac2 new_hyp_concrete_type 
  (isr : refs) 
  (h : constr) :=
  let tyi := find_context_types (type h) in 
    match isr with
      | ISR is =>
          let res := get is in 
          setref is { hyps_inst := res.(hyps_inst) ; types_inst := List.append (res.(types_inst)) tyi }
          might_instantiate_type tyi res.(hyps_inst)
      | _ => Control.throw Wrong_reference
    end.  *)

(** Temporary hack before adding a state: we apply the transformation
 as much as the maximum number of prenex quantifiers over Type of an hypothesis **)

Ltac2 max_quantifiers () : int :=
  let hs := Control.hyps () in
  let rec aux hs max :=
    match hs with
      | [] => max
      | (id, opt, ty) :: hs' => 
          match opt with
            | Some _ => aux hs' max
            | None => 
                let res := 
                let rec aux2 ty nb :=
                  match kind ty with
                    | Prod bd ty' => 
                        let typb := Binder.type bd in 
                        if is_type_or_set typb then aux2 ty' (Int.add nb 1)
                        else nb
                    | _ => nb
                end in aux2 ty 0 in
                  if Int.le res max then aux hs' max else aux hs' res
          end
    end
  in aux hs 0.

(* Tests *)

(* Goal ((forall (A B C D E: Type), A) -> (forall (B : Type), B) -> False).
Proof. intros. let x := max_quantifiers () in printf "%i" x. Abort. *)


(* Result printer *)
Ltac2 elimination_polymorphism_printer () :=
  let ref := ISR (ref (compute_init_state ())) in isr_printer ref.

Ltac2 elimination_polymorphism () :=
  let ref := ISR (ref (compute_init_state ())) in instantiate_state ref.

Ltac clear_prenex_poly_hyps_in_context := repeat match goal with 
| H : forall (A : ?T), _ |- _ => first [ constr_eq T Set | constr_eq T Type] ; 
let T := type of H in let U := type of T in tryif (constr_eq U Prop) then try (clear H)
else fail
end.

Tactic Notation "elimination_polymorphism" := 
  ltac2:(Notations.do0 max_quantifiers elimination_polymorphism) ;
  clear_prenex_poly_hyps_in_context.

Tactic Notation "elimination_polymorphism_printer" :=
    ltac2:(Notations.do0 max_quantifiers elimination_polymorphism_printer).

Require Import List.
Import ListNotations.

Section tests.
Set Default Proof Mode "Classic".

Goal (forall (A: Type) (x: list A), x = x) -> (forall (x: list nat), x = x).
intros H.
elimination_polymorphism. assumption.
Abort.

Lemma test_clever_instances : forall (A B C D E : Type) (l : list A) (l' : list B)
(p : C * D) (p' : D*E), l = l -> l' = l' -> p = p -> (forall (A : Type) (x : A), x= x)
-> (forall (A : Type) (l : list A), l = l) -> (forall (A B : Type) (p : A *B), p =p ) ->
p' = p'.
intros.
elimination_polymorphism.
Abort.

Goal (forall (A: Type), list A -> False).
intros. assert (H1: forall A, List.nth_error (@nil A) 0 = None) by auto.
elimination_polymorphism.
assert (H2: @nth_error A (@nil A) 0 = @None A) by assumption. Abort.

Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. elimination_polymorphism. split. assumption.
split. assumption. assumption. Qed.

Fixpoint zip {A B : Type} (l : list A) (l' : list B) :=
  match l, l' with
  | [], _ => []
  | x :: xs, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys 
  end.

Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C) (l : list A),
let f0 := fun x : A => (f x, g x) in
(forall (H7 H9 : Type) (H10 : H7 -> H9), map H10 [] = []) ->
(forall (H7 H9 : Type) (H10 : H7 -> H9) (h : H7) (l0 : list H7),
 map H10 (h :: l0) = H10 h :: map H10 l0) ->
map f0 l = zip (map f l) (map g l)).
Proof. intros. 
elimination_polymorphism.
Abort.

Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C) (l : list A),
let f0 := fun x : A => (f x, g x) in
(forall (H7 H9 : Type) (H10 : H7 -> H9), map H10 [] = []) ->
(forall (H7 H9 : Type) (H10 : H7 -> H9) (h : H7) (l0 : list H7),
 map H10 (h :: l0) = H10 h :: map H10 l0) ->
map f0 l = zip (map f l) (map g l)).
Proof. intros.
elimination_polymorphism.
Abort.

Goal (forall A B C : Type,
forall (f : A -> B) (g : A -> C),
let f0 := fun x : A => (f x, g x) in
let f1 := @map A (B * C) f0 in
let f2 := @map A B f in
let f3 := @map A C g in
(forall (H5 H7 : Type) (l' : list H7), @zip H5 H7 [] l' = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7), @zip H7 H9 (H10 :: H11) [] = []) ->
(forall (H7 H9 : Type) (H10 : H7) (H11 : list H7) (h : H9) (l : list H9),
 @zip H7 H9 (H10 :: H11) (h :: l) = (H10, h) :: @zip H7 H9 H11 l) ->
f1 [] = [] ->
(forall (a : A) (l : list A), f1 (a :: l) = f0 a :: f1 l) ->
f2 [] = [] ->
(forall (a : A) (l : list A), f2 (a :: l) = f a :: f2 l) ->
f3 [] = [] ->
(forall (a : A) (l : list A), f3 (a :: l) = g a :: f3 l) ->
(forall (x : Type) (x0 x1 : x) (x2 x3 : list x), x0 :: x2 = x1 :: x3 -> x0 = x1 /\ x2 = x3) ->
(forall (x : Type) (x0 : x) (x1 : list x), [] = x0 :: x1 -> False) ->
(forall (x x0 : Type) (x1 x2 : x) (x3 x4 : x0), (x1, x3) = (x2, x4) -> x1 = x2 /\ x3 = x4) -> 
f1 [] = @zip B C (f2 []) (f3 [])).
Proof. intros. elimination_polymorphism. assumption. Abort.
 

End tests.

Section big_test.

Variable (A B C : Type).
Variable (CompDec : Type -> Type).
Variable (HA : CompDec A).
Variable (HB : CompDec B).
Variable (HC : CompDec C).

Goal (forall (f : A -> B) (g : B -> C) (a: A) (l : list A),
(map g (map f l) = map (fun x : A => g (f x)) l) ->
let f0 := (fun x : A => g (f x)) in
(forall x : A, f0 x = g (f x)) ->
let f1 := map g in
let f2 := map f in
let f3 := map f0 in
let f4 := map f0 in 
f1 nil = nil -> 
forall (b : B) (l : list B), f1 (b :: l) = g b :: map g l ->
f2 nil = nil ->
forall (a : A) (l : list A), f2 (a :: l) = f a :: map f l ->
f3 nil = nil ->
f4 nil = nil -> 
(forall (a : A) (l : list A), f3 (a :: l) = f0 a :: map f0 l) ->  
(forall (x : Type) (x0 x1 : x) (x2 x3 : list x),
         x0 :: x2 = x1 :: x3 -> x0 = x1 /\ x2 = x3) ->  
(forall (x : Type) (x0 : x) (x1 : list x), nil = x0 :: x1 -> False) ->
let proj_list := (fun (A : Type) (x x0 : list A) =>
                match x0 with
                | nil => x
                | _ :: x2 => x2
                end) in 
let proj_list0 := (fun (A : Type) (x : A) (x0 : list A) =>
                 match x0 with
                 | nil => x
                 | x1 :: _ => x1
                 end) in
(forall x : list A,
                x = nil \/ x = proj_list0 A a x :: proj_list A l x) ->
(forall (H13 : Type) (H15 : list H13), proj_list H13 H15 nil = H15) ->
(forall (H13 : Type) (H15 : list H13) (h : H13) (l : list H13),
          proj_list H13 H15 (h :: l) = l) ->
(forall (H15 : Type) (H17 : H15), proj_list0 H15 H17 nil = H17)   ->
(forall (H15 : Type) (H17 h : H15) (l : list H15),
          proj_list0 H15 H17 (h :: l) = h) -> map g (map f (a :: l)) = map f0 (a :: l)).
intros. elimination_polymorphism. Abort.

End big_test.



