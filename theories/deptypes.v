Require Import MetaCoq.Template.All.
From MetaCoq.PCUIC Require Import PCUICReflect.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Import MCMonadNotation.
Require Import utilities.
Require Import List.
Require Import String.
Import ListNotations.
Unset MetaCoq Strict Unquote Universe Mode.

(** Description of the transformation elim_nondep_functional_arity

A non-mutual and non-recursive inductive

I (P1 : T1) ... (Pk : Tk) : Type -> ... -> Type := (with l types)
| C1 x11 ... x1m : I P1 ... Pk TyC11 ... TyC1l
...
| Cn xn1 ... xnm : I P1 ... Pk TyCn1 ... TyCnl.

where all the TyCijs are closed types with prenex quantification over
type variables

is transformed into an inductive 
I' (P1 : T1) ... (Pk : Tk) : Type :=
| C1' trm_tag_TyC11 ... trm_tagTyC1l x11 ... x1m : I' P1 ... Pk
...
| Cn' trm_tag_TyCn1 ... trm_tagTyCnl xn1 ... xnm : I' P1 ... Pk.

All the closed types which are not dependent functions
are replaced by arguments of an inductive 
isomorphic to unit. 
All the closes type which are dependent functions are replaced
by a arguments of an inductive taking these terms as parameters.
For each closed type, one is created, and we provide already 
created typ_tag for frequent types such as nat, bool or unit *)

Inductive typ_tag_nat := trm_tag_nat.

Inductive typ_tag_unit := trm_tag_unit.

Inductive typ_tag_bool := trm_tag_bool.

Inductive typ_tag_list (A: Type) := trm_tag_list : typ_tag_list A.

Inductive typ_tag_id (A : Type) := trm_tag_id : typ_tag_id A.

Inductive typ_tag_prod (A B : Type) := trm_tag_prod : typ_tag_prod A B.

Definition base_mapping_tags_terms 
  : list (term*term):= 
  [(<%nat%>, <%typ_tag_nat%>); 
  (<%bool%>, <%typ_tag_bool%>);
  (<%unit%>, <%typ_tag_unit%>);
  (<%@list%>, <%trm_tag_list%>);
  (<%@id%>, <%typ_tag_id%>);
  (<%@prod%>, <%typ_tag_prod%>)].

MetaCoq Quote Recursively Definition prod_reif_rec := @prod.

(** Step 1: find the number of indexes of type Type or Set in the inductive *)

Fixpoint skipn_prods (n : nat) (t : term) :=
  match n with
    | 0 => t
    | S n => 
      match t with
       | tProd na Ty u => skipn_prods n u
       | _ => t
      end
    end.

Fixpoint nb_args_codomain_type_or_set (t: term) : option nat :=
  match t with
    | tProd _ Ty u => 
      match Ty with
        | tSort s => if Universe.is_prop s then None else
          match (nb_args_codomain_type_or_set u) with
           | Some x => Some (S x)
           | None => None
          end
        | _ => None
        end
    | _ => Some 0
end.

Definition find_nbr_arity mind : option nat :=
  let (x, y) := (mind.(ind_npars), (List.hd default_body mind.(ind_bodies)))
                    in 
                   let Ty_ind := y.(ind_type) in
                   nb_args_codomain_type_or_set (skipn_prods x Ty_ind).

(** Step 2: look at the codomain of constructors and get from npars to npars + nbarity 
arguments of return type *)

Fixpoint codomain (t: term) :=
  match t with
    | tProd Na Ty u => codomain u
    | _ => t
  end.

Definition drop_nargs (n : nat) (t : term) :=
  match t with
    | tApp _ l => List.skipn n l 
    | _ => []
  end.

Definition index_args_in_codomain_of_constructors mind :=
  let (npars, ty_cstr) :=  (mind.(ind_npars), (hd default_body mind.(ind_bodies)).(ind_ctors)) in
  let fix aux ty_cstr :=
  match ty_cstr with
    | x :: xs => drop_nargs npars (codomain x.(cstr_type)) :: aux xs 
    | [] => []
  end
  in aux ty_cstr.

(** Step  3: creating the tag for all arguments we obtained (if it does not exist) *)

Fixpoint buildn_params_type (npars: nat) :=
  match npars with
    | 0 => []
    | S n' =>
      let s := string_of_nat npars in
      {| decl_name := mkNamed (String.append ("A")%bs s); 
      decl_body := None; decl_type := tSort (fresh_universe) |} :: buildn_params_type n'
  end.

(* Build the type forall (A1 : Type) ... (Anpars : Type), I A1 ... An 
The I is an inductive represented by its de Brujin index *)
Fixpoint mkProd_type (npars : nat) (deBrujinindex_inductive : nat) :=
  if Nat.eqb deBrujinindex_inductive 0 then tRel 0 else
  match npars with
    | 0 => <%Set%>
    | S n => let s := string_of_nat (deBrujinindex_inductive-npars) in
      tProd (mkNamed (String.append ("A")%bs s)) (<%Type%>) (mkProd_type n deBrujinindex_inductive)
  end. Print LevelSet.

Definition create_tag_oind npars id : one_inductive_entry :=
  {| 
    mind_entry_typename := (String.append ("typ_tag_") id);
    mind_entry_arity := <%Set%> ;
    mind_entry_consnames := [(String.append ("trm_tag_") id)];
    mind_entry_lc := [tApp (tRel (npars)) (Rel_list npars 0)];
   |}.

(* Creates an inductive tag (as a mutual_inductive_entry) 
with npars parameters of type Type *)
Definition create_tag_mind (npars : nat) (id : ident) : mutual_inductive_entry :=
  {| 
    mind_entry_record := None;
    mind_entry_finite := Finite; (* not corecursive *)
    mind_entry_params := buildn_params_type npars;
    mind_entry_inds := [create_tag_oind npars id];
    mind_entry_universes := Monomorphic_entry ContextSet.empty; 
    mind_entry_template := false; 
    mind_entry_variance := None;
    mind_entry_private := None;
  |}. 

(* Tests : 

Definition create_tag_test (npars : nat) (id : ident) :=
tmMkInductive true (create_tag_mind npars id).

MetaCoq Run (create_tag_test 0 "unit2" %bs).
MetaCoq Run (create_tag_test 1 "list2"%bs).
MetaCoq Run (create_tag_test 2 "prod2"%bs). *)

Fixpoint find_kername (kn : kername) (l : list (term*term)) : option (term * term) :=
  match l with
    | [] => None
    | (tInd {| inductive_mind := kn' ; inductive_ind := ind |} u, y) :: xs => 
      if eq_kername kn kn' then Some (tInd {| inductive_mind := kn' ; inductive_ind := ind |} u, y) 
      else find_kername kn xs 
    | _ :: xs => find_kername kn xs 
  end. 

Fixpoint count_prenex_foralls (t : term) :=
  match t with
    | tProd Na Ty u => S (count_prenex_foralls u)
    | _ => 0
  end.

Definition create_tag_and_return (npars : nat) (id : ident) :=
fsh <- tmFreshName id ;; 
let mind := create_tag_mind npars id in
tmMkInductive true mind ;;
curmodpath <- tmCurrentModPath tt ;;
let name_indu := (curmodpath, fsh) in
tmReturn (tInd {| inductive_mind := name_indu ; inductive_ind := 0 |} []).

(* Creates all the tags for the types which are not in l_base.
It returns the list of lists of tags needed *)

Fixpoint create_tags (inputs : list term) (l_base : list (term*term)) : 
TemplateMonad (list (term*term)) :=
  match inputs with 
    | [] => tmReturn []
    | x :: xs => 
      match x with
        | tInd {| inductive_mind := kn ; inductive_ind := ind |} u => 
          match find_kername kn l_base with
            | None =>
              mind <- tmQuoteInductive kn  ;;
              y <- create_tag_and_return mind.(ind_npars) kn.2 ;;
              l <- create_tags xs l_base ;; 
              tmReturn ((tInd {| inductive_mind := kn ; inductive_ind := ind |} u, y) :: l)
            | Some y => 
              l <- create_tags xs l_base ;; tmReturn (y :: l)
          end
        | _ => 
          let npars := count_prenex_foralls x in
          y <- create_tag_and_return npars "Typ"%bs ;;
          l <- create_tags xs l_base ;; tmReturn ((x, y) :: l)      
        end
  end.

(** Step 4 : add arguments to constructor's types *)

Fixpoint add_nondep_args (t : term) (l : list term) : term :=
  match l with
   | [] => t
   | x :: xs => tProd (mkNamed "tag"%bs) x (add_nondep_args t xs)
  end.

Fixpoint add_nondep_args_list (l1 : list term) (l2 : list (list term)) :=
  match l1, l2 with
    | [], [] => []
    | x :: xs, y :: ys => add_nondep_args x y :: add_nondep_args_list xs ys
    | _, _ => []
  end.

Definition create_oind_transformed oind ltags : one_inductive_entry :=
  {| 
    mind_entry_typename := (String.append oind.(mind_entry_typename) "'");
    mind_entry_arity := <% Type %> ;
    mind_entry_consnames := List.map (fun x => String.append x "'") oind.(mind_entry_consnames);
    mind_entry_lc := add_nondep_args_list oind.(mind_entry_lc) ltags ;
   |}.

Definition create_mind_transformed mind ltags : mutual_inductive_entry :=
  {| 
    mind_entry_record := mind.(mind_entry_record);
    mind_entry_finite := mind.(mind_entry_finite);
    mind_entry_params := mind.(mind_entry_params);
    mind_entry_inds := List.map (fun x => create_oind_transformed x ltags) 
      mind.(mind_entry_inds);
    mind_entry_universes := mind.(mind_entry_universes); 
    mind_entry_template := mind.(mind_entry_template); 
    mind_entry_variance := mind.(mind_entry_variance);
    mind_entry_private := mind.(mind_entry_private);
  |}. 

(** Step 5 : final transformation *) Print eqb_term.

Fixpoint ty_to_tag s (t : term) (l : list (term*term)) :=
  match l with
    | (x, y) :: xs => if eqb_term (trans s t) (trans s x) then y else ty_to_tag s t xs
    | [] => default_reif
  end.

Definition ty_to_tag_list_of_list s (l1 : list (list term)) (l2 : list (term*term)) :=
  List.map (List.map (fun x => ty_to_tag s x l2)) l1. Print program.

(* Polymorphic Definition elim_type_in_indexes (t : term) :=

tmQuoteInductive (inductive_mind ind0) => on a direct le mind donc adapter
  A_quoted <- tmQuoteRec A ;;
  let s := (trans_global_env A_quoted.1) in 
  match find_nbr_arity A_quoted with
    | None => 
      tmFail "wrong argument given to the transformation"%bs 
    | Some 0 => 
      tmPrint "the transformation does nothing here: the type is not dependent or not handled"%bs
    | Some (S n) => 
      match info_inductive A_quoted.1 A_quoted.2 with
        | None => tmFail "not an inductive"%bs
        | Some indu =>
          let indu_entry := mind_body_to_entry indu in
          let l := index_args_in_codomain_of_constructors A_quoted in
          let lflat := flat_map id l in
          tags_avail <- create_tags lflat base_mapping_tags_terms ;;
          let args_new_constructors := ty_to_tag_list_of_list s l tags_avail in
          tmMkInductive true (create_mind_transformed indu_entry args_new_constructors)
        end
  end. *)


(** Isomorphisms tests **)

Inductive door : Type := Left | Right.

Inductive DOORS : Type -> Type :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

MetaCoq Run (elim_type_in_indexes DOORS).

MetaCoq Quote Recursively Definition DOORS_reif := DOORS. Print DOORS_reif.

Compute index_args_in_codomain_of_constructors DOORS_reif. 





Inductive DOORS' : Type :=
| IsOpen' (t : typ_tag_bool) (d : door) : DOORS'
| Toggle' (t : typ_tag_unit) (d : door) : DOORS'.

Definition coerce (d : DOORS') :=
  match d as y return
  match y with
    | IsOpen' _ _ => DOORS bool
    | Toggle' _ _ => DOORS unit
  end
  with
   | IsOpen' _ d => IsOpen d
   | Toggle' _ d => Toggle d 
  end. Print coerce.

Definition coerce2 (A : Type) (d : DOORS A) : DOORS bool + DOORS unit :=
match d with
   | IsOpen d => inl (IsOpen d)
   | Toggle d => inr (Toggle d) 
  end. Print coerce2.

(* Definition coerce3 (t : DOORS bool + DOORS unit) :=
  match t with
  | inl (IsOpen d) => IsOpen d
  | inl (Toggle d) => IsOpen d
  | inr (IsOpen d) => Toggle d
  | inr (Toggle d) => Toggle d
end.
 *)
Axiom  UIP : forall U (x y:U) (p1 p2:x = y), p1 = p2.

Lemma test A : forall (d : DOORS A), {A = unit} + {A = bool}.
Proof. intro d.
destruct d. auto.
auto. Qed.

Definition test2 := 
fun (A : Type) (d : DOORS A) =>
match
  d as d0 in (DOORS T)
  return
    match d0 with
    | IsOpen _ => T = bool
    | Toggle _ => T = unit
    end
with
| IsOpen d0 => (fun _ : door => eq_refl) d0
| Toggle d0 => (fun _ : door => eq_refl) d0
end. 

(* Definition coerce_recip  {A : Type} (d : DOORS A) (prf : {A = unit} + {A = bool}) :=
match d with
| IsOpen d0 =>
match prf with
| left H => match (UIP Type A bool (test2 bool (IsOpen d0)) H) with
             | eq_refl => IsOpen d
            end
| right H => match UIP A d H with
             | eq_refl => Toggle d
             end
end
| Toggle d0 => match prf with
| left H => match UIP Type A unit (test2 A d) eq_refl with
             | eq_refl => IsOpen d
            end
| right H => match UIP A d H with
             | eq_refl => Toggle d
             end
end
end. *)



Definition f {A : Type} (x: DOORS A) : DOORS' :=
  match x with
    | IsOpen d => IsOpen' trm_tag_bool d
    | Toggle d => Toggle' trm_tag_unit d
  end.

Definition f'  (x: (DOORS bool) + (DOORS unit)) : DOORS' :=
  match x with
    | inl (IsOpen d) => IsOpen' trm_tag_bool d
    | inl (Toggle d) => IsOpen' trm_tag_bool d
    | inr (IsOpen d) => Toggle' trm_tag_unit d
    | inr (Toggle d) => Toggle' trm_tag_unit d
  end.

Definition g (x : DOORS') :=
  match x as y
  return 
  match y with
    | IsOpen' _ _ => DOORS bool
    | Toggle' _ _ => DOORS unit 
  end
  with
   | IsOpen' trm_tag_bool d => IsOpen d
   | Toggle' trm_tag_unit d => Toggle d 
  end.

Definition g' (x : DOORS') :=
  match x with
   | IsOpen' trm_tag_bool d => inl (IsOpen d)
   | Toggle' trm_tag_unit d => inr (Toggle d)
  end. 

Lemma fgid : forall (A: Type) (x : DOORS A), 
g (f x) = coerce (f x).
Proof. intros. destruct (f x). simpl. destruct t; reflexivity.
simpl. destruct t. reflexivity. Qed.

Axiom iso : forall A, exists (f : DOORS A -> (DOORS bool + DOORS unit))
(g : (DOORS bool + DOORS unit) -> DOORS A), 
(forall x, f (g x) = x) /\ (forall x, g (f x) = x).

Lemma g'f'id : forall (A : Type) (x : DOORS'),
f' (g' x) = x. Proof. intros. destruct x; destruct t; simpl in *; reflexivity. Qed.

From Coq Require Import Program.Equality.

Lemma unit_not_bool : @eq Type unit bool -> False. Admitted.

Lemma f'g'id : forall (A: Type) (x : (DOORS bool + DOORS unit)), 
g' (f' x) = x. Proof. intros;
simpl. destruct x. dependent destruction d. simpl. reflexivity.
pose proof (h := unit_not_bool).
assert False. apply h. apply x0. elim H.
simpl. dependent destruction d. 
pose proof (h := unit_not_bool).
assert False. apply h. symmetry. apply x0. elim H. 
 simpl. reflexivity. Qed.

Print All Dependencies f'g'id.




