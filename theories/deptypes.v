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

For each closed type, one is created, and we provide already 
created typ_tag for frequent types such as nat, bool or unit *)

Inductive typ_tag_nat := trm_tag_nat.

Inductive typ_tag_unit := trm_tag_unit.

Inductive typ_tag_bool := trm_tag_bool.


Definition base_mapping_tags_terms 
  : list (term*term):= 
  [(<%nat%>, <%typ_tag_nat%>); 
  (<%bool%>, <%typ_tag_bool%>);
  (<%unit%>, <%typ_tag_unit%>)].

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

Definition create_tag_oind id : one_inductive_entry :=
  {| 
    mind_entry_typename := (String.append ("typ_tag_") id);
    mind_entry_arity := <%Set%> ;
    mind_entry_consnames := [(String.append ("trm_tag_") id)];
    mind_entry_lc := [tRel 0];
   |}.

(* Creates an inductive tag (as a mutual_inductive_entry) *)
Definition create_tag_mind (id : ident) : mutual_inductive_entry :=
  {| 
    mind_entry_record := None;
    mind_entry_finite := Finite; (* not corecursive *)
    mind_entry_params := [];
    mind_entry_inds := [create_tag_oind id];
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

Definition create_tag_and_return (id : ident) :
TemplateMonad term :=
fsh <- tmFreshName id ;; 
let mind := create_tag_mind id in
tmMkInductive true mind ;;
curmodpath <- tmCurrentModPath tt ;;
let name_indu := (curmodpath, String.append "typ_tag_"%bs fsh) in
tmReturn (tInd {| inductive_mind := name_indu ; inductive_ind := 0 |} []).

(* Creates all the tags for the types which are not in l_base.
It returns the list of lists of tags needed *)

Fixpoint create_tags (inputs : list term) (l_base : list (term*term)) : 
TemplateMonad (list (term*term)) :=
  match inputs with 
    | [] => tmReturn []
    | x :: xs => 
      let (x', y') := dest_app x in
      match x' with
        | tInd {| inductive_mind := kn ; inductive_ind := ind |} u => 
          match find_kername kn l_base with
            | None =>
              mind <- tmQuoteInductive kn  ;;
              y <- create_tag_and_return kn.2 ;; tmPrint y ;;
              l <- create_tags xs l_base ;;
              match y' with
                | [] => tmReturn ((tInd {| inductive_mind := kn ; inductive_ind := ind |} u, y) :: l)
                | _ :: _ =>
                  tmReturn ((tApp (tInd {| inductive_mind := kn ; inductive_ind := ind |} u) y', y) :: l)
              end
            | Some y => 
              l <- create_tags xs l_base ;; tmReturn (y :: l)
          end
        | _ => 
          let npars := count_prenex_foralls x in
          y <- create_tag_and_return "Typ"%bs ;;
          l <- create_tags xs l_base ;; tmReturn ((x, y) :: l)      
        end
  end.

(** Step 4 : add arguments to constructor's types *)

Fixpoint keep_firstn_args (t : term) (npars : nat) :=
  match t with
    | tProd Na Ty u => tProd Na Ty (keep_firstn_args u npars) 
    | tApp u l => tApp u (List.firstn npars l)
    | _ => t
  end.

Fixpoint add_nondep_args (t : term) (npars : nat) (l : list term) : term :=
  match l with
   | [] => keep_firstn_args t npars
   | x :: xs => tProd (mkNamed "tag"%bs) x (lift 1 0 (add_nondep_args t npars xs))
  end.

Fixpoint add_nondep_args_list (l1 : list term) npars (l2 : list (list term)) :=
  match l1, l2 with
    | [], [] => []
    | x :: xs, y :: ys => add_nondep_args x npars y :: add_nondep_args_list xs npars ys
    | _, _ => []
  end.

Definition create_oind_transformed oind npars ltags : one_inductive_entry :=
  {| 
    mind_entry_typename := (String.append oind.(mind_entry_typename) "'");
    mind_entry_arity := <% Type %> ;
    mind_entry_consnames := List.map (fun x => String.append x "'") oind.(mind_entry_consnames);
    mind_entry_lc := add_nondep_args_list oind.(mind_entry_lc) npars ltags ;
   |}.

Definition create_mind_transformed mind ltags : mutual_inductive_entry :=
  let npars := List.length mind.(mind_entry_params) in
  {| 
    mind_entry_record := mind.(mind_entry_record);
    mind_entry_finite := mind.(mind_entry_finite);
    mind_entry_params := mind.(mind_entry_params);
    mind_entry_inds := List.map (fun x => create_oind_transformed x npars ltags) 
      mind.(mind_entry_inds);
    mind_entry_universes := mind.(mind_entry_universes); 
    mind_entry_template := mind.(mind_entry_template); 
    mind_entry_variance := mind.(mind_entry_variance);
    mind_entry_private := mind.(mind_entry_private);
  |}. 

(** Step 5 : final transformation *)
 

Fixpoint ty_to_tag s (t : term) (l : list (term*term)) :=
  match l with
    | (x, y) :: xs => 
      if eqb_term (trans s t) (trans s x) then y
      else ty_to_tag s t xs
    | [] => tVar "error: the tag has not been found"%bs
  end.

Definition ty_to_tag_list_of_list s (l1 : list (list term)) (l2 : list (term*term)) :=
  List.map (fun l => List.rev (List.map (fun x => ty_to_tag s x l2) l)) l1. 

Definition elim_type_in_indexes (tm : term) :=
(* IMPROVE : trick to use eqb_term, we need a global_env, so we use a dumb global 
env *)
  unit_rec <- tmQuoteRec unit ;;
  let s := (trans_global_env unit_rec.1) in
  match tm with
    | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
      match find_nbr_arity decl with
        | None => 
            tmFail "wrong argument given to the transformation"%bs 
        | Some 0 => 
            tmPrint "the transformation does nothing here: the type is not dependent or not handled"%bs
        | Some (S n) => 
                let indu_entry := mind_body_to_entry decl in
                let l := index_args_in_codomain_of_constructors decl in
                let lflat := flat_map id l in
                tags_avail <- create_tags lflat base_mapping_tags_terms ;;
                let args_new_constructors := ty_to_tag_list_of_list s l tags_avail in
                tmMkInductive true (create_mind_transformed indu_entry args_new_constructors)
        end
    | _ => tmPrint tm ;; tmFail " is not an inductive"%bs
end.


(** Tests **)

Inductive door : Type := Left | Right.

Inductive DOORS : Type -> Type :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

MetaCoq Run (elim_type_in_indexes <% DOORS %>). 
Print DOORS'.

Inductive test : Type -> Type -> Type :=
| test1 : bool -> test (list nat) (bool).
 MetaCoq Run (elim_type_in_indexes <% test %>).
Print test'.

Inductive test_parameter (A B : Type) : Type -> Type :=
| c1 : bool -> door -> test_parameter A B unit.
MetaCoq Run (elim_type_in_indexes <% test_parameter %>). 
Print test_parameter'.


(* Generation of the transformation function *)

(* Tests but struggling *)
Definition coerce (d : DOORS') :=
  match d as y return
  match y with
    | IsOpen' _ _ => DOORS bool
    | Toggle' _ _ => DOORS unit
  end
  with
   | IsOpen' _ d => IsOpen d
   | Toggle' _ d => Toggle d 
  end.

Definition coerce2 (A : Type) (d : DOORS A) : DOORS bool + DOORS unit :=
match d with
   | IsOpen d => inl (IsOpen d)
   | Toggle d => inr (Toggle d) 
  end.

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




