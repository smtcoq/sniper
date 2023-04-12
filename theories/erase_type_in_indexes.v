Require Import MetaCoq.Template.All.
From MetaCoq.PCUIC Require Import PCUICReflect.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Import MCMonadNotation.
Require Import utilities.
Require Import List.
Require Import String.
Import ListNotations.
Unset MetaCoq Strict Unquote Universe Mode.

(** Description of the transformation erase_type_in_indexes

A non-mutual inductive

I (P1 : T1) ... (Pk : Tk) : Type -> ... -> Type := (with l types)
| C1 x11 ... x1m : I P1 ... Pk TyC11 ... TyC1l
...
| Cn xn1 ... xnm : I P1 ... Pk TyCn1 ... TyCnl.

where all the TyCijs are closed types

is transformed into an inductive 
I' (P1 : T1) ... (Pk : Tk) : Type :=
| C1' x11 ... x1m : I' P1 ... Pk
...
| Cn' xn1 ... xnm : I' P1 ... Pk.

We simply erase the type information *)


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

(** Step 2: look at the codomain of constructors and remove from npars to npars + nbarity 
arguments of return type *)

Fixpoint keep_firstn_args (t : term) (npars : nat) :=
  match t with
    | tProd Na Ty u => tProd Na Ty (keep_firstn_args u npars) 
    | tApp u l => tApp u (List.firstn npars l)
    | _ => t
  end.

Definition create_oind_transformed oind npars id : one_inductive_entry :=
  {| 
    mind_entry_typename := id;
    mind_entry_arity := <% Type %> ;
    mind_entry_consnames := List.map (fun x => String.append x "'") oind.(mind_entry_consnames);
    mind_entry_lc := List.map (fun x => keep_firstn_args x npars) oind.(mind_entry_lc) ;
   |}.

Definition create_mind_transformed mind id : mutual_inductive_entry :=
  let npars := List.length mind.(mind_entry_params) in
  {| 
    mind_entry_record := mind.(mind_entry_record);
    mind_entry_finite := mind.(mind_entry_finite);
    mind_entry_params := mind.(mind_entry_params);
    mind_entry_inds := List.map (fun x => create_oind_transformed x npars id) 
      mind.(mind_entry_inds);
    mind_entry_universes := mind.(mind_entry_universes); 
    mind_entry_template := mind.(mind_entry_template); 
    mind_entry_variance := mind.(mind_entry_variance);
    mind_entry_private := mind.(mind_entry_private);
  |}. 


(* Step 3 : building the Coq function from the initial type to the result type *)

Definition get_name_constructors_first_oind mind :=
  match hd_error (mind_entry_inds mind) with
    | None => tmFail "cannot get any inductives in this mutual inductive entry"%bs
    | Some y => tmReturn (mind_entry_consnames y)
  end.

Definition first_inductive (kn : kername) :=
{| inductive_mind := kn ; inductive_ind := 0 |}.

Fixpoint gen_names_tys (nb_arity : nat) :=
  match nb_arity with
    | 0 => [mkNamed "t"%bs]
    | S n => mkNamed "Ty"%bs :: gen_names_tys n
  end.

Fixpoint build_branchs (lcnames : list (list aname)) (lc' : list term) (lpars : list term) :=
  match lcnames, lc' with
    | l :: ls, t :: ts  => {| bcontext := l ; bbody := tApp t (List.map (lift (Datatypes.length l) 0) lpars) |} :: 
      build_branchs ls ts lpars 
    | _, _ => []
  end.

Fixpoint get_n_constructors (n : nat) (i : inductive) := 
  match n with
   | 0 => []
   | S n' => tConstruct i n' [] :: get_n_constructors n' i
  end.

(* build a lambda binding variables of type Type with suitable names *)
Fixpoint mkLambda_ty (t : term) (n : nat) (n0 : nat)  :=
  match n with
    | 0 => t
    | S n' => let s := string_of_nat (n'-n) in
      tLambda (mkNamed (String.append "A" s)) (tSort fresh_universe) (mkLambda_ty t n' n0)
  end.
   

Definition build_match_traduction (kn kn' : kername) (lpars : list term) 
  (nb_arity : nat)
  (lcnames : list (list aname)) (* list of names for arguments of constructors of the initial type *)
  (lc' : list term) (* list of constructors of the transformed type *) :=
    tCase {| ci_ind := first_inductive kn ; ci_npar := Datatypes.length lpars;
      ci_relevance := Relevant |} 
          {| puinst := [] ; pparams := lpars ; pcontext := gen_names_tys nb_arity;
      preturn := tApp (tInd (first_inductive kn') []) lpars |}
          (tRel 0) (build_branchs lcnames lc' lpars).


Fixpoint names_of_prods (t : term) :=
  match t with
    | tProd Na _ u => Na :: names_of_prods u
    | _ => []
  end.

Definition names_for_args_constructor_first_oind mind :=
  match hd_error (mind_entry_inds mind) with
    | None => []
    | Some y => List.map (fun x => names_of_prods x) (mind_entry_lc y)
  end. 

Definition build_traduction (kn kn' : kername) (lpars : list term) 
  (nb_arity : nat)
  (lcnames : list (list aname)) (* list of names for arguments of constructors of the initial type *)
  (lc' : list term) := 
  let n := Datatypes.length lpars in
  mkLambda_ty (tLambda (mkNamed "x"%bs) 
    (tApp (tInd {| inductive_mind := kn ; inductive_ind := 0 |} []) lpars) 
        (build_match_traduction kn kn' lpars nb_arity lcnames lc')) n n.

(** Step 4 : final transformation *) Print tmMkInductive. 

Definition get_curmodpath := curmodpath <- tmCurrentModPath tt ;; tmReturn curmodpath.

Definition erase_type_in_indexes (tm : term) curmodpath :=
  match tm with
    | tInd ({| inductive_mind := kn ; inductive_ind := 0 |}) u =>
        decl <- tmQuoteInductive (inductive_mind  ({| inductive_mind := kn ; inductive_ind := 0 |})) ;;
        fresh <- tmFreshName (String.append kn.2 "'"%bs) ;;
      match find_nbr_arity decl with
        | None => 
            tmFail "wrong argument given to the transformation"%bs 
        | Some 0 => 
            tmPrint "the transformation does nothing here: the type is not dependent or not handled"%bs
        | Some (S n) =>
                let indu_entry := mind_body_to_entry decl in 
                let npars := List.length indu_entry.(mind_entry_params) in
                let lcnames := names_for_args_constructor_first_oind indu_entry in
                let nb_constructors := Datatypes.length lcnames in
                let lpars := Rel_list npars 0 in
                tmMkInductive true (create_mind_transformed indu_entry fresh);;
                let lc' := get_n_constructors nb_constructors ({| inductive_mind :=                 
                (curmodpath, fresh) ; inductive_ind := 0 |}) in
               tmReturn (build_traduction kn (curmodpath, (String.append kn.2 "'"%bs)) lpars
              (S n) lcnames lc')
        end
    | _ => tmPrint tm ;; tmFail " is not an inductive"%bs
end.


(** Tests **)

Inductive door : Type := Left | Right.

Inductive DOORS : Type -> Type :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

MetaCoq Run (erase_type_in_indexes <% DOORS %>). 
Print DOORS'.

Inductive test : Type -> Type -> Type :=
| test1 : bool -> test (list nat) (bool).
 MetaCoq Run (erase_type_in_indexes <% test %>).
Print test'.

Inductive test_parameter (A B : Type) : Type -> Type :=
| c1 : bool -> door -> test_parameter A B unit.
MetaCoq Run (erase_type_in_indexes <% test_parameter %>). 
Print test_parameter'.

Check (nat + (bool + unit))%type.
Check ((nat + bool) + unit)%type.

(* Step 3: Generation of the transformation function *)

(* Definition transfo1 {A : Type} (d : DOORS A) : DOORS' :=
    match d with
      | IsOpen d => IsOpen' d
      | Toggle d => Toggle' d
    end.

MetaCoq Quote Recursively Definition transfo1_reif_rec := transfo1.

Print transfo1_reif_rec.

Definition transfo2 {A B : Type} (t : test A B) :=
  match t with
    | test1 b => test1' b
  end.
MetaCoq Quote Recursively Definition transfo2_reif_rec := transfo2.

Print transfo2_reif_rec.

Definition transfo3 (A B : Type) (C : Type) (t : test_parameter A B C) :=
  match t with
    | c1 b d => c1' A B b d
  end.
MetaCoq Quote Recursively Definition transfo3_reif_rec := transfo3.
 *)


      
           





