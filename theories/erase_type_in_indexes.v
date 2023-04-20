Require Import MetaCoq.Template.All.
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

Definition gen_names_tys (nb_arity : nat) :=
  let fix aux nb_arity :=
  match nb_arity with
    | 0 => [mkNamed "t"%bs]
    | S n => mkNamed "Ty"%bs :: aux n
  end in List.rev (aux nb_arity).

Fixpoint get_n_constructors (n : nat) (i : inductive) := 
  match n with
   | 0 => []
   | S n' => tConstruct i n' [] :: get_n_constructors n' i
  end.

(* build a lambda binding variables of type Type with suitable names *)
Fixpoint mkLambda_ty (t : term) (n : nat) (n0 : nat)  :=
  match n with
    | 0 => t
    | S n' => let s := string_of_nat (n0-n) in
      tLambda (mkNamed (String.append "A" s)) (tSort fresh_universe) (mkLambda_ty t n' n0)
  end.

Fixpoint mkProd_ty (t : term) (n : nat) (n0 : nat)  :=
  match n with
    | 0 => t
    | S n' => let s := string_of_nat (n0-n') in
      tProd (mkNamed (String.append "A" s)) (tSort fresh_universe) (mkProd_ty t n' n0)
  end.

Definition create_hole (t : term) := hole.
   
Fixpoint build_branchs (lcnames : list (list aname)) (lc' : list term) (lpars : list term) :=
  match lcnames, lc' with
    | l :: ls, t :: ts  => {| bcontext := l ; bbody := tApp t 
      ((List.map (lift 1 (Datatypes.length l)) lpars)++(Rel_list (Datatypes.length l) 0)) |} :: 
      build_branchs ls ts lpars
    | _, _ => []
  end.

Definition build_match_traduction (kn kn' : kername) (lpars : list term) 
  (nb_arity : nat)
  (lcnames : list (list aname)) (* list of names for arguments of constructors of the initial type *)
  (lc' : list term) (* list of constructors of the transformed type *) :=
    tCase {| ci_ind := first_inductive kn ; ci_npar := Datatypes.length lpars;
      ci_relevance := Relevant |} 
          {| puinst := [] ; pparams := (List.map (lift (S (nb_arity)) 0) lpars) ; pcontext := gen_names_tys nb_arity;
      preturn := tApp (tInd (first_inductive kn') []) (List.map (lift (S (2*nb_arity)) 0) lpars) |}
          (tRel 0) (build_branchs lcnames lc' (List.map (lift (S nb_arity) 0) lpars)).


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

Definition build_traduction_term (kn kn' : kername) (lpars : list term) 
  (nb_arity : nat)
  (lcnames : list (list aname)) (* list of names for arguments of constructors of the initial type *)
  (lc' : list term) := 
  let n := Datatypes.length lpars in
  let nb_lambdas := nb_arity + n in
  let lindexes := Rel_list nb_arity 0 in
  mkLambda_ty (tLambda (mkNamed "x"%bs)
    (tApp (tInd {| inductive_mind := kn ; inductive_ind := 0 |} []) ((List.map (lift nb_arity 0) lpars)++lindexes)) 
        (build_match_traduction kn kn' lpars nb_arity lcnames lc')) nb_lambdas nb_lambdas.

Definition build_traduction_type (kn kn' : kername) (lpars : list term) 
  (nb_arity : nat) :=
  let lindexes := Rel_list nb_arity 0 in
  let npars := Datatypes.length lpars in
  let nbprods := npars + nb_arity in
  mkProd_ty (tProd mknAnon (tApp (tInd {| inductive_mind := kn ; inductive_ind := 0 |} []) 
    ((List.map (lift nb_arity 0) lpars)++lindexes))
    (tApp (tInd {| inductive_mind := kn' ; inductive_ind := 0 |} []) (List.map (lift nb_arity 0) lpars))) nbprods nbprods.
  

(** Step 4 : final transformation *)
 
Definition quote_inductive_and_kername (tm : term) :=
  match tm with
      | tInd ({| inductive_mind := kn ; inductive_ind := 0 |}) u =>
          decl <- tmQuoteInductive (inductive_mind  ({| inductive_mind := kn ; inductive_ind := 0 |})) ;;
          tmReturn (decl, kn)
      | _ => tmPrint tm ;; tmFail " is not an inductive"%bs
    end. 

Definition erase_type_in_indexes_aux (p : mutual_inductive_body * kername) :=
  match p with
    | (decl, kn) => 
        match find_nbr_arity decl with
          | None => 
              tmFail "wrong argument given to the transformation"%bs 
          | Some 0 => 
              tmFail "the transformation does nothing here: the type is not dependent or not handled"%bs
          | Some (S n) =>
                  fresh <- tmFreshName (String.append kn.2 "'"%bs) ;;
                  let indu_entry := mind_body_to_entry decl in 
                  let npars := decl.(ind_npars) in
                  let lcnames := names_for_args_constructor_first_oind indu_entry in
                  let nb_constructors := Datatypes.length lcnames in
                  let lpars := Rel_list npars 0 in
                  curmodpath <- tmCurrentModPath tt ;;
                  tmMkInductive true (create_mind_transformed indu_entry fresh);;
                  let lc' := List.rev (get_n_constructors nb_constructors ({| inductive_mind :=                 
                  (curmodpath, fresh) ; inductive_ind := 0 |})) in
                  res <- tmEval all (build_traduction_term kn (curmodpath, fresh) lpars (S n) lcnames lc') ;;
                  res2 <- tmEval all (build_traduction_type kn (curmodpath, fresh) lpars (S n)) ;;
                  tmReturn ((res, res2), (kn, (curmodpath, fresh)))
        end
end.

Definition pose_definitions (p : term*term) (id : ident) : TemplateMonad term :=
  res2 <- tmEval all p.2 ;; 
  ty_unq <- tmUnquoteTyped Type res2 ;;
  res <- tmEval all p.1 ;; 
  trm_unq <- tmUnquoteTyped ty_unq res ;;
  def <- tmDefinition id trm_unq ;; 
  def_quote <- tmQuote def ;; tmReturn def_quote.

Fixpoint erase_type_in_indexes (l : list term) : TemplateMonad (list term * (list (kername*kername))) :=
  match l with
    | [] => tmReturn ([], [])
    | x :: xs => 
      p0 <- quote_inductive_and_kername x ;;
      p <- erase_type_in_indexes_aux p0 ;;
      fresh <- tmFreshName "transfo"%bs ;;
      res <- pose_definitions p.1 fresh;;
      res' <- erase_type_in_indexes xs ;; 
      res0 <- tmEval all res'.1 ;; 
      res1 <- tmEval all res'.2 ;;
      tmReturn (res::res0, p.2 :: res1)
  end. 

(** Tests **)

Inductive door : Type := Left | Right.

Inductive DOORS : Type -> Type :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

MetaCoq Run (erase_type_in_indexes [<% DOORS %>]).  
Print transfo.

Inductive test : Type -> Type -> Type :=
| test1 : bool -> test (list nat) (bool).
 MetaCoq Run (erase_type_in_indexes [<% test %>]).
Print transfo0.

Inductive test_parameter (A B : Type) : Type -> Type :=
| c1 : bool -> door -> test_parameter A B unit.
MetaCoq Run (erase_type_in_indexes [<% test_parameter %>]). 

Print transfo1. 
Print test_parameter'.

Definition user_id := nat.

Inductive bank_operation : Type -> Type :=
| Withdraw : user_id -> nat -> nat -> bank_operation unit
| GetBalance : user_id -> bank_operation nat.

MetaCoq Run (erase_type_in_indexes [<% bank_operation %>]).
Print bank_operation'.
Print transfo2.

MetaCoq Quote Definition DOORS_reif := DOORS. 
MetaCoq Quote Definition DOORS'_reif := DOORS'.

Definition list_kn_test := 
  [ ((MPfile
         ["erase_type_in_indexes"%bs; "theories"%bs; "Sniper"%bs],
      "DOORS"%bs), (MPfile
         ["erase_type_in_indexes"%bs; "theories"%bs; "Sniper"%bs],
      "DOORS'"%bs)); ((MPfile
         ["erase_type_in_indexes"%bs; "theories"%bs; "Sniper"%bs],
      "bank_operation"%bs), (MPfile
         ["erase_type_in_indexes"%bs; "theories"%bs; "Sniper"%bs],
      "bank_operation'"%bs))].
