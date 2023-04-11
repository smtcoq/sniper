Require Import MetaCoq.Template.All.
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

where all the TyCijs are closed types

is transformed into an inductive 
I' (P1 : T1) ... (Pk : Tk) : Type :=
| C1' x11 ... x1m trm_tag_TyC11 ... trm_tagTyC1l : I' P1 ... Pk
...
| Cn' xn1 ... xnm trm_tag_TyCn1 ... trm_tagTyCnl : I' P1 ... Pk.

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

(* TODO : expliquer dans la thèse ceci : *)
(* program = global_env × term
     : Type *)

(* Record global_env : Type := mk_global_env
  { universes : ContextSet.t;
    declarations : global_declarations;
    retroknowledge : Environment.Retroknowledge.t }. *)

(* global_declarations = list (kername × global_decl)
     : Type *)

(* Inductive global_decl : Type :=
    ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.*)

(* Record mutual_inductive_body : Type
  := Build_mutual_inductive_body
  { ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body;
    ind_universes : universes_decl;
    ind_variance : option (list Variance.t) }. *)

(* ({|
   universes :=
     (LevelSetProp.of_list
        [Level.Level "Coq.Init.Datatypes.23"%bs;
        Level.Level "Coq.Init.Datatypes.22"%bs; Level.lzero],
     ConstraintSet.empty);
   declarations :=
     [(MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "prod"%bs,
      InductiveDecl
        {|
          ind_finite := Finite;
          ind_npars := 2;
          ind_params :=
            [{|
               decl_name :=
                 {|
                   binder_name := nNamed "B"%bs;
                   binder_relevance := Relevant
                 |};
               decl_body := None;
               decl_type :=
                 tSort
                   (Universe.of_levels
                      (inr
                         (Level.Level "Coq.Init.Datatypes.23"%bs)))
             |};
            {|
              decl_name :=
                {|
                  binder_name := nNamed "A"%bs;
                  binder_relevance := Relevant
                |};
              decl_body := None;
              decl_type :=
                tSort
                  (Universe.of_levels
                     (inr
                        (Level.Level "Coq.Init.Datatypes.22"%bs)))
            |}];
          ind_bodies :=
            [{|
               ind_name := "prod"%bs;
               ind_indices := [];
               ind_sort :=
                 Universe.from_kernel_repr
                   (Level.Level "Coq.Init.Datatypes.22"%bs,
                   false)
                   [(Level.Level "Coq.Init.Datatypes.23"%bs,
                    false)];
               ind_type :=
                 tProd
                   {|
                     binder_name := nNamed "A"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (Universe.of_levels
                         (inr
                            (Level.Level
                               "Coq.Init.Datatypes.22"%bs))))
                   (tProd
                      {|
                        binder_name := nNamed "B"%bs;
                        binder_relevance := Relevant
                      |}
                      (tSort
                         (Universe.of_levels
                            (inr
                               (Level.Level
                                  "Coq.Init.Datatypes.23"%bs))))
                      (tSort
                         (Universe.from_kernel_repr
                            (Level.Level
                               "Coq.Init.Datatypes.22"%bs,
                            false)
                            [(Level.Level
                                "Coq.Init.Datatypes.23"%bs,
                             false)])));
               ind_kelim := IntoAny;
               ind_ctors :=
                 [{|
                    cstr_name := "pair"%bs;
                    cstr_args :=
                      [{|
                         decl_name :=
                           {|
                             binder_name := nAnon;
                             binder_relevance := Relevant
                           |};
                         decl_body := None;
                         decl_type := tRel 1
                       |};
                      {|
                        decl_name :=
                          {|
                            binder_name := nAnon;
                            binder_relevance := Relevant
                          |};
                        decl_body := None;
                        decl_type := tRel 1
                      |}];
                    cstr_indices := [];
                    cstr_type :=
                      tProd
                        {|
                          binder_name := nNamed "A"%bs;
                          binder_relevance := Relevant
                        |}
                        (tSort
                           (Universe.of_levels
                              (inr
                                 (Level.Level
                                    "Coq.Init.Datatypes.22"%bs))))
                        (tProd
                           {|
                             binder_name := nNamed "B"%bs;
                             binder_relevance := Relevant
                           |}
                           (tSort
                              (Universe.of_levels
                                 (inr
                                    (Level.Level
                                       "Coq.Init.Datatypes.23"%bs))))
                           (tProd
                              {|
                                binder_name := nAnon;
                                binder_relevance := Relevant
                              |} (tRel 1)
                              (tProd
                                 {|
                                   binder_name := nAnon;
                                   binder_relevance := Relevant
                                 |} (tRel 1)
                                 (tApp (tRel 4) [tRel 3; tRel 2]))));
                    cstr_arity := 2
                  |}];
               ind_projs := [];
               ind_relevance := Relevant
             |}];
          ind_universes := Monomorphic_ctx;
          ind_variance := None
        |})]%list;
   retroknowledge :=
     {|
       Environment.Retroknowledge.retro_int63 :=
         Some
           (MPfile
              ["PrimInt63"%bs; "Int63"%bs; "Cyclic"%bs;
              "Numbers"%bs; "Coq"%bs]%list, "int"%bs);
       Environment.Retroknowledge.retro_float64 :=
         Some
           (MPfile ["PrimFloat"%bs; "Floats"%bs; "Coq"%bs]%list,
           "float"%bs)
     |}
 |},
tInd
  {|
    inductive_mind :=
      (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs]%list,
      "prod"%bs);
    inductive_ind := 0
  |} []%list) *)

(* 

Record mutual_inductive_entry : Type
  := Build_mutual_inductive_entry
  { mind_entry_record : option (option ident);
    mind_entry_finite : recursivity_kind;
    mind_entry_params : context;
    mind_entry_inds : list one_inductive_entry;
    mind_entry_universes : universes_entry;
    mind_entry_template : bool;
    mind_entry_variance : option (list (option Variance.t));
    mind_entry_private : option bool }. *)

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

Definition find_nbr_arity (p : program) : option nat :=
  let opt := info_inductive p.1 p.2 in
  match opt with 
    | None => None
    | Some mind => let (x, y) := (mind.(ind_npars), (List.hd default_body mind.(ind_bodies)))
                    in 
                   let Ty_ind := y.(ind_type) in
                   nb_args_codomain_type_or_set (skipn_prods x Ty_ind)
  end.

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

Definition index_args_in_codomain_of_constructors (p: program) :=
  let (npars, ty_cstr) := info_nonmutual_inductive p.1 p.2 in 
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

Fixpoint make_universes_list (npars: nat) :=
  match npars with
    | 0 => []
    | S n' => let s := string_of_nat n' in (Level.Level (String.append ("Deptypes.")%bs s)) :: 
              make_universes_list n'
  end. Print Universe.make. 

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

(* Creates all the tags for the types which are not in l_base.
It returns the list of lists of tags needed, for each constructor *)

Fixpoint create_tags (l_base : list term) : TemplateMonad (term*term) :

(** Isomorphisms tests **)

Inductive door : Type := Left | Right.

Inductive DOORS : Type -> Type :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

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




