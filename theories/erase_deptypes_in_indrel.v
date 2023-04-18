Require Import utilities.
Require Import List.
Import ListNotations.
Require Import MetaCoq.Template.All.
Require Import erase_type_in_indexes.


(** Description of the transformation erase_deptype_in_inrel :

Notation : ?Ak means that this type could be present or not.

A non-mutual inductive relation

R (P1 : T1) ... (Pk : Tk) : X1 -> ... Xp -> (A11 : Type) -> ... -> (Aml : Type) -> 
I1 A11 ... Al1 -> ... -> Im Am1 ... Aml -> ?A11 -> ... -> ?Al1 ->
?A1m -> ... -> ?Aml -> Prop := 

C1 : forall (x1 : T1) ... (xj : Tj) (H ... : Prop) : R P1 ... Pk X1 ... Xp 
    TYC11 ... TYCml 

where all the Ij could be transformed by the transformation 
erase_type_in_indexes and all the Aiks are different non 
isomorphic types for each i fixed.
The Xis are not sorts.

will be transformed into

R' (P1 : T1) ... (Pk : Tk) : X1 -> ... Xp -> I1' -> ... Im' -> ?{TYC111  + ... + TYC1m1} 
-> ... -> ?{?TYCjl1 + ... + TYCjml} :=
| C1' : forall (x1 : T1) ... (xj : Tj) (H ... : Prop) : R' P1 Pk X1 ... Xp (inl ( inl ( ... )))
 
*)

(* Examples *)

Inductive doors_o_callee : (bool*bool) -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| doors_o_callee_is_open (d : door) (ω : bool*bool) (x : bool) (equ : true = x)
  : doors_o_callee ω bool (IsOpen d) x

(** - There is no particular doors_o_calleeises on the result [x] of a request for [ω] to
      close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : bool*bool) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

MetaCoq Quote Recursively Definition doc_rec := doors_o_callee.

Record env := mk_env 
  { env_parameters : list (aname*term*nat); (* the name of a parameter, its type and its db index *)
    env_arguments : list (aname*term*nat); (* idem for the arguments of the inductive *)
    env_types : list (aname*term*nat); (* idem for its args of type Type *)
    env_inductives : list (aname*term*nat); (* idem for the inductives arguments *)
    env_elements : list (aname*term*nat); (* idem for the args of the args of type Type *)
    domain : term
 }. 

Definition lift10_term_and_db (p : aname*term*nat) :=
  let x := p.1.1 in 
  let y := p.1.2 in
  let z := p.2 in
  (x, lift 1 0 y, S z).

(* we get the parameters, from the first to the last *)
Definition get_parameters (mind : mutual_inductive_entry) :=
  let params := mind_entry_params mind in
  let fix aux l n := 
  match l with
   | x :: xs => (decl_name x, decl_type x, n) :: aux xs (S n)
   | [] => []
  end in aux params 0.

Definition get_first_oind_from_mind (mind : mutual_inductive_entry) :=
  let oind := mind_entry_inds mind in 
  hd_error oind. 

(* Here, each function takes at arguments the partially builded record env, 
this explains the use of product types *) 

Fixpoint get_args (t : term) l :=
  match t with
  | tProd Na (tSort s) u => if negb (Universe.is_prop s) then (t, [], l) else let p := get_args u l in
      (p.1.1, (Na, (tSort s), 0) :: List.map lift10_term_and_db p.1.2, List.map lift10_term_and_db p.2)
  | tProd Na Ty u => let p := get_args u l in
      (p.1.1, (Na, lift 1 0 Ty, 0) :: List.map lift10_term_and_db p.1.2, List.map lift10_term_and_db p.2)
  | _ => (t, [], l)
  end.

Fixpoint get_types (t : term) (p : (list (aname*term*nat))*(list (aname*term*nat))) :=
 match t with
  | tProd Na (tSort s) u => let p0 := get_types u (p.1, p.2) in
      (p0.1.1.1, (Na, lift 1 0 (tSort s), 0) :: List.map lift10_term_and_db p0.1.1.2, 
       List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
  | tProd Na _ u => (t, [], p.1, p.2)
  | _ => (t, [], p.1, p.2)
  end.

Fixpoint get_indus (t: term) (p : (list (aname*term*nat))*(list (aname*term*nat))*(list (aname*term*nat))) := 
 match t with
  | tProd Na (tInd ind inst) u => let p0 := get_indus u (p.1.1, p.1.2, p.2) in
      (p0.1.1.1.1, (Na, lift 1 0 (tInd ind inst), 0) :: List.map lift10_term_and_db p0.1.1.1.2, 
       List.map lift10_term_and_db p0.1.1.2, List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
  | tProd Na (tApp (tInd ind inst) l) u  => let p0 := get_indus u (p.1.1, p.1.2, p.2) in
      (p0.1.1.1.1, (Na, lift 1 0 (tApp (tInd ind inst) l), 0) :: List.map lift10_term_and_db p0.1.1.1.2, 
       List.map lift10_term_and_db p0.1.1.2, List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
  | tProd Na _ u => (t, [], p.1.1, p.1.2, p.2)
  | _ => (t, [], p.1.1, p.1.2, p.2)
  end.

Fixpoint get_elems (t : term) (p : (list (aname*term*nat))*(list (aname*term*nat))*
                  (list (aname*term*nat))*(list (aname*term*nat))) :=
  match t with
    | tProd Na Ty u => let p0 := get_elems u (p.1.1.1, p.1.1.2, p.1.2, p.2) in
        (p0.1.1.1.1.1, (Na, lift 1 0 Ty, 0) :: List.map lift10_term_and_db p0.1.1.1.1.2, List.map lift10_term_and_db p0.1.1.1.2, 
        List.map lift10_term_and_db p0.1.1.2, List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
    | _ => (t, [], p.1.1.1, p.1.1.2, p.1.2, p.2)
  end. 


Definition get_env_default (e : env) (mind : mutual_inductive_entry) : env :=
  let env_pars := get_parameters mind in
  let opt := get_first_oind_from_mind mind in
  match opt with
    | None => e
    | Some x => let arity := mind_entry_arity x in
                let p := get_args arity env_pars in
                let p1 := get_types p.1.1 (p.1.2, p.2) in
                let p2 := get_indus p1.1.1.1 (p1.1.1.2, p1.1.2, p1.2) in
                let p3 := get_elems p2.1.1.1.1 (p2.1.1.1.2, p2.1.1.2, p2.1.2, p2.2) in
                {| 
                   env_parameters := p3.2;
                   env_arguments := p3.1.2 ;
                   env_types := p3.1.1.2 ;
                   env_inductives := p3.1.1.1.2;
                   env_elements := p3.1.1.1.1.2;
                   domain := p3.1.1.1.1.1;
                |}
end.

Definition get_env mind := 
  get_env_default 
                {| 
                   env_parameters := [] ;
                   env_arguments := [] ;
                   env_types := [] ;
                   env_inductives := [] ;
                   env_elements := [] ;
                   domain := default_reif ;
                |} mind.

Compute get_env ({|
         mind_entry_record := None;
         mind_entry_finite := Finite;
         mind_entry_params := [];
         mind_entry_inds :=
           [{|
              mind_entry_typename :=
                "doors_o_callee"%bs;
              mind_entry_arity :=
                tProd
                  {|
                    binder_name := nAnon;
                    binder_relevance :=
                      Relevant
                  |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                            "prod"%bs);
                          inductive_ind := 0
                        |} [])
                     [tInd
                        {|
                          inductive_mind :=
                            (MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                            "bool"%bs);
                          inductive_ind := 0
                        |} [];
                     tInd
                       {|
                         inductive_mind :=
                           (MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                           "bool"%bs);
                         inductive_ind := 0
                       |} []])
                  (tProd
                     {|
                       binder_name :=
                         nNamed "a"%bs;
                       binder_relevance :=
                         Relevant
                     |}
                     (tSort
                        (Universe.lType
                           {|
                             t_set :=
                              {|
                              LevelExprSet.this :=
                              [(
                              Level.Level
                              "Sniper.theories.erase_deptypes_in_indrel.15"%bs,
                              0)];
                              LevelExprSet.is_ok :=
                              LevelExprSet.Raw.singleton_ok
                              (
                              Level.Level
                              "Sniper.theories.erase_deptypes_in_indrel.15"%bs,
                              0)
                              |};
                             t_ne := eq_refl
                           |}))
                     (tProd
                        {|
                          binder_name := nAnon;
                          binder_relevance :=
                            Relevant
                        |}
                        (tApp
                           (tInd
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["erase_type_in_indexes"%bs;
                              "theories"%bs;
                              "Sniper"%bs],
                              "DOORS"%bs);
                              inductive_ind :=
                              0
                              |} []) [
                           tRel 0])
                        (tProd
                           {|
                             binder_name :=
                              nAnon;
                             binder_relevance :=
                              Relevant
                           |} (tRel 1)
                           (tSort
                              Universe.lProp))));
              mind_entry_consnames :=
                ["doors_o_callee_is_open"%bs;
                "doors_o_callee_toggle"%bs];
              mind_entry_lc :=
                [tProd
                   {|
                     binder_name :=
                       nNamed "d"%bs;
                     binder_relevance :=
                       Relevant
                   |}
                   (tInd
                      {|
                        inductive_mind :=
                          (MPfile
                             ["erase_type_in_indexes"%bs;
                             "theories"%bs;
                             "Sniper"%bs],
                          "door"%bs);
                        inductive_ind := 0
                      |} [])
                   (tProd
                      {|
                        binder_name :=
                          nNamed "ω"%bs;
                        binder_relevance :=
                          Relevant
                      |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "prod"%bs);
                              inductive_ind :=
                              0
                            |} [])
                         [tInd
                            {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                              inductive_ind :=
                              0
                            |} [];
                         tInd
                           {|
                             inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                             inductive_ind :=
                              0
                           |} []])
                      (tProd
                         {|
                           binder_name :=
                             nNamed "x"%bs;
                           binder_relevance :=
                             Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                              inductive_ind :=
                              0
                            |} [])
                         (tProd
                            {|
                              binder_name :=
                              nNamed "equ"%bs;
                              binder_relevance :=
                              Relevant
                            |}
                            (tApp
                              (tInd
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Logic"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "eq"%bs);
                              inductive_ind :=
                              0
                              |} [])
                              [
                              tInd
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                              inductive_ind :=
                              0
                              |} [];
                              tConstruct
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                              inductive_ind :=
                              0
                              |} 0 []; 
                              tRel 0])
                            (tApp 
                              (tRel 4)
                              [
                              tRel 2;
                              tInd
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                              inductive_ind :=
                              0
                              |} [];
                              tApp
                              (tConstruct
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["erase_type_in_indexes"%bs;
                              "theories"%bs;
                              "Sniper"%bs],
                              "DOORS"%bs);
                              inductive_ind :=
                              0
                              |} 0 [])
                              [tRel 3];
                              tRel 1]))));
                tProd
                  {|
                    binder_name :=
                      nNamed "d"%bs;
                    binder_relevance :=
                      Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile
                            ["erase_type_in_indexes"%bs;
                            "theories"%bs;
                            "Sniper"%bs],
                         "door"%bs);
                       inductive_ind := 0
                     |} [])
                  (tProd
                     {|
                       binder_name :=
                         nNamed "ω"%bs;
                       binder_relevance :=
                         Relevant
                     |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "prod"%bs);
                             inductive_ind :=
                              0
                           |} [])
                        [tInd
                           {|
                             inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                             inductive_ind :=
                              0
                           |} [];
                        tInd
                          {|
                            inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "bool"%bs);
                            inductive_ind := 0
                          |} []])
                     (tProd
                        {|
                          binder_name :=
                            nNamed "x"%bs;
                          binder_relevance :=
                            Relevant
                        |}
                        (tInd
                           {|
                             inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "unit"%bs);
                             inductive_ind :=
                              0
                           |} [])
                        (tApp (tRel 3)
                           [tRel 1;
                           tInd
                             {|
                              inductive_mind :=
                              (
                              MPfile
                              ["Datatypes"%bs;
                              "Init"%bs;
                              "Coq"%bs],
                              "unit"%bs);
                              inductive_ind :=
                              0
                             |} [];
                           tApp
                             (tConstruct
                              {|
                              inductive_mind :=
                              (
                              MPfile
                              ["erase_type_in_indexes"%bs;
                              "theories"%bs;
                              "Sniper"%bs],
                              "DOORS"%bs);
                              inductive_ind :=
                              0
                              |} 1 [])
                             [tRel 2]; 
                           tRel 0])))]
            |}];
         mind_entry_universes :=
           Monomorphic_entry
             ({|
                VSet.this := LevelSet.Raw.Leaf;
                VSet.is_ok :=
                  LevelSet.Raw.empty_ok
              |},
             {|
               CS.this :=
                 ConstraintSet.Raw.Leaf;
               CS.is_ok :=
                 ConstraintSet.Raw.empty_ok
             |});
         mind_entry_template := false;
         mind_entry_variance := None;
         mind_entry_private := None
       |}).

MetaCoq Quote Definition sum_reif := @sum. 

Require Import Coq.micromega.Lia.

Program Fixpoint mkSum_proved (l : list term) {measure (length l) } :=
  match l with
    | [] => default_reif
    | [x] => x
    | [x; y] => tApp sum_reif [x; y] 
    |  x :: y :: xs => let t := tApp sum_reif [x ; y] in
        mkSum_proved (t :: xs)
    end.
Next Obligation.
unfold Wf.MR. apply Acc_intro. intro y. induction y.
- intro H. simpl in H. apply Acc_intro. intro y'.
intros H1. inversion H1.
- simpl. intro H1. apply Acc_intro. intro y0.
assert (H0 : #|y0| < #|a0 :: y| -> (#|y0| = #|y| \/ #|y0| < #| y|)).
intro H. induction y. destruct y0. lia. simpl in H. lia.
simpl in *. lia. intro H. apply H0 in H. destruct H as [ H | H']. 
 + constructor.
rewrite H. intros y1 H2. apply Inverse_Image.Acc_inverse_image.
eapply Wf_nat.acc_lt_rel with (F := lt). intros.
unfold Wf_nat.inv_lt_rel. exists (S x). lia. lia.
exists (S #|y1|). lia.
 + apply IHy. lia. lia. Qed.

Unset Guard Checking.

Fixpoint mkSum (l : list term)  :=
  match l with
    | [] => default_reif
    | [x] => x
    | [x; y] => tApp sum_reif [x; y] 
    |  x :: y :: xs => let t := tApp sum_reif [x ; y] in
        mkSum (t :: xs)
    end.

Set Guard Checking.

MetaCoq Unquote Definition test := 
(mkSum [<%nat%> ; <%bool%>; <%unit%>; <% nat -> nat %> ]).

(* We look at the domain of each constructor: it is the 
inductive relation R applied to its parameters, 
its arguments, the CONCRETE types TyC1 ..., given at the 
transformed inductives as indexes, and the arguments of this types.
These TyCis should be collected to form a sum type *)

(* nb_args : the number of arguments of the relation R (of type Type excluded) *)
(* nb_tys : the number of arguments of type Type of R *)
(* They are computed thanks to the env record *)
Fixpoint collect_tys_term t nb_args nb_tys :=
  match t with
    | tProd Na Ty u => collect_tys_term u nb_args nb_tys
    | tApp (tRel n) l => List.firstn nb_tys (List.skipn nb_args l)
    | _ => []
  end. 

Definition collect_tys_list 
(l : list term) nb_args nb_tys : list (list term) :=
List.map (fun x => collect_tys_term x nb_args nb_tys) l. 

(* return each list of arguments used by 
an inductive *)
Definition inductive_list_args 
(npars : nat)
(e : env) :=
  let indu := env_inductives e in
  let fix aux npars l :=
    match l with
      | [] => []
      | (_, tApp (tInd ind u) l, _) :: xs => 
        (List.skipn npars l) :: aux npars xs
      | _ :: xs => aux npars xs
    end
  in aux npars indu. 

Definition flat_inductive_list_args npars e := 
  tr_flatten (inductive_list_args npars e).

Fixpoint find_trel 
  (n : nat) (l : list (aname*term*nat)) :=
    match l with
  | (_, tRel k, _) :: l' => if Nat.eqb n k then true else find_trel n l'
  | _ :: l' => find_trel n l' 
  | [] => false
  end.

Definition args_used_aux e tys :=
  let args := env_arguments e in
  let fix aux args tys :=
    match tys with
      | tRel k :: tys' => find_trel k args :: aux args tys' 
      | _ => []
    end in aux args tys.

Definition args_used npars e := 
  let tys := flat_inductive_list_args npars e in 
  args_used_aux e tys.

(* [A11; ...; A1n]
 ... [Ak1; ...; Akn] becomes 
[A1; ...; Ak1] ... [A1n ; ... Akn] *)
Fixpoint transpose_list_of_list


Definition build_sum_types_with_args_used (l : list (list term))


  








(* We need to look at the field 
env_elements of R to look which types require an argument 
and then, which sum types to build *)
