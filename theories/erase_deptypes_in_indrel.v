Require Import utilities.
Require Import List.
Import ListNotations.
Require Import MetaCoq.Template.All.
Import MCMonadNotation.
Require Import erase_type_in_indexes.
Unset MetaCoq Strict Unquote Universe Mode.


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
| doors_o_callee_is_open (d : door) (ω : bool*bool) (x : bool) (equ : true = x)
  : doors_o_callee ω bool (IsOpen d) x
| doors_o_callee_toggle (d : door) (ω : bool*bool) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

MetaCoq Quote Recursively Definition doc_rec := doors_o_callee.

Inductive doors_o_caller : (bool*bool) -> forall (a : Type), DOORS a -> Prop :=
| req_is_open (d : door) (ω : bool*bool)
  : doors_o_caller ω bool (IsOpen d)
| req_toggle (d : door) (ω : bool*bool) (H : ω.1 = false -> ω.2 = false)
  : doors_o_caller ω unit (Toggle d).

Parameter id_correct : nat -> bool.

Inductive bank_operation_correct : forall (a : Type), bank_operation a -> Prop :=
| Withdraw_correct (u : user_id) (solde : nat) (amount : nat) (_ : Nat.leb solde amount) :
  id_correct u = true -> bank_operation_correct unit (Withdraw u solde amount)
| GetBalance_correct (u : user_id) : id_correct u -> bank_operation_correct nat (GetBalance u).

Inductive trm : Type -> Type :=
| N : nat -> trm nat
| B : bool -> trm bool.

Inductive trm_le : forall (A B : Type), trm A -> trm B -> Prop :=
| lez (n : nat) : trm_le nat nat (N 0) (N n) 
| leS (n : nat) (m : nat) : trm_le nat nat (N n) (N m) -> trm_le nat nat (N n) (N (S m))
| leB : trm_le bool bool (B false) (B true).

Record env := mk_env 
  { env_parameters : list (aname*term*nat); (* the name of a parameter, its type and its db index *)
    env_arguments : list (aname*term*nat); (* idem for the arguments of the inductive *)
    env_types : list (aname*term*nat); (* idem for its args of type Type *)
    env_inductives : list (aname*term*nat); (* idem for the inductives arguments *)
    env_elements : list (aname*term*nat); (* idem for the args of the args of type Type *)
    domain : term;
    constructors : list term
 }. 

Definition lift10_term_and_db (p : aname*term*nat) :=
  let x := p.1.1 in 
  let y := p.1.2 in
  let z := p.2 in
  (x, lift 1 0 y, S z). 

(* substitutes tRel 0 by tRel 0 
when tRel 0 is not in the term, it is useful because all db indexes will decrease of 1 *)
Definition subst_term_and_db (p : aname*term*nat) :=
  let x := p.1.1 in 
  let y := p.1.2 in
  let z := p.2 in
  (x, subst [tRel 0] 0 y, z-1).

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
                   constructors := mind_entry_lc x
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
                   constructors := []
                |} mind.

(* Definition foo := ({|
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

Definition bar := get_env foo. *)

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

(* 
Deal with the constructor
We look at the domain of each constructor: it is the 
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
  (l : list term) 
   nb_args nb_tys : list (list term) :=
  List.map (fun x => collect_tys_term x nb_args nb_tys) l. 

(* [A11; ...; A1n] ...
 [Ak1; ...; Akn] becomes 
[A1; ...; Ak1] ... [A1n ; ... Akn] *)

Fixpoint transpose_list_of_list_aux (l acc : list (list term)) (n : nat) : list (list term) :=
  match n with
    | 0 => acc
    | S n' => 
       transpose_list_of_list_aux l 
       (mapi (fun i x => ([nth i (nth n' l []) default_reif]++x)) acc) n'
  end.

Definition transpose_list_of_list (l : list (list term)) :=
  let n := Datatypes.length (hd [] l) in
  let m := Datatypes.length l in
  let fix aux n := 
  match n with
    | 0 => []
    | S n' => [] :: aux n'
  end
  in transpose_list_of_list_aux l (aux n) m.

(* Compute transpose_list_of_list [[nat_reif; unit_reif; <%False%>] ; 
  [<%True%>; or_reif; bool_reif] ;
[<% Type%> ; <%Prop %> ; <% DOORS %>] ]. *)

Definition tys_term_for_each_constructor  
  (e : env)  :=
      let lc := constructors e in
      let nb_args := Datatypes.length (env_parameters e) + Datatypes.length (env_arguments e) in
      let nb_tys := Datatypes.length (env_types e) in
      transpose_list_of_list (collect_tys_list lc nb_args nb_tys).

(* Compute tys_term_for_each_constructor bar. *)

(* Deal with the inductive *)

(* returns each list of arguments used by 
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

Fixpoint find_rel_in_triple 
  (n : nat) (l : list (aname*term*nat)) :=
    match l with
  | (_, tRel k, _) :: l' => if Nat.eqb n k then true else find_rel_in_triple n l'
  | _ :: l' => find_rel_in_triple n l'
  | [] => false
  end.

Definition args_used_aux e tys :=
  let args := env_elements e in
  let fix aux args tys :=
    match tys with
      | tRel k :: tys' => find_rel_in_triple k args :: aux args tys' 
      | _ => []
    end in aux args tys.

Definition args_used npars e : list bool:= 
  let tys := flat_inductive_list_args npars e in 
  args_used_aux e tys.

Fixpoint sum_types_with_args_used 
  (l : list (list term)) (l' : list bool) := 
  match l, l' with
    | [], [] => []
    | _, [] => []
    | [], _ => []
    | x :: xs, true :: ys => mkSum x :: sum_types_with_args_used xs ys
    | _ :: xs, false :: ys =>  sum_types_with_args_used xs ys
  end.

Definition get_sum_types
(e : env) :=
  let npars := Datatypes.length (env_parameters e) in
  let l := tys_term_for_each_constructor e in
  let args_usd := args_used npars e in
  sum_types_with_args_used l args_usd.

(* Compute get_sum_types (get_env foo). *)

(* we add the correct inl and inr terms according to which type 
the constructor use in the sum type *)

Definition inl_reif := <%@inl%>. 

Definition inr_reif := <%@inr%>.

Fixpoint add_inls (t : term) (n : nat) :=
  match n with
    | 0 => t
    | S n' => tApp inl_reif [hole ; hole ; add_inls t n']
  end.

Definition add_inls_inrs 
(t : term)
(nb_constructors : nat) (* How many constructor there are *)
(nb_constructor : nat) (* The current constructor *) :=
  match nb_constructor with
    | 0 => add_inls t nb_constructors
    | S _ => add_inls (tApp inr_reif [hole; hole ; t]) (nb_constructors-nb_constructor)
  end.

Fixpoint add_inls_inrs_n_aux (l : list term) (n nb_constructors : nat) :=
   match n, l with
    | 0, [x] => [add_inls_inrs x nb_constructors 0]
    | 0, [] => []
    | S n', x :: xs => add_inls_inrs x nb_constructors n :: add_inls_inrs_n_aux xs n' nb_constructors
    | _, _ => []
    end.

Definition add_inls_inrs_n (ltypes : list term) (nb_constructors : nat) :=
  add_inls_inrs_n_aux ltypes nb_constructors nb_constructors.

(* Compute (List.rev (add_inls_inrs_n (List.rev [<%bool%> ; <%unit%>]) 1)). *)

Fixpoint listtRel0 (n : nat) :=
  match n with
    | 0 => []
    | S n' => tRel 0 :: listtRel0 n'
  end.

Definition new_arguments_for_each_constructor 
(e : env) :=
  let ltys := tys_term_for_each_constructor e in
  let fix aux ltys' :=
  match ltys' with
    | [] => []
    | x :: xs => let n := Datatypes.length x in
       List.rev (add_inls_inrs_n (listtRel0 n) (n-1)) :: aux xs end
    in (aux ltys).

(* Compute new_arguments_for_each_constructor bar. *)

(* Definition tata := (add_inls_inrs <%unit%> 3 2). Compute tata. *)

Fixpoint lookup_kername (kn : kername) (l : list (kername*kername)) :=
  match l with
  | [] =>  default_error_kn
  | (kn1, kn2) :: xs =>  if eq_kername kn kn1 then kn2 else lookup_kername kn xs
  end.

Definition unlift1 t := subst10 (tRel 0) t. 

Definition replace_by_new_inductive 
(t : term) (indus : list (kername*kername)) (nb : nat) :=
  match t with
    | tInd  {| inductive_mind := kn ; inductive_ind := n |} inst => 
        tInd  {| inductive_mind := (lookup_kername kn indus) ;
        inductive_ind := n |} inst
    | tApp (tInd {| inductive_mind := kn ; inductive_ind := n |} inst) l => 
        let l' := List.skipn nb (List.map unlift1 l) in
        tApp (tInd {| inductive_mind := (lookup_kername kn indus) ; inductive_ind := n |} inst) l'
    | _ => default_reif (* should not happen *)
  end. 

Fixpoint subst_two_lists (l l' : list term) :=
  match l, l' with
    | [], [] => []
    | x :: xs, y :: ys => subst10 x y :: subst_two_lists xs ys
    | _, _ => []
  end.

Definition transfo_in_indu t indus :=
  match t with
    | tApp (tConstruct {| inductive_mind := kn ; inductive_ind := n |} m inst) l =>
        let kn' := lookup_kername kn indus in 
        tApp (tConstruct {| inductive_mind := kn' ; inductive_ind := n |} m inst) l
    | _ => default_reif (* should not happen *)
  end.

Definition transfo_in_list_indus l indus :=
List.map (fun x => transfo_in_indu x indus) l.

(* old domain of constructor
 I [params]++[arguments]++[Types]++[Is applied to params]++[elements]
There is no db index in types so deleting them will not change the 
db indexes of other terms.
I [params]++[arguments]++[I's applied to params]++[inl or inr elements]
*) 
Definition transfo_in_list 
(e : env) 
(lsum : list term)
(indus : list (kername*kername))
(l : list term) := 
  let pars := env_parameters e in
  let npars := Datatypes.length pars in
  let nargs := Datatypes.length (env_arguments e) in
  let ntypes := Datatypes.length (env_types e) in
  let nindus := Datatypes.length (env_inductives e) in
  (List.firstn (npars+nargs) l) ++ (* remove the types *)
  transfo_in_list_indus (List.firstn nindus (List.skipn (npars+nargs+ntypes) l)) indus ++ (* change the Is by the I's and remove the types *)
  subst_two_lists (List.skipn (npars+nargs+ntypes+nindus) l) lsum.

Definition transfo_type_constructor 
(t : term) 
(lsum : list term) (* the arguments of type sum *)
(e : env)
(indus : list (kername*kername))
:= 
  let fix aux t e :=
  match t with
    | tProd Na Ty u => tProd Na (aux Ty e) (aux u e)
    | tApp (tRel k) l => tApp (tRel k) (transfo_in_list e lsum indus l)
    | _ => t
  end in aux t e.

Definition transformed_env_inductive
(e : env) 
(indus : list (kername*kername)) (* the mapping between the old and the new inductive *)
:=
  let sums := get_sum_types e in 
  let nb_unlift := Datatypes.length (env_types e) in
  let n := Datatypes.length (env_parameters e) + Datatypes.length (env_types e) in
  let new_args := transpose_list_of_list (new_arguments_for_each_constructor e) in
  let fix unlift l n := match n with
    | 0 => l
    | S n => unlift (List.map subst_term_and_db l) n
  end in 
  {| 
  env_parameters := unlift (env_parameters e) nb_unlift ;
  env_arguments := unlift (env_arguments e) nb_unlift ;
  env_types := [] ;
  env_inductives := List.map (fun x => (x.1.1, replace_by_new_inductive x.1.2 indus n, x.2)) 
(env_inductives e) ;
  env_elements := mapi (fun i p => (p.1.1, nth i sums default_reif, p.2)) (env_elements e)  ;
  domain := domain e ; constructors :=
  mapi (fun i x => transfo_type_constructor x (nth i new_args []) e indus) (constructors e); |}.

Fixpoint mkProdsNamed (t : term) (l : list (aname*term*nat)) :=
  match l with
    | [] => t
    | x :: xs => tProd x.1.1 x.1.2 (mkProdsNamed t xs)
  end.

Definition reconstruct_arity 
(e : env) :=
mkProdsNamed (domain e) ((env_arguments e)++(env_types e)++(env_inductives e)++(env_elements e)).

Definition erase_deptypes_in_indrel_inductive
  (id : string) 
  (mind : mutual_inductive_entry) 
  (indus : list (kername*kername)) :=
  let e := get_env mind in
  let opt := get_first_oind_from_mind mind in
  match opt with
    | None => mind
    | Some oind =>
      let e' := transformed_env_inductive e indus in
      let oind' := 
      {| 
        mind_entry_typename := id;
        mind_entry_arity := reconstruct_arity e' ;
        mind_entry_consnames := List.map (fun x => String.append x "'") oind.(mind_entry_consnames);
        mind_entry_lc := constructors e' ;
      |} in 
      {| 
       mind_entry_record := mind.(mind_entry_record);
        mind_entry_finite := mind.(mind_entry_finite);
        mind_entry_params := mind.(mind_entry_params);
        mind_entry_inds := [oind'];
        mind_entry_universes := mind.(mind_entry_universes); 
        mind_entry_template := mind.(mind_entry_template); 
        mind_entry_variance := mind.(mind_entry_variance);
        mind_entry_private := mind.(mind_entry_private);
      |} 
   end.

(* Definition bar2 := erase_deptypes_in_indrel_inductive "dooc'"%bs foo list_kn_test.  *)

Definition erase_deptypes_in_indrel 
(indus : list (kername*kername))
(t : term)
 :=
  p <- quote_inductive_and_kername t ;;
  match p with
    | (decl, kn) => 
      let mind := mind_body_to_entry decl in 
      fresh <- tmFreshName (String.append kn.2 ("'")%bs) ;;
      let mind_transfo := erase_deptypes_in_indrel_inductive fresh mind indus in 
      res <- tmEval all mind_transfo ;;
      tmPrint res ;;
      tmMkInductive true mind_transfo
  end.

Definition erase_dep_transform_pred (l : list term) (R : term) :=
  res <- erase_type_in_indexes l ;;
  let indus := res.2 in
  erase_deptypes_in_indrel indus R ;; 
  res0 <- tmEval all res.1 ;;
  tmReturn res0.

MetaCoq Run (erase_dep_transform_pred [<%DOORS%>] <% doors_o_callee %> >>= tmPrint).

MetaCoq Run (erase_deptypes_in_indrel list_kn_test <% doors_o_caller %>).
Print doors_o_caller'.
MetaCoq Run (erase_deptypes_in_indrel list_kn_test <% bank_operation_correct %>).
Print bank_operation_correct'.

MetaCoq Run (erase_dep_transform_pred [<%trm%>] <%trm_le%>).
Print trm_le.
Print trm_le'.

Require Import Coq.Program.Equality.

Lemma equivalence_trm_le_nat : 
  forall (A B : Type) (n : trm A) (m : trm B), 
trm_le A B n m <-> trm_le' (transfo0 A n) (transfo0 B m).
Proof. intros n m. split.
  + intro H. induction H. simpl. constructor. 
    simpl. simpl in IHtrm_le. constructor. assumption. simpl. constructor.
  + intro H. dependent induction H. 
    - destruct n0; destruct m0. destruct n. constructor. inversion x. inversion x0. 
      inversion x. inversion x0. inversion x. 
    -  destruct n0; destruct m0. subst. inversion x0. inversion x. subst. constructor.
  apply IHtrm_le'. assumption. reflexivity. inversion x. inversion x0. inversion x0. 
    - destruct n0; destruct m0. inversion x0. inversion x. inversion x0. inversion x.
  inversion x. subst. inversion x0. constructor. Qed. 

Lemma trm_le_is_le :
  forall (n m : nat), trm_le nat nat (N n) (N m) <-> Nat.leb n m = true.
Proof. intros. rewrite equivalence_trm_le_nat; simpl.

