Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import eta_expand.
Require Import List.

Definition A := (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |} []) [tRel 2]).
Definition e := [(MPfile ["List"%string; "Lists"%string; "Coq"%string], "hd"%string,
       ConstantDecl
         {|
         cst_type := tProd
                       {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                       (tSort
                          {|
                          Universe.t_set := {|
                                            UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Lists.List.1", 0)];
                                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Lists.List.1", 0) |};
                          Universe.t_ne := Logic.eq_refl |})
                       (tProd
                          {|
                          binder_name := nNamed "default"%string;
                          binder_relevance := Relevant |} (tRel 0)
                          (tProd
                             {|
                             binder_name := nNamed "l"%string;
                             binder_relevance := Relevant |}
                             (tApp
                                (tInd
                                   {|
                                   inductive_mind := (MPfile
                                                        ["Datatypes"%string; "Init"%string;
                                                        "Coq"%string], "list"%string);
                                   inductive_ind := 0 |} []) [tRel 1]) 
                             (tRel 2)));
         cst_body := Some
                       (tLambda
                          {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                          (tSort
                             {|
                             Universe.t_set := {|
                                               UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Lists.List.1", 0)];
                                               UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Lists.List.1", 0) |};
                             Universe.t_ne := Logic.eq_refl |})
                          (tLambda
                             {|
                             binder_name := nNamed "default"%string;
                             binder_relevance := Relevant |} (tRel 0)
                             (tLambda
                                {|
                                binder_name := nNamed "l"%string;
                                binder_relevance := Relevant |}
                                (tApp
                                   (tInd
                                      {|
                                      inductive_mind := (MPfile
                                                           ["Datatypes"%string; "Init"%string;
                                                           "Coq"%string], "list"%string);
                                      inductive_ind := 0 |} []) [tRel 1])
                                (tCase
                                   ({|
                                    inductive_mind := (MPfile
                                                         ["Datatypes"%string; "Init"%string;
                                                         "Coq"%string], "list"%string);
                                    inductive_ind := 0 |}, 1, Relevant)
                                   (tLambda
                                      {|
                                      binder_name := nNamed "l"%string;
                                      binder_relevance := Relevant |}
                                      (tApp
                                         (tInd
                                            {|
                                            inductive_mind := (MPfile
                                                                 ["Datatypes"%string;
                                                                 "Init"%string; "Coq"%string],
                                                              "list"%string);
                                            inductive_ind := 0 |} []) [
                                         tRel 2]) (tRel 3)) (tRel 0)
                                   [(0, tRel 1);
                                   (2,
                                   tLambda
                                     {|
                                     binder_name := nNamed "x"%string;
                                     binder_relevance := Relevant |} 
                                     (tRel 2)
                                     (tLambda
                                        {|
                                        binder_name := nNamed "l0"%string;
                                        binder_relevance := Relevant |}
                                        (tApp
                                           (tInd
                                              {|
                                              inductive_mind := (MPfile
                                                                 ["Datatypes"%string;
                                                                 "Init"%string; "Coq"%string],
                                                                "list"%string);
                                              inductive_ind := 0 |} []) [
                                           tRel 3]) (tRel 1)))]))));
         cst_universes := Monomorphic_ctx
                            ({| VSet.this := []; VSet.is_ok := LevelSet.Raw.empty_ok |},
                            {|
                            CS.this := [(Level.Level "Coq.Lists.List.1",
                                        ConstraintType.Le BinNums.Z0,
                                        Level.Level "Coq.Init.Datatypes.60")];
                            CS.is_ok := ConstraintSet.Raw.add_ok (s:=[])
                                          (Level.Level "Coq.Lists.List.1",
                                          ConstraintType.Le BinNums.Z0,
                                          Level.Level "Coq.Init.Datatypes.60")
                                          ConstraintSet.Raw.empty_ok |}) |});
      (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string,
      InductiveDecl
        {|
        ind_finite := Finite;
        ind_npars := 2;
        ind_params := [{|
                       decl_name := {|
                                    binder_name := nNamed "x"%string;
                                    binder_relevance := Relevant |};
                       decl_body := None;
                       decl_type := tRel 0 |};
                      {|
                      decl_name := {|
                                   binder_name := nNamed "A"%string;
                                   binder_relevance := Relevant |};
                      decl_body := None;
                      decl_type := tSort
                                     {|
                                     Universe.t_set := {|
                                                       UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0)];
                                                       UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0) |};
                                     Universe.t_ne := Logic.eq_refl |} |}];
        ind_bodies := [{|
                       ind_name := "eq"%string;
                       ind_type := tProd
                                     {|
                                     binder_name := nNamed "A"%string;
                                     binder_relevance := Relevant |}
                                     (tSort
                                        {|
                                        Universe.t_set := {|
                                                          UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0)];
                                                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0) |};
                                        Universe.t_ne := Logic.eq_refl |})
                                     (tProd
                                        {|
                                        binder_name := nNamed "x"%string;
                                        binder_relevance := Relevant |} 
                                        (tRel 0)
                                        (tProd
                                           {|
                                           binder_name := nAnon;
                                           binder_relevance := Relevant |} 
                                           (tRel 1) (tSort Universe.lProp)));
                       ind_kelim := IntoAny;
                       ind_ctors := [("eq_refl"%string,
                                     tProd
                                       {|
                                       binder_name := nNamed "A"%string;
                                       binder_relevance := Relevant |}
                                       (tSort
                                          {|
                                          Universe.t_set := {|
                                                            UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0)];
                                                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Logic.13", 0) |};
                                          Universe.t_ne := Logic.eq_refl |})
                                       (tProd
                                          {|
                                          binder_name := nNamed "x"%string;
                                          binder_relevance := Relevant |} 
                                          (tRel 0) (tApp (tRel 2) [tRel 1; tRel 0; tRel 0])),
                                     0)];
                       ind_projs := [];
                       ind_relevance := Relevant |}];
        ind_universes := Monomorphic_ctx
                           ({|
                            VSet.this := [Level.Level "Coq.Init.Logic.13"];
                            VSet.is_ok := LevelSet.Raw.add_ok (s:=[])
                                            (Level.Level "Coq.Init.Logic.13")
                                            LevelSet.Raw.empty_ok |},
                           {| CS.this := []; CS.is_ok := ConstraintSet.Raw.empty_ok |});
        ind_variance := None |});
      (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "list"%string,
      InductiveDecl
        {|
        ind_finite := Finite;
        ind_npars := 1;
        ind_params := [{|
                       decl_name := {|
                                    binder_name := nNamed "A"%string;
                                    binder_relevance := Relevant |};
                       decl_body := None;
                       decl_type := tSort
                                      {|
                                      Universe.t_set := {|
                                                        UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)];
                                                        UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0) |};
                                      Universe.t_ne := Logic.eq_refl |} |}];
        ind_bodies := [{|
                       ind_name := "list"%string;
                       ind_type := tProd
                                     {|
                                     binder_name := nNamed "A"%string;
                                     binder_relevance := Relevant |}
                                     (tSort
                                        {|
                                        Universe.t_set := {|
                                                          UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)];
                                                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0) |};
                                        Universe.t_ne := Logic.eq_refl |})
                                     (tSort
                                        {|
                                        Universe.t_set := {|
                                                          UnivExprSet.this := [
                                                                 (Level.lSet, 0);
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)];
                                                          UnivExprSet.is_ok := UnivExprSet.Raw.add_ok
                                                                 (s:=[(Level.lSet, 0)])
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)
                                                                 (UnivExprSet.Raw.singleton_ok
                                                                 (Level.lSet, 0)) |};
                                        Universe.t_ne := Universes.Universe.add_obligation_1
                                                           (Level.Level
                                                              "Coq.Init.Datatypes.60", 0)
                                                           {|
                                                           Universe.t_set := {|
                                                                 UnivExprSet.this := [(Level.lSet,
                                                                 0)];
                                                                 UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (Level.lSet, 0) |};
                                                           Universe.t_ne := Logic.eq_refl |} |});
                       ind_kelim := IntoAny;
                       ind_ctors := [("nil"%string,
                                     tProd
                                       {|
                                       binder_name := nNamed "A"%string;
                                       binder_relevance := Relevant |}
                                       (tSort
                                          {|
                                          Universe.t_set := {|
                                                            UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)];
                                                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0) |};
                                          Universe.t_ne := Logic.eq_refl |})
                                       (tApp (tRel 1) [tRel 0]), 0);
                                    ("cons"%string,
                                    tProd
                                      {|
                                      binder_name := nNamed "A"%string;
                                      binder_relevance := Relevant |}
                                      (tSort
                                         {|
                                         Universe.t_set := {|
                                                           UnivExprSet.this := [(
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0)];
                                                           UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                                 (
                                                                 Level.Level
                                                                 "Coq.Init.Datatypes.60", 0) |};
                                         Universe.t_ne := Logic.eq_refl |})
                                      (tProd
                                         {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant |} 
                                         (tRel 0)
                                         (tProd
                                            {|
                                            binder_name := nAnon;
                                            binder_relevance := Relevant |}
                                            (tApp (tRel 2) [tRel 1]) 
                                            (tApp (tRel 3) [tRel 2]))), 2)];
                       ind_projs := [];
                       ind_relevance := Relevant |}];
        ind_universes := Monomorphic_ctx
                           ({|
                            VSet.this := [Level.Level "Coq.Init.Datatypes.60"];
                            VSet.is_ok := LevelSet.Raw.add_ok (s:=[])
                                            (Level.Level "Coq.Init.Datatypes.60")
                                            LevelSet.Raw.empty_ok |},
                           {| CS.this := []; CS.is_ok := ConstraintSet.Raw.empty_ok |});
        ind_variance := None |})].

Ltac unquote_term t_reif := 
run_template_program (tmUnquote t_reif) ltac:(fun t => 
let x := constr:(t.(my_projT2)) in let y := eval hnf in x in pose y).

MetaCoq Quote Definition unit_reif := unit.

MetaCoq Quote Definition eq_reif := Eval cbn in @eq.


(* Equality of type B between two terms *)
Definition mkEq (B t1 t2 : term) := tApp eq_reif [B ; t1 ; t2].


(* find the bodies of an inductive simply quoted *)
Fixpoint get_decl_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => None 
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then let loind := ind_bodies mind in Some loind else get_decl_inductive I e'
                                  | _ => get_decl_inductive I e'
                               end)    
    end
end
| _ => None
end.

(* find the number of parameters of an inductive simply quoted *)
Fixpoint get_npar_inductive (I : term) (e : global_env) :=
match I with 
| tInd ind _ => match ind.(inductive_mind) with
          | (file, ident) => match e with 
                      | [] => 0
                      | (na,d) :: e' => 
                                (match d with
                                  | InductiveDecl mind => if (String.eqb
ident na.2) then ind_npars mind else get_npar_inductive I e'
                                  | _ => get_npar_inductive I e'
                               end)    
    end
end
| _ => 0
end.



Definition get_type_constructor (c : term):=
match c with
| tConstruct ind _ _ => let kn := ind.(inductive_mind) in 
tInd {| inductive_mind := kn ; inductive_ind := 0 |} []
| _ => unit_reif
end.



(* does not work for mutual inductives *)
Ltac list_ctors_and_types I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval compute in y.(ind_ctors) in pose z
| None => fail
end).

(*  in the type of the constructor we need to susbtitute the free variables by the corresponding inductive type *)

Fixpoint subst_type_constructor_list' (l : list ((string × term) × nat)) (p : term) :=

match l with 
| nil => nil
| ((_, Ty), _):: l' => (subst10 p Ty)  :: (subst_type_constructor_list' l' p)
end.



MetaCoq Quote Recursively Definition list_reif := list.
Print list_reif.


(* Fixpoint subst_type_constructor_list_no_param (l : list ((string × term) × nat)) (T : term) (n : nat) :=
let l' := subst_type_constructor_list' l T n in 
let fix aux (l' : list term) n := match (n, l') with
| (0, _) => l'
| (S m, nil) => nil
| (S m, x :: xs) => aux xs m
end in rev (aux  (rev l') n).
Check subst_type_constructor_list_no_param. *)

Definition type_no_app t := match t with
| tApp u l => (u, l)
| _ => (t, [])
end.

(* Ltac list_types_of_ctors I :=
run_template_program (tmQuoteRec I) ltac:(fun t => 
let x := eval compute in (get_decl_inductive t.2 t.1) in match x with
| Some (?y::_) => let z := eval cbv in y.(ind_ctors) in 
let v := eval cbv in t.2 in let u := eval cbv in (subst_type_constructor_list' z v) in
pose u
| None => fail 1
end). *)

(* beta reduction *)
Fixpoint typing_prod_list (T : term) (args : list term) := 
match T with
| tProd _ A U => match args with 
        | nil => T
        | x :: xs => typing_prod_list (subst10 x U) xs
        end
| _ => T
end.



(* Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (p : term × (list term)) (n : nat) :=
let T := p.1 in 
let args := p.2 in
match l with 
| nil => nil
| ((_, Ty), _):: l' => (typing_prod_list (subst1 T n Ty) args) :: (subst_type_constructor_list l' p n)
end.
(* subst10 T (tApp Ty args) or (tApp (subst10 T Ty) args)  *) *)

Fixpoint subst_type_constructor_list (l : list ((string × term) × nat)) (p : term × (list term)) (n : nat) :=
let T := p.1 in 
let args := p.2 in
match l with 
| nil => nil
| ((_, Ty), _):: l' => (typing_prod_list (subst10 T Ty) args) :: (subst_type_constructor_list l' p n)
end.

(* t is a term recursively quoted *)
Definition list_types_of_each_constructor t :=
let v := (type_no_app t.2) in (* the inductive not applied to its parameters and the list of its parameters *)
let x := get_decl_inductive v.1 t.1 in (* the first inductive declaration in a mutual inductive block  *)
let n := get_npar_inductive v.1 t.1 in  (* numbers of parameters *)
match x with
| Some y => match y with 
          | nil => nil
          | cons y' _ => let z := y'.(ind_ctors) in let u := 
subst_type_constructor_list z v n in u 
          end
| None => nil
end.

Eval cbv in list_types_of_each_constructor (e, A).













(* Definition list_types_of_each_constructor_test t :=
let x := get_decl_inductive t.2 t.1 in match x with
| Some y => match y with 
          | nil => nil
          | cons y' l => let z := y'.(ind_ctors) in let v := t.2 in subst_type_constructor_list' z v
          end
| None => nil
end. *)




Ltac unquote_list l :=
match constr:(l) with
| nil => idtac
| cons ?x ?xs => unquote_term x ; unquote_list xs
end.






Fixpoint get_info_inductive (I : term) := 
let p := type_no_app I in match p.1 with
| tInd ind inst => Some ((ind, inst), p.2)
| _ => None
end.


Fixpoint get_list_of_rel (i : nat) := match i with
| 0 => []
| S n => (get_list_of_rel n) ++ [tRel n] (* n *)
end.




(* gets the list of constructors given an inductive recursively quoted and the number of its constructors *)
Definition get_list_ctors_tConstruct I n := 
let I' := get_info_inductive I in match I' with
| Some J => let ind := J.1.1 in let inst := J.1.2 in let args := J.2 in let 
fix aux n' ind' inst' args :=
match n' with 
| 0 => []
| S m =>  (aux m ind' inst' args) ++ [tApp (tConstruct ind' m inst') args]
end
in aux n J.1.1 J.1.2 J.2
| None => []
end.

(* Definition list_types_of_each_constructor_no_param  t :=
let x := get_decl_inductive t.2 t.1 in let n:= get_npar_inductive t.2 t.1 in 
match x with
| Some y => match y with 
          | nil => nil
          | cons y' l => let z := y'.(ind_ctors) in let v := t.2 in let u := 
subst_type_constructor_list_no_param z v n in u
          end
| None => nil
end. *)

Ltac list_ctors_unquote_requote_rec t :=
run_template_program (tmUnquote t) (fun t => 
let x:= eval hnf in t.(my_projT2) in run_template_program (tmQuoteRec x) ltac:(fun t => 
let x:= eval cbv in (list_types_of_each_constructor t) in pose x)).



Definition get_type_of_args t := 
let fix aux t (acc : list term) := match t with 
| tLambda _ ty s => aux s (ty::acc)
| tProd _ ty s => aux s (ty :: acc)
| _ => acc 
end in aux t [].



Ltac prove_hypothesis H :=
repeat match goal with
  | H' := ?x : ?P |- _ =>  lazymatch P with 
                | Prop => let def := fresh in assert (def : x) by 
(intros ; rewrite H ; reflexivity) ;  clear H'
          end
end.





Definition get_env (T: term) (n  : nat) := 
let fix aux T n acc := 
match (T, n) with
| (tProd _ A t, 0) => ((acc, t), A)
| (tProd _ A t, S n') => aux t n' (A::acc)
| _ => ((acc, T), T)
end
in aux T n [].




Fixpoint prenex_quantif_list (l : list term) (t : term):= 
match l with
| [] => t 
| x :: xs => prenex_quantif_list xs (mkProd x t)
end.

Fixpoint remove_elem (n : nat) (l : list term) := match l, n with
| [], _ => []
| _, 0 => l
| x :: xs, S m => remove_elem m xs
end.


Definition list_of_args (t : term) := let fix aux acc t := match t with
| tProd _ t1 t2 => aux (t1 :: acc) t2
(* | tApp t l => let n := Datatypes.length l in remove_elem n 
(rev (aux acc t)) (* we need to remove the n first elements applied in order to avoid quantifying over them *) *)
| _ => acc
end in aux [] t.


Definition E := (tApp
       (tInd
          {|
          inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                            "eq"%string);
          inductive_ind := 0 |} [])
       [tRel 2;
       tApp (tConst (MPfile ["List"%string; "Lists"%string; "Coq"%string], "hd"%string) [])
         [tRel 2; tRel 1; tRel 0];
       tCase
         ({|
          inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
          inductive_ind := 0 |}, 1, Relevant)
         (tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                  inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                    "list"%string);
                  inductive_ind := 0 |} []) [tRel 2]) (tRel 3)) (tRel 0)
         [(0, tRel 1);
         (2,
         tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |} 
           (tRel 2)
           (tLambda {| binder_name := nNamed "l0"%string; binder_relevance := Relevant |}
              (tApp
                 (tInd
                    {|
                    inductive_mind := (MPfile
                                         ["Datatypes"%string; "Init"%string; "Coq"%string],
                                      "list"%string);
                    inductive_ind := 0 |} []) [tRel 3]) (tRel 1)))]]).
Definition l_constructor := [tApp
        (tConstruct
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |} 0 []) [tRel 2];
     tApp
       (tConstruct
          {|
          inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                            "list"%string);
          inductive_ind := 0 |} 1 []) [tRel 2]].
Definition l_ty_constructor := [tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                              "list"%string);
            inductive_ind := 0 |} []) [tRel 2];
      tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
        (tRel 2)
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tApp
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "list"%string);
                 inductive_ind := 0 |} []) [tRel 3])
           (tApp
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "list"%string);
                 inductive_ind := 0 |} []) [tRel 4]))].

Eval cbv in list_of_args (hd unit_reif ( l_ty_constructor)).

Definition l := [tRel 0;
      tSort
        {|
        Universe.t_set := {|
                          UnivExprSet.this := [(Level.Level "Coq.Lists.List.1", 0)];
                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                 (Level.Level "Coq.Lists.List.1", 0) |};
        Universe.t_ne := Logic.eq_refl |}].


Definition prenex_quantif_list_ctor (c : term) (l : list term) (l' : list term) (E : term) :=
(* c is the constructor reified, l is the list of the type of its arguments, l' is the list of the 
type of the prenex quantification in the hypothesis, E is the environment *)
let n := Datatypes.length l in
prenex_quantif_list l' (prenex_quantif_list l (subst [tApp (lift n 0 c) (rev (get_list_of_rel n))] 0 (lift n 1 E))).

Definition get_equalities (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) :=
let fix aux (E : term) (l_ctors : list term) (l_ty_ctors  : list term) (l_ty : list term) acc :=
match (l_ctors, l_ty_ctors) with
| (nil, _) | (_ , nil) => acc
| (x :: xs, y :: ys) => aux E xs ys l_ty
((prenex_quantif_list_ctor x (list_of_args y) l_ty E) :: acc)
end
in aux E l_ctors l_ty_ctors l_ty [].

(*TODO : tactique qui prend la liste en paramètre + l'hypothèse H et qui prouve l'unquote de la liste 
grâce à H *)

Ltac prove_list_hypothesis H l := match constr:(l) with 
| [] => idtac 
| cons ?x ?xs => run_template_program (tmUnquote x) (fun x => let y := eval cbv in x.(my_projT2) in 
assert y by (rewrite H ; reflexivity) ; prove_list_hypothesis H constr:(xs))
end.

Ltac count_prenex_forall H :=
  match H with
| forall _ : _, ?A => idtac "a" ; constr:(S ltac:(count_prenex_forall A))
| _ => idtac "b" ; constr:(0)
end.

Goal False.
Fail let n := count_prenex_forall (forall (x y z : nat), 3=3) in pose n.
Abort.

Print lift.

Ltac eliminate_pattern_matching_test H :=

  let n := fresh "n" in 
  let n' := fresh "n'" in
  evar (n : nat);
  evar (n': nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x b :=
    match b with 
    | false => 
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n := p) 
                                        end ; 
        tac_rec 0 x true
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y false
      | _ => fail
    end 
    | true => match goal with
              | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y true
              | _ => instantiate (n' := m)
              end
      end
in
    tac_rec 0 ltac:(fresh) false;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in (lift n' 0 prod.2) in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
pose list_of_hyp
(* unquote_list list_of_hyp ; prove_hypothesis H *)
)].


MetaCoq Quote Recursively Definition foo_reif := (fun A (l: list A) => match l with 
| [] => unit
| cons x xs => unit
end).

Print foo_reif.

Definition min1 (x : nat) := match x with
| 0 => 0
| S x => x
end.
Definition min1' := min1.

Definition min1'' := min1'.

Definition min1''' := min1''.

Print list_reif.

MetaCoq Quote Definition hyp_cons_reif := ((forall (A: Type) (x : A) (a : A) (l : list A), 
@hd A x (@cons A a l) = match (@cons A a l) with
| nil => x
| y :: xs => y
end)).

Print hyp_cons_reif.

Goal True.
Proof. 
expand_fun min1.
expand_fun hd.
eliminate_pattern_matching_test H0.
unquote_term (hd unit_reif l0).
unquote_term (hd unit_reif (tl l0)).
let l' := eval unfold l0 in l0 in unquote_list l'.
unquote_term (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tSort
           {|
           Universe.t_set := {|
                             UnivExprSet.this := [(Level.Level "Coq.Lists.List.1", 0)];
                             UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                    (Level.Level "Coq.Lists.List.1", 0) |};
           Universe.t_ne := Logic.eq_refl |})
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
           (tRel 0)
           (tApp
              (tInd
                 {|
                 inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                                   "eq"%string);
                 inductive_ind := 0 |} [])
              [tRel 1;
              tApp (tConst (MPfile ["List"%string; "Lists"%string; "Coq"%string], "hd"%string) [])
                [tRel 1; tRel 0;
                tApp
                  (tApp
                     (tConstruct
                        {|
                        inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                          "list"%string);
                        inductive_ind := 0 |} 0 []) [tRel 1]) []];
              tCase
                ({|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "list"%string);
                 inductive_ind := 0 |}, 1, Relevant)
                (tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                           "list"%string);
                         inductive_ind := 0 |} []) [tRel 1]) (tRel 2))
                (tApp
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                           "list"%string);
                         inductive_ind := 0 |} 0 []) [tRel 1]) [])
                [(0, tRel 0);
                (2,
                tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                  (tRel 1)
                  (tLambda {| binder_name := nNamed "l0"%string; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                           inductive_mind := (MPfile
                                                ["Datatypes"%string; "Init"%string; "Coq"%string],
                                             "list"%string);
                           inductive_ind := 0 |} []) [tRel 2]) (tRel 1)))]]))).



Check cons.
Print list_reif.

exact I.
Qed.



















