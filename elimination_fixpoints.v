Add Rec LoadPath "/home/louise/github.com/louiseddp/smtcoq/coq-8.11/src" as SMTCoq.

Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.Universes.
Require Import MetaCoq.PCUIC.PCUICEquality.
Require Import MetaCoq.PCUIC.PCUICSubstitution.
Require Import MetaCoq.Template.All.
Require Import definitions.
Require Import eta_expand.
Require Import String.
Unset Strict Unquote Universe Mode.

Print term.

(*  | tFix : mfixpoint term -> nat -> term *)
Print mfixpoint.
(* fun term : Type => list (def term)
     : Type -> Type *)

Print def.

(* Record def (term : Type) : Type := mkdef
  { dname : aname;  dtype : term;  dbody : term;  rarg : nat } 
rarg = index of the recursive argument *)

MetaCoq Quote Recursively Definition length_reif := Datatypes.length.

Print length_reif.
(* 
length_reif = 
([(MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string,
  ConstantDecl
    {|
    cst_type := tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                  (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.63"))))
                  (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                             "list"%string);
                           inductive_ind := 0 |} []) [tRel 0])
                     (tInd
                        {|
                        inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                          "nat"%string);
                        inductive_ind := 0 |} []));
    cst_body := Some
                  (tLambda {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                     (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.63"))))
                     (tFix
                        [{|
                         dname := {| binder_name := nNamed "length"%string; binder_relevance := Relevant |};
                         dtype := tProd {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
                                    (tApp
                                       (tInd
                                          {|
                                          inductive_mind := (MPfile
                                                               ["Datatypes"%string; "Init"%string;
                                                               "Coq"%string], "list"%string);
                                          inductive_ind := 0 |} []) [tRel 0])
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                         "nat"%string);
                                       inductive_ind := 0 |} []);
                         dbody := tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
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
                                                             ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                          "list"%string);
                                        inductive_ind := 0 |}, 1, Relevant)
                                       (tLambda
                                          {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
                                          (tApp
                                             (tInd
                                                {|
                                                inductive_mind := (MPfile
                                                                     ["Datatypes"%string; "Init"%string;
                                                                     "Coq"%string], "list"%string);
                                                inductive_ind := 0 |} []) [tRel 2])
                                          (tInd
                                             {|
                                             inductive_mind := (MPfile
                                                                  ["Datatypes"%string; "Init"%string;
                                                                  "Coq"%string], "nat"%string);
                                             inductive_ind := 0 |} [])) (tRel 0)
                                       [(0,
                                        tConstruct
                                          {|
                                          inductive_mind := (MPfile
                                                               ["Datatypes"%string; "Init"%string;
                                                               "Coq"%string], "nat"%string);
                                          inductive_ind := 0 |} 0 []);
                                       (2,
                                       tLambda
                                         {| binder_name := nNamed "a"%string; binder_relevance := Relevant |}
                                         (tRel 2)
                                         (tLambda
                                            {|
                                            binder_name := nNamed "l'"%string;
                                            binder_relevance := Relevant |}
                                            (tApp
                                               (tInd
                                                  {|
                                                  inductive_mind := (MPfile
                                                                       ["Datatypes"%string; "Init"%string;
                                                                       "Coq"%string], "list"%string);
                                                  inductive_ind := 0 |} []) [tRel 3])
                                            (tApp
                                               (tConstruct
                                                  {|
                                                  inductive_mind := (MPfile
                                                                       ["Datatypes"%string; "Init"%string;
                                                                       "Coq"%string], "nat"%string);
                                                  inductive_ind := 0 |} 1 []) [tApp (tRel 3) [tRel 0]])))]);
                         rarg := 0 |}] 0)| );
    cst_universes := Monomorphic_ctx
                       (LevelSetProp.of_list [Level.Level "Coq.Init.Datatypes.63"],
                       ConstraintSet.add
                         (UnivConstraint.make (Level.Level "Coq.Init.Datatypes.63") ConstraintType.Le0
                            (Level.Level "Coq.Init.Datatypes.60")) ConstraintSet.empty) |});
 (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string,
 InductiveDecl
   {|
   ind_finite := Finite;
   ind_npars := 0;
   ind_params := [];
   ind_bodies := [{|
                  ind_name := "nat"%string;
                  ind_type := tSort (Universe.of_levels (inr Level.lSet));
                  ind_kelim := IntoAny;
                  ind_ctors := [("O"%string, tRel 0, 0);
                               ("S"%string,
                               tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tRel 0) (tRel 1),
                               1)];
                  ind_projs := [];
                  ind_relevance := Relevant |}];
   ind_universes := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty);
   ind_variance := None |});
 (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "list"%string,
 InductiveDecl
   {|
   ind_finite := Finite;
   ind_npars := 1;
   ind_params := [{|
                  decl_name := {| binder_name := nNamed "A"%string; binder_relevance := Relevant |};
                  decl_body := None;
                  decl_type := tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))) |}];
   ind_bodies := [{|
                  ind_name := "list"%string;
                  ind_type := tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                                (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                                (tSort
                                   (Universe.from_kernel_repr (Level.lSet, false)
                                      [(Level.Level "Coq.Init.Datatypes.60", false)]));
                  ind_kelim := IntoAny;
                  ind_ctors := [("nil"%string,
                                tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                                  (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                                  (tApp (tRel 1) [tRel 0]), 0);
                               ("cons"%string,
                               tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
                                 (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
                                    (tRel 0)
                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                       (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))), 2)];
                  ind_projs := [];
                  ind_relevance := Relevant |}];
   ind_universes := Monomorphic_ctx
                      (LevelSetProp.of_list [Level.Level "Coq.Init.Datatypes.60"], ConstraintSet.empty);
   ind_variance := None |})],
tConst (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string) [])
     : program *)


(* Returns the definition in a fixpoint *)
Definition get_def_in_fix (f: term) := match f with 
| tFix l _ => match l with 
          | [] => f
          | x :: xs => x.(dbody)
          end
| _ => f
end.

MetaCoq Quote Definition term_test := (forall A (l : list A),
    Datatypes.length l =
    (fix length (s : list A) : nat :=
       match s with
       | nil => 0
       | cons _ s' => S (Datatypes.length s')
       end) l).

Print term_test.

(* tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
  (tSort (Universe.of_levels (inr (Level.Level "TransfoCoq.elimination_fixpoints.217"))))
  (tProd {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "list"%string);
           inductive_ind := 0 |} []) [tRel 0])
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
           inductive_ind := 0 |} [])
        [tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
           inductive_ind := 0 |} [];
        tApp (tConst (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string) [])
          [tRel 1; tRel 0];
        tApp
          (tFix
             [{|
              dname := {| binder_name := nNamed "length"%string; binder_relevance := Relevant |};
              dtype := tProd {| binder_name := nNamed "s"%string; binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "list"%string);
                               inductive_ind := 0 |} []) [tRel 1])
                         (tInd
                            {|
                            inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                              "nat"%string);
                            inductive_ind := 0 |} []);
              dbody := tLambda {| binder_name := nNamed "s"%string; binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "list"%string);
                               inductive_ind := 0 |} []) [tRel 2])
                         (tCase
                            ({|
                             inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                               "list"%string);
                             inductive_ind := 0 |}, 1, Relevant)
                            (tLambda {| binder_name := nNamed "s"%string; binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["Datatypes"%string; "Init"%string;
                                                          "Coq"%string], "list"%string);
                                     inductive_ind := 0 |} []) [tRel 3])
                               (tInd
                                  {|
                                  inductive_mind := (MPfile
                                                       ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                    "nat"%string);
                                  inductive_ind := 0 |} [])) (tRel 0)
                            [(0,
                             tConstruct
                               {|
                               inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "nat"%string);
                               inductive_ind := 0 |} 0 []);
                            (2,
                            tLambda {| binder_name := nNamed "a"%string; binder_relevance := Relevant |}
                              (tRel 3)
                              (tLambda
                                 {| binder_name := nNamed "s'"%string; binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string; "Init"%string;
                                                            "Coq"%string], "list"%string);
                                       inductive_ind := 0 |} []) [tRel 4])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string; "Init"%string;
                                                            "Coq"%string], "nat"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp
                                       (tConst
                                          (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                          "length"%string) []) [tRel 5; tRel 0]])))]);
              rarg := 0 |}] 0) [tRel 0]]))
     : term *)

Definition body_reif := (tLambda {| binder_name := nNamed "s"%string; binder_relevance := Relevant |}
                         (tApp
                            (tInd
                               {|
                               inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "list"%string);
                               inductive_ind := 0 |} []) [tRel 2])
                         (tCase
                            ({|
                             inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                               "list"%string);
                             inductive_ind := 0 |}, 1, Relevant)
                            (tLambda {| binder_name := nNamed "s"%string; binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["Datatypes"%string; "Init"%string;
                                                          "Coq"%string], "list"%string);
                                     inductive_ind := 0 |} []) [tRel 3])
                               (tInd
                                  {|
                                  inductive_mind := (MPfile
                                                       ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                    "nat"%string);
                                  inductive_ind := 0 |} [])) (tRel 0)
                            [(0,
                             tConstruct
                               {|
                               inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "nat"%string);
                               inductive_ind := 0 |} 0 []);
                            (2,
                            tLambda {| binder_name := nNamed "a"%string; binder_relevance := Relevant |}
                              (tRel 3)
                              (tLambda
                                 {| binder_name := nNamed "s'"%string; binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string; "Init"%string;
                                                            "Coq"%string], "list"%string);
                                       inductive_ind := 0 |} []) [tRel 4])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["Datatypes"%string; "Init"%string;
                                                            "Coq"%string], "nat"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp
                                       (tConst
                                          (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                          "length"%string) []) [tRel 5; tRel 0]])))])).



Definition test_transfo := 
tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
  (tSort (Universe.of_levels (inr (Level.Level "TransfoCoq.elimination_fixpoints.217"))))
  (tProd {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "list"%string);
           inductive_ind := 0 |} []) [tRel 0])
     (tApp
        (tInd
           {|
           inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
           inductive_ind := 0 |} [])
        [tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
           inductive_ind := 0 |} [];
        tApp (tConst (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string) [])
          [tRel 1; tRel 0];
        tApp
         body_reif [tRel 0]])).

MetaCoq Quote Definition goal := (forall (A : Type) (l: list A), Datatypes.length l = match l with 
| nil => 0
| cons _ xs => S (Datatypes.length xs) 
end).

Print goal.

Fail MetaCoq Unquote Definition test_unquote := test_transfo.

Definition replace_fix (t : term) (f : term) :=
let f' := get_def_in_fix f 
in match t with












