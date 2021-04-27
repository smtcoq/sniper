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


Goal False.
get_def length. expand_hyp length_def.
Abort.
(*  | tFix : mfixpoint term -> nat -> term *)
Print mfixpoint.
(* fun term : Type => list (def term)
     : Type -> Type *)

Print def.

(* Record def (term : Type) : Type := mkdef
  { dname : aname;  dtype : term;  dbody : term;  rarg : nat } 
rarg = index of the recursive argument *)

MetaCoq Quote Recursively Definition length_reif_rec := Datatypes.length.

Print length_reif_rec.



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


Definition body_reif := tLambda
                {|
                binder_name := nNamed "A"%string;
                binder_relevance := Relevant |}
                (tSort
                   (Universe.of_levels
                      (inr (Level.Level "TransfoCoq.elimination_fixpoints.271"))))
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
                      tRel 0])
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
                            tRel 1])
                         (tInd
                            {|
                            inductive_mind := (MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                              "nat"%string);
                            inductive_ind := 0 |} [])) 
                      (tRel 0)
                      [(0,
                       tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["Datatypes"%string;
                                              "Init"%string; "Coq"%string],
                                           "nat"%string);
                         inductive_ind := 0 |} 0 []);
                      (2,
                      tLambda
                        {|
                        binder_name := nNamed "a"%string;
                        binder_relevance := Relevant |} 
                        (tRel 1)
                        (tLambda
                           {|
                           binder_name := nNamed "xs"%string;
                           binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                 inductive_mind := (
                                                   MPfile
                                                   ["Datatypes"%string;
                                                   "Init"%string; "Coq"%string],
                                                   "list"%string);
                                 inductive_ind := 0 |} []) [
                              tRel 2])
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (
                                                   MPfile
                                                   ["Datatypes"%string;
                                                   "Init"%string; "Coq"%string],
                                                   "nat"%string);
                                 inductive_ind := 0 |} 1 [])
                              [tApp (tRel 4) [tRel 3; tRel 0]])))])).




MetaCoq Quote Definition goal := (Datatypes.length = fun A (l : list A) => match l with 
| nil => 0
| cons _ xs => S (Datatypes.length xs) 
end).

Print goal.

(* tApp
  (tInd
     {|
     inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
     inductive_ind := 0 |} [])
  [tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
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
  tConst (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string) [];
  tLambda {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
    (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.63"))))
    (tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
       (tApp
          (tInd
             {|
             inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                               "list"%string);
             inductive_ind := 0 |} []) [tRel 0])
       (tCase
          ({|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "list"%string);
           inductive_ind := 0 |}, 1, Relevant)
          (tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
             (tApp
                (tInd
                   {|
                   inductive_mind := (MPfile
                                        ["Datatypes"%string; "Init"%string; "Coq"%string],
                                     "list"%string);
                   inductive_ind := 0 |} []) [tRel 1])
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
            (tRel 1)
            (tLambda {| binder_name := nNamed "xs"%string; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                     inductive_mind := (MPfile
                                          ["Datatypes"%string; "Init"%string;
                                          "Coq"%string], "list"%string);
                     inductive_ind := 0 |} []) [tRel 2])
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
                        "length"%string) []) [tRel 3; tRel 0]])))]))]*)

Fail MetaCoq Unquote Definition test_unquote := test_transfo.

(* Definition replace_fix (t : term) (f : term) :=
let f' := get_def_in_fix f 
in match t with *)




MetaCoq Quote Definition test' := (Datatypes.length =
             (fix length {A} (l : list A) : nat :=
                match l with
                | nil  => 0
                | cons _ xs => S (length xs)
                end)).

Print test'.

(* tApp
  (tInd
     {|
     inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                       "eq"%string);
     inductive_ind := 0 |} [])
  [tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
     (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.63"))))
     (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
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
                                ["Datatypes"%string; "Init"%string;
                                "Coq"%string], "nat"%string);
           inductive_ind := 0 |} []));
  tConst
    (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string)
    [];
  tFix
    [{|
     dname := {|
              binder_name := nNamed "length"%string;
              binder_relevance := Relevant |};
     dtype := tProd
                {|
                binder_name := nNamed "A"%string;
                binder_relevance := Relevant |}
                (tSort
                   (Universe.of_levels
                      (inr (Level.Level "TransfoCoq.elimination_fixpoints.271"))))
                (tProd
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
                      tRel 0])
                   (tInd
                      {|
                      inductive_mind := (MPfile
                                           ["Datatypes"%string; "Init"%string;
                                           "Coq"%string], "nat"%string);
                      inductive_ind := 0 |} []));
     dbody := tLambda
                {|
                binder_name := nNamed "A"%string;
                binder_relevance := Relevant |}
                (tSort
                   (Universe.of_levels
                      (inr (Level.Level "TransfoCoq.elimination_fixpoints.271"))))
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
                      tRel 0])
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
                            tRel 1])
                         (tInd
                            {|
                            inductive_mind := (MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                              "nat"%string);
                            inductive_ind := 0 |} [])) 
                      (tRel 0)
                      [(0,
                       tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["Datatypes"%string;
                                              "Init"%string; "Coq"%string],
                                           "nat"%string);
                         inductive_ind := 0 |} 0 []);
                      (2,
                      tLambda
                        {|
                        binder_name := nNamed "a"%string;
                        binder_relevance := Relevant |} 
                        (tRel 1)
                        (tLambda
                           {|
                           binder_name := nNamed "xs"%string;
                           binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                 inductive_mind := (
                                                   MPfile
                                                   ["Datatypes"%string;
                                                   "Init"%string; "Coq"%string],
                                                   "list"%string);
                                 inductive_ind := 0 |} []) [
                              tRel 2])
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (
                                                   MPfile
                                                   ["Datatypes"%string;
                                                   "Init"%string; "Coq"%string],
                                                   "nat"%string);
                                 inductive_ind := 0 |} 1 [])
                              [tApp (tRel 4) [tRel 3; tRel 0]])))]));
     rarg := 1 |}] 0]


*)

MetaCoq Quote Definition length_reif := Datatypes.length.

Definition toto := tApp
  (tInd
     {|
     inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                       "eq"%string);
     inductive_ind := 0 |} [])
  [tProd {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
     (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.63"))))
     (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
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
                                ["Datatypes"%string; "Init"%string;
                                "Coq"%string], "nat"%string);
           inductive_ind := 0 |} []));
  tConst
    (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string)
    []; subst10 length_reif body_reif].


MetaCoq Unquote Definition toto_unquote := toto.
Print toto_unquote.



















