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

MetaCoq Quote Recursively Definition length_reif_rec := Datatypes.length.

Print length_reif_rec.

Fixpoint eliminate_lambda_aux (t : term) (l : list (aname*term)) :=
match t with 
| tLambda na T u => eliminate_lambda_aux u ((na, T)::l)
| _ => (t, l)
end.

Fixpoint eliminate_lambda t := eliminate_lambda_aux t [].

Fixpoint create_lambda (t : term) (l : list (aname*term)) :=
match l with 
| nil => t
| (na, T):: xs => create_lambda (tLambda na T t) xs
end.


(* Returns the definition in a fixpoint *)
Definition get_def_in_fix_aux  (f: term) := 
let fix aux acc f :=
match f with 
| tLambda na T u => aux ((na, T)::acc) u 
| tFix l _ => match l with 
          | [] => (acc, f)
          | x :: xs => (acc, x.(dbody))
          end
| _ => (acc, f)
end
in aux [] f.

Definition get_def_in_fix (f: term) := 
let p := get_def_in_fix_aux f in
create_lambda p.2 p.1.

MetaCoq Quote Definition term_test := (Datatypes.length =
             (fun A : Type =>
              fix length (l : list A) : nat := match l with
                                               | [] => 0
                                               | _ :: l' => S (length l')
                                               end)).

Print term_test.

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
              inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "list"%string);
              inductive_ind := 0 |} []) [tRel 0])
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
           inductive_ind := 0 |} []));
  tConst (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "length"%string) [];
  tLambda {| binder_name := nNamed "A"%string; binder_relevance := Relevant |}
    (tSort (Universe.of_levels (inr (Level.Level "TransfoCoq.elimination_fixpoints.236"))))
    (tFix
       [{|
        dname := {| binder_name := nNamed "length"%string; binder_relevance := Relevant |};
        dtype := tProd {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
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
                      inductive_ind := 0 |} []);
        dbody := tLambda {| binder_name := nNamed "l"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                           "list"%string);
                         inductive_ind := 0 |} []) [tRel 1])
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
                               inductive_ind := 0 |} []) [tRel 2])
                         (tInd
                            {|
                            inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
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
                        (tRel 2)
                        (tLambda {| binder_name := nNamed "l'"%string; binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                 inductive_mind := (MPfile
                                                      ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                   "list"%string);
                                 inductive_ind := 0 |} []) [tRel 3])
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (MPfile
                                                      ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                   "nat"%string);
                                 inductive_ind := 0 |} 1 []) [tApp (tRel 3) [tRel 0]])))]);
        rarg := 0 |}] 0)] *)


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
             (fun A => fix length (l : list A) : nat :=
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

Compute (subst10 length_reif body_reif).


MetaCoq Unquote Definition toto_unquote := toto.
Print toto_unquote.




Fixpoint replace_tFix_by_def (l : list term) (def : term) := match l with 
| nil => nil
| cons x xs => let p := (eliminate_lambda x) in match p.1 with 
        | tFix _ _ => (subst10 def (get_def_in_fix x)) :: xs
        | _ => x :: (replace_tFix_by_def xs def)
      end
end.

Definition get_args (t : term) := match t with 
| tApp u l => l
| _ => nil
end.

Definition new_app (t : term) (l : list term) := match t with 
| tApp u _ => tApp u l
| _ => t
end.


Ltac eliminate_fix_hyp H := 
let T := type of H in
lazymatch T with 
| @eq ?A ?t ?u => 
let H' := fresh in quote_term T ltac:(fun T =>
quote_term t ltac:(fun t =>
quote_term u ltac:(fun u => 
let l := eval cbv in (get_args T) in 
let l' := eval cbv in (replace_tFix_by_def l t) in 
let eq := eval cbv in (new_app T l')
in idtac eq ;
run_template_program (tmUnquote eq) 
ltac:(fun z => 
let w := eval hnf in (z.(my_projT2)) 
in pose w))))
| _ => fail "not an equality" 
end.

Goal Nat.add = (fun n m : nat => match n with
                            | 0 => m
                            | S p => S (p + m)
                            end).
Proof.
unfold Nat.add.
Abort.

Goal False.
get_def @Datatypes.length.
get_def Nat.add.
eliminate_fix_hyp add_def.
assert P.
unfold P. 
Fail eliminate_fix_hyp length_def.

 expand_hyp length_def.
Abort.














