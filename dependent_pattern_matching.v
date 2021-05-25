Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Require Import definitions.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.
Import ListNotations.
Require Import String.


Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons _ x ls1' => Cons _ x (app _ ls1' _ ls2)
    end.


Variable x : A.


Compute app 0 Nil 2 (Cons 1 x (Cons 0 x Nil)).



  Fixpoint inject (ls : list A) : ilist (Datatypes.length ls) :=
    match ls in (list _) return (ilist (Datatypes.length ls)) with
      | nil => Nil
      | h :: t => Cons _ h (inject t)
    end.


  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject _ t
    end.



MetaCoq Quote Definition app_reif := 

(fun n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) =>
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons _ x ls1' => Cons _ x (app _ ls1' _ ls2)
    end).


Ltac eliminate_pattern_matching_test H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) 
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
 pose list_of_hyp) ].

MetaCoq Quote Definition foo := (forall (H : nat) (H0 : ilist H) (H1 : nat) (H2 : ilist H1),
     app H H0 H1 H2 =
     match H0 in (ilist n1) return (ilist (n1 + H1)) with
     | Nil => H2
     | Cons n x ls1' => Cons (n + H1) x (app n ls1' H1 H2)
     end).

MetaCoq Quote Definition foo1 := (forall (H : nat) (H0 : ilist H) (H1 : nat) (H2 : ilist H1),
     app 0 Nil H1 H2 = H2). (* on substitue les indices dans la variable sur laquelle on matche 
dans le corps de la fonction? *)


Definition foo2 := (forall (n : nat) (x : A) (ls1' : ilist n) (H1 : nat) (H2 : ilist H1),
     app _ (Cons n x ls1') H1 H2 = Cons (n + H1) x (app n ls1' H1 H2)).

MetaCoq Quote Definition foo2_reif:= 
(forall (n : nat) (x : A) (ls1' : ilist n) (H1 : nat) (H2 : ilist H1),
     app _ (Cons n x ls1') H1 H2 = Cons (n + H1) x (app n ls1' H1 H2)).

Print foo2.

Print foo.
Print foo2.

Goal False.
get_def app.
expand_hyp app_def.
eliminate_fix_hyp H.
eliminate_pattern_matching_test H0.
assert (test1 : forall (H : nat) (H0 : ilist H) (H1 : nat) (H2 : ilist H1),
     app 0 Nil H1 H2 = H2) by (intros ; reflexivity).

Fail eliminate_pattern_matching H0.
unquote_term (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
           inductive_ind := 0 |} [])
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tVar "A"%string)
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
              (tApp
                 (tInd
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} []) [tRel 1])
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tInd
                    {|
                    inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                      "nat"%string);
                    inductive_ind := 0 |} [])
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string; "Sniper"%string],
                                            "ilist"%string);
                          inductive_ind := 0 |} []) [tRel 0])
                    (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                                            "eq"%string);
                          inductive_ind := 0 |} [])
                       [tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string; "Sniper"%string],
                                               "ilist"%string);
                             inductive_ind := 0 |} [])
                          [tApp
                             (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                                []) [tRel 4; tRel 1]];
                       tApp
                         (tConst
                            (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                            "app"%string) [])
                         [tRel 4;
                         tApp
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (MPfile
                                                      ["dependent_pattern_matching"%string;
                                                      "Sniper"%string], "ilist"%string);
                                 inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2]; 
                         tRel 1; tRel 0];
                       tCase
                         ({|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string; "Sniper"%string],
                                            "ilist"%string);
                          inductive_ind := 0 |}, 0, Relevant)
                         (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                 "nat"%string);
                               inductive_ind := 0 |} [])
                            (tLambda
                               {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} []) [tRel 0])
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} [])
                                  [tApp
                                     (tConst
                                        (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                        "add"%string) []) [tRel 2; tRel 3]])))
                         (tApp
                            (tApp
                               (tConstruct
                                  {|
                                  inductive_mind := (MPfile
                                                       ["dependent_pattern_matching"%string;
                                                       "Sniper"%string], "ilist"%string);
                                  inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2])
                         [(0, tRel 0);
                         (3,
                         tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
                           (tInd
                              {|
                              inductive_mind := (MPfile
                                                   ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                "nat"%string);
                              inductive_ind := 0 |} [])
                           (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                              (tVar "A"%string)
                              (tLambda
                                 {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} []) [tRel 1])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp
                                       (tConst
                                          (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                          "add"%string) []) [tRel 2; tRel 4]; 
                                    tRel 1;
                                    tApp
                                      (tConst
                                         (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "app"%string) []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]])))))).


Print app_reif.
Abort.

End ilist.















