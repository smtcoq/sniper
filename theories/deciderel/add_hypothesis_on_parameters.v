From MetaCoq.Template Require Import All.
From SMTCoq Require Import SMTCoq.
Require Import String.
Require Import List. 
Import ListNotations.
Unset MetaCoq Strict Unquote Universe Mode.

Section utilities.

Definition mkProdName na T u :=
tProd {| binder_name := nNamed na ; binder_relevance := Relevant |} T u.

Inductive impossible_term :=.
MetaCoq Quote Definition impossible_term_reif := impossible_term.

End utilities.

Section trm.

Variable trm : term.
Definition term_rel0 := 
tApp trm [tRel 0].

(* As the source is the type A1 -> ... -> An 
and the target has type A1 -> foo A1 -> A2 -> foo A2 ... -> An -> foo An, 
we need to lift the first variable n times, the second variable n-1 times and so on *)
Fixpoint liftn_aux (n n' : nat) (t : term) :=
match n with
| 0 => t
| S m => lift 1 n' (liftn_aux m (S n') t)
end.

Definition liftn (n : nat) (t : term) := liftn_aux n 0 t.

Fixpoint add_trm_parameter_aux (t : term) (n : nat) (lrel : list term) (fuel : nat) : term :=
let len := Datatypes.length lrel in
match fuel with
| 0 => impossible_term_reif
| S m => 
match t with
| tProd Na u v => let u' := match u with
      | tApp (tRel k) l => if Nat.eqb n k then tApp (tRel (k+ len)) (List.map (lift len 0) (List.firstn len l) ++ lrel ++ 
(List.map (lift len (n - 1)) (List.skipn len l))) else (liftn_aux len (n - len) u)
      | _ => (liftn_aux len (n - len) u)
 end in
tProd Na u' (add_trm_parameter_aux v (S n) 
(List.map (lift 1 0) lrel) m)
| tApp u l => match u with
        | tRel k => if Nat.eqb n k then tApp (tRel (k+ len)) (List.map (lift len 0) (List.firstn len l) ++ lrel ++ 
(List.map (lift len (n - 1)) (List.skipn len l)))
else tApp u l
        | _ => lift len 0 t
end
| _ => lift len 0 t
      end
end.

(* Auxiliary functions to find a new suitable name *)
Definition find_name_trm : ident :=
match trm with
| tInd i _ => ("H"++(i.(inductive_mind)).2)%bs
| tConst k _ => k.2
| _ => "new_ident"%bs
end.

Definition trm_aname (na : aname) :=
let new_name :=
match na.(binder_name) with 
| nNamed id => nNamed (find_name_trm++id)%bs
| nAnon => nNamed find_name_trm
end in
{| binder_name := new_name; binder_relevance := na.(binder_relevance) |}.

Fixpoint add_trm_for_each_poly_var (t: term) (acc: list term) (fuel : nat) : term :=
match t with
| tProd Na u v => match u with
      | tSort s => if negb (Universe.is_prop s) then 
                   let acc' := (List.map (lift 1 0) acc) ++ [tRel 0] in
                   tProd Na (tSort s) (mkProdName (find_name_trm) (term_rel0) (add_trm_for_each_poly_var v acc' fuel))
else let len := Datatypes.length acc in (add_trm_parameter_aux t len acc fuel)
      | _ => let len := Datatypes.length acc in add_trm_parameter_aux t len acc fuel
      end
| _ => let len := Datatypes.length acc in add_trm_parameter_aux t len acc fuel
end. 
  
Fixpoint fuel_trm t  := match t with
| tProd _ u v => fuel_trm u + fuel_trm v + 1
| _ => 1
end.

Definition add_trm_parameter (t : term) :=
let fuel := fuel_trm t in add_trm_for_each_poly_var t [] fuel.

End trm.

(* Section tests_CompDec.


MetaCoq Quote Recursively Definition Add_reif_rec := Add.

MetaCoq Quote Definition CompDec_reif := @CompDec.

Inductive Add (A: Type) (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add A a l (a::l)
    | Add_cons x l l' : Add A a l l' -> Add A a (x::l) (x::l').

Inductive Add_compdec (A : Type) (HA : CompDec A) (a: A) : list A -> list A -> Prop :=
    | Add_head_comp l : Add_compdec A HA a l (a::l)
    | Add_cons_comp x l l' : Add_compdec A HA a l l' -> Add_compdec A HA a (x::l) (x::l').


Definition test :=  tProd {| binder_name := nNamed "A"%bs; binder_relevance := Relevant |}
                (tSort (Universe.of_levels (inr (Level.Level "compdecs_poly_ind.164"%bs))))
                (tProd {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |}
                   (tRel 0)
                   (tProd {| binder_name := nNamed "l"%bs; binder_relevance := Relevant |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                "list"%bs);
                              inductive_ind := 0
                            |} []) [tRel 1])
                      (tApp (tRel 3)
                         [tRel 2; tRel 1; tRel 0;
                         tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                  "list"%bs);
                                inductive_ind := 0
                              |} 1 []) [tRel 2; tRel 1; tRel 0]]))).

MetaCoq Quote Definition nat_reif := nat.

Definition ty_Add_cons := tProd {| binder_name := nNamed "A"%bs; binder_relevance := Relevant |}
                       (tSort (Universe.of_levels (inr (Level.Level "compdecs_poly_ind.201"%bs))))
                       (tProd {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |} 
                          (tRel 0)
                          (tProd {| binder_name := nNamed "x"%bs; binder_relevance := Relevant |}
                             (tRel 1)
                             (tProd {| binder_name := nNamed "l"%bs; binder_relevance := Relevant |}
                                (tApp
                                   (tInd
                                      {|
                                        inductive_mind :=
                                          (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs);
                                        inductive_ind := 0
                                      |} []) [tRel 2])
                                (tProd
                                   {| binder_name := nNamed "l'"%bs; binder_relevance := Relevant |}
                                   (tApp
                                      (tInd
                                         {|
                                           inductive_mind :=
                                             (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "list"%bs);
                                           inductive_ind := 0
                                         |} []) [tRel 3])
                                   (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                      (tApp (tRel 5) [tRel 4; tRel 3; tRel 1; tRel 0])
                                      (tApp (tRel 6)
                                         [tRel 5; tRel 4;
                                         tApp
                                           (tConstruct
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                                  "list"%bs);
                                                inductive_ind := 0
                                              |} 1 []) [tRel 5; tRel 3; tRel 2];
                                         tApp
                                           (tConstruct
                                              {|
                                                inductive_mind :=
                                                  (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                                  "list"%bs);
                                                inductive_ind := 0
                                              |} 1 []) [tRel 5; tRel 3; tRel 1]])))))).
MetaCoq Quote Definition Add_compdec_reif := Add_compdec.

Inductive test_indu_inst (a : nat) : list nat -> list nat -> Prop :=
| c0 : forall l l', test_indu_inst a l l'.

MetaCoq Quote Definition test_indu_inst_reif := test_indu_inst.

MetaCoq Unquote Definition test1 := (subst10 test_indu_inst_reif (add_trm_parameter CompDec_reif <% forall a l l', test_indu_inst a l l' %>)).
(* test1 has not changed as expected *) 

MetaCoq Unquote Definition ty_Add_cons_test := (subst10 Add_compdec_reif (add_trm_parameter CompDec_reif ty_Add_cons )).
Print ty_Add_cons_test.
Inductive prod_compdec (A : Type) (HA : CompDec A) (B : Type) (HB : CompDec B) :=
| pair_compdec : A -> B -> prod_compdec A HA B HB.

MetaCoq Quote Recursively Definition prod_compdec_reif := prod_compdec.

MetaCoq Quote Recursively Definition prod_reif := prod.

Definition ty_prod_reif := tProd
                {|
                  binder_name := nNamed "A"%bs;
                  binder_relevance := Relevant
                |}
                (tSort
                   (Universe.of_levels
                      (inr (Level.Level "Coq.Init.Datatypes.22"%bs))))
                (tProd
                   {|
                     binder_name := nNamed "B"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (Universe.of_levels
                         (inr
                            (Level.Level "Coq.Init.Datatypes.23"%bs))))
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
                         (tApp (tRel 4) [tRel 3; tRel 2])))).

MetaCoq Unquote Definition test_ty_prod :=  (subst10 prod_compdec_reif.2 (add_trm_parameter CompDec_reif ty_prod_reif)).

Compute (subst10 Add_compdec_reif (add_trm_parameter test CompDec_reif)).

MetaCoq Quote Definition goal := (forall A HA a  l, Add_compdec A HA a l (a::l)).

Inductive test_two_params (A B : Type) :=
| test0 : test_two_params A B.

Inductive test_two_params_compdec (A : Type) (HA : CompDec A) (B : Type) (HB : CompDec B) :=
|test0compdec : test_two_params_compdec A HA B HB.

MetaCoq Quote Recursively Definition test_two_params_reif := test_two_params.
MetaCoq Quote Recursively Definition test_two_params_compdec_reif := test_two_params_compdec.

Definition ty_test0_reif := tProd {| binder_name := nNamed "A"%bs; binder_relevance := Relevant |}
                (tSort (Universe.of_levels (inr (Level.Level "compdecs_poly_ind.218"%bs))))
                (tProd {| binder_name := nNamed "B"%bs; binder_relevance := Relevant |}
                   (tSort (Universe.of_levels (inr (Level.Level "compdecs_poly_ind.219"%bs))))
                   (tApp (tRel 2) [tRel 1; tRel 0])).

MetaCoq Quote Definition goal2 := (forall A HA B HB, test_two_params_compdec A HA B HB).

MetaCoq Unquote Definition test_two_params_comp := (subst10 test_two_params_compdec_reif.2 (add_trm_parameter CompDec_reif ty_test0_reif )).
MetaCoq Unquote Definition test3 := (subst10 Add_compdec_reif (add_trm_parameter CompDec_reif test)).

End tests_CompDec. *)
