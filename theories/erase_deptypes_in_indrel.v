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

Print doc_rec.
Compute (mind_body_to_entry {|
          ind_finite := Finite;
          ind_npars := 0;
          ind_params := [];
          ind_bodies :=
            [{|
               ind_name := "doors_o_callee"%bs;
               ind_indices :=
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
                   decl_type :=
                     tApp
                       (tInd
                          {|
                            inductive_mind :=
                              (MPfile
                                 ["erase_type_in_indexes"%bs;
                                 "theories"%bs;
                                 "Sniper"%bs],
                              "DOORS"%bs);
                            inductive_ind := 0
                          |} []) [tRel 0]
                 |};
                 {|
                   decl_name :=
                     {|
                       binder_name := nNamed "a"%bs;
                       binder_relevance := Relevant
                     |};
                   decl_body := None;
                   decl_type :=
                     tSort
                       (Universe.of_levels
                          (inr
                             (Level.Level
                                "Sniper.theories.erase_deptypes_in_indrel.15"%bs)))
                 |};
                 {|
                   decl_name :=
                     {|
                       binder_name := nAnon;
                       binder_relevance := Relevant
                     |};
                   decl_body := None;
                   decl_type :=
                     tApp
                       (tInd
                          {|
                            inductive_mind :=
                              (MPfile
                                 ["Datatypes"%bs;
                                 "Init"%bs; "Coq"%bs],
                              "prod"%bs);
                            inductive_ind := 0
                          |} [])
                       [tInd
                          {|
                            inductive_mind :=
                              (MPfile
                                 ["Datatypes"%bs;
                                 "Init"%bs; "Coq"%bs],
                              "bool"%bs);
                            inductive_ind := 0
                          |} [];
                       tInd
                         {|
                           inductive_mind :=
                             (MPfile
                                ["Datatypes"%bs;
                                "Init"%bs; "Coq"%bs],
                             "bool"%bs);
                           inductive_ind := 0
                         |} []]
                 |}];
               ind_sort :=
                 Universe.of_levels
                   (inl PropLevel.lProp);
               ind_type :=
                 tProd
                   {|
                     binder_name := nAnon;
                     binder_relevance := Relevant
                   |}
                   (tApp
                      (tInd
                         {|
                           inductive_mind :=
                             (MPfile
                                ["Datatypes"%bs;
                                "Init"%bs; "Coq"%bs],
                             "prod"%bs);
                           inductive_ind := 0
                         |} [])
                      [tInd
                         {|
                           inductive_mind :=
                             (MPfile
                                ["Datatypes"%bs;
                                "Init"%bs; "Coq"%bs],
                             "bool"%bs);
                           inductive_ind := 0
                         |} [];
                      tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["Datatypes"%bs;
                               "Init"%bs; "Coq"%bs],
                            "bool"%bs);
                          inductive_ind := 0
                        |} []])
                   (tProd
                      {|
                        binder_name := nNamed "a"%bs;
                        binder_relevance := Relevant
                      |}
                      (tSort
                         (Universe.of_levels
                            (inr
                               (Level.Level
                                  "Sniper.theories.erase_deptypes_in_indrel.15"%bs))))
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
                                 inductive_ind := 0
                               |} []) [
                            tRel 0])
                         (tProd
                            {|
                              binder_name := nAnon;
                              binder_relevance :=
                                Relevant
                            |} (tRel 1)
                            (tSort
                               (Universe.of_levels
                                  (inl
                                  PropLevel.lProp))))));
               ind_kelim := IntoPropSProp;
               ind_ctors :=
                 [{|
                    cstr_name :=
                      "doors_o_callee_is_open"%bs;
                    cstr_args :=
                      [{|
                         decl_name :=
                           {|
                             binder_name :=
                               nNamed "equ"%bs;
                             binder_relevance :=
                               Relevant
                           |};
                         decl_body := None;
                         decl_type :=
                           tApp
                             (tInd
                                {|
                                  inductive_mind :=
                                  (
                                  MPfile
                                  ["Logic"%bs;
                                  "Init"%bs;
                                  "Coq"%bs], "eq"%bs);
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                 inductive_ind := 0
                               |} 0 []; 
                             tRel 0]
                       |};
                      {|
                        decl_name :=
                          {|
                            binder_name :=
                              nNamed "x"%bs;
                            binder_relevance :=
                              Relevant
                          |};
                        decl_body := None;
                        decl_type :=
                          tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                  ["Datatypes"%bs;
                                  "Init"%bs;
                                  "Coq"%bs],
                                "bool"%bs);
                              inductive_ind := 0
                            |} []
                      |};
                      {|
                        decl_name :=
                          {|
                            binder_name :=
                              nNamed "ω"%bs;
                            binder_relevance :=
                              Relevant
                          |};
                        decl_body := None;
                        decl_type :=
                          tApp
                            (tInd
                               {|
                                 inductive_mind :=
                                  (
                                  MPfile
                                  ["Datatypes"%bs;
                                  "Init"%bs;
                                  "Coq"%bs],
                                  "prod"%bs);
                                 inductive_ind := 0
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
                                 inductive_ind := 0
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
                              |} []]
                      |};
                      {|
                        decl_name :=
                          {|
                            binder_name :=
                              nNamed "d"%bs;
                            binder_relevance :=
                              Relevant
                          |};
                        decl_body := None;
                        decl_type :=
                          tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                  ["erase_type_in_indexes"%bs;
                                  "theories"%bs;
                                  "Sniper"%bs],
                                "door"%bs);
                              inductive_ind := 0
                            |} []
                      |}];
                    cstr_indices :=
                      [tRel 2;
                      tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["Datatypes"%bs;
                               "Init"%bs; "Coq"%bs],
                            "bool"%bs);
                          inductive_ind := 0
                        |} [];
                      tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["erase_type_in_indexes"%bs;
                                  "theories"%bs;
                                  "Sniper"%bs],
                               "DOORS"%bs);
                             inductive_ind := 0
                           |} 0 []) [
                        tRel 3]; tRel 1];
                    cstr_type :=
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                  "bool"%bs);
                                  inductive_ind := 0
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
                                  "Coq"%bs], "eq"%bs);
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
                                  |} 0 []) [
                                  tRel 3]; 
                                  tRel 1]))));
                    cstr_arity := 4
                  |};
                 {|
                   cstr_name :=
                     "doors_o_callee_toggle"%bs;
                   cstr_args :=
                     [{|
                        decl_name :=
                          {|
                            binder_name :=
                              nNamed "x"%bs;
                            binder_relevance :=
                              Relevant
                          |};
                        decl_body := None;
                        decl_type :=
                          tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                  ["Datatypes"%bs;
                                  "Init"%bs;
                                  "Coq"%bs],
                                "unit"%bs);
                              inductive_ind := 0
                            |} []
                      |};
                     {|
                       decl_name :=
                         {|
                           binder_name :=
                             nNamed "ω"%bs;
                           binder_relevance :=
                             Relevant
                         |};
                       decl_body := None;
                       decl_type :=
                         tApp
                           (tInd
                              {|
                                inductive_mind :=
                                  (
                                  MPfile
                                  ["Datatypes"%bs;
                                  "Init"%bs;
                                  "Coq"%bs],
                                  "prod"%bs);
                                inductive_ind := 0
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
                             |} []]
                     |};
                     {|
                       decl_name :=
                         {|
                           binder_name :=
                             nNamed "d"%bs;
                           binder_relevance :=
                             Relevant
                         |};
                       decl_body := None;
                       decl_type :=
                         tInd
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["erase_type_in_indexes"%bs;
                                  "theories"%bs;
                                  "Sniper"%bs],
                               "door"%bs);
                             inductive_ind := 0
                           |} []
                     |}];
                   cstr_indices :=
                     [tRel 1;
                     tInd
                       {|
                         inductive_mind :=
                           (MPfile
                              ["Datatypes"%bs;
                              "Init"%bs; "Coq"%bs],
                           "unit"%bs);
                         inductive_ind := 0
                       |} [];
                     tApp
                       (tConstruct
                          {|
                            inductive_mind :=
                              (MPfile
                                 ["erase_type_in_indexes"%bs;
                                 "theories"%bs;
                                 "Sniper"%bs],
                              "DOORS"%bs);
                            inductive_ind := 0
                          |} 1 []) [
                       tRel 2]; tRel 0];
                   cstr_type :=
                     tProd
                       {|
                         binder_name := nNamed "d"%bs;
                         binder_relevance := Relevant
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
                                |} [])
                             (tApp 
                                (tRel 3)
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
                                  inductive_ind := 0
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
                                  inductive_ind := 0
                                  |} 1 []) [
                                  tRel 2]; 
                                tRel 0])));
                   cstr_arity := 3
                 |}];
               ind_projs := [];
               ind_relevance := Relevant
             |}];
          ind_universes := Monomorphic_ctx;
          ind_variance := None
        |}).

Record env := mk_env 
  { env_parameters : list (aname*term*nat); (* the name of a parameter, its type and its db index *)
    env_argumentss : list (aname*term*nat); (* idem for the arguments of the inductive *)
    env_types : list (aname*term*nat); (* idem for its args of type Type *)
    env_inductives : list (aname*term*nat); (* idem for the inductives arguments *)
    env_elems : list (aname*term*nat); (* idem for the args of the args of type Type *)
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
      (p.1.1, (Na, Ty, 0) :: List.map lift10_term_and_db p.1.2, List.map lift10_term_and_db p.2)
  | _ => (t, [], l)
  end.

Fixpoint get_types (t : term) (p : (list (aname*term*nat))*(list (aname*term*nat))) :=
 match t with
  | tProd Na (tSort s) u => let p0 := get_types u (p.1, p.2) in
      (p0.1.1.1, (Na, tSort s, 0) :: List.map lift10_term_and_db p0.1.1.2, 
       List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
  | tProd Na _ u => (t, [], p.1, p.2)
  | _ => (t, [], p.1, p.2)
  end.

Fixpoint get_indus (t: term) (p : (list (aname*term*nat))*(list (aname*term*nat))*(list (aname*term*nat))) := 
 match t with
  | tProd Na (tInd ind inst) u => let p0 := get_indus u (p.1.1, p.1.2, p.2) in
      (p0.1.1.1.1, (Na, tInd ind inst, 0) :: List.map lift10_term_and_db p0.1.1.1.2, 
       List.map lift10_term_and_db p0.1.1.2, List.map lift10_term_and_db p0.1.2, List.map lift10_term_and_db p0.2)
  | tProd Na _ u => (t, [], p.1.1, p.1.2, p.2)
  | _ => (t, [], p.1.1, p.1.2, p.2)
  end.

Fixpoint get_elems (p : term*(list (aname*term*nat))*(list (aname*term*nat))*
                  (list (aname*term*nat))*(list aname*term*nat)) :=

Definition get_env_aux (e : env) (mind : mutual_inductive_entry) : env :=
  let env_pars := get_parameters mind in
  let opt := get_first_oind_from_mind in
  match opt with
    | None => env
    | Some x => let arity := mind_entry_arity x in
                let p := get_args arity in
                let p0 := get_args p in
                let p1 := get_types p0 in
                let p2 := get_indus p1 in
                let p3 := get_elems p2 in
end.


