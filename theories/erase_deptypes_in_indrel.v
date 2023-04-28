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

Inductive ExampleR1 : (bool*bool) -> forall (a : Type), Example a -> a -> Prop :=
| ExampleR1C1 (d : bool) (ω : bool*bool) (x : bool) (equ : true = x)
  : ExampleR1 ω bool (ToBool d) x
| ExampleR1C2 (d : bool) (ω : bool*bool) (x : unit)
  : ExampleR1 ω unit (ToUnit d) x.

Inductive ExampleR2 : (bool*bool) -> forall (a : Type), Example a -> Prop :=
| ExampleR2C1 (d : bool) (ω : bool*bool)
  : ExampleR2 ω bool (ToBool d)
| ExampleR2C2 (d : bool) (ω : bool*bool) (H : ω.1 = false -> ω.2 = false)
  : ExampleR2 ω unit (ToUnit d).

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

Fixpoint unliftn t n := 
  match n with
    | 0 => t 
    | S n => unliftn (unlift1 t) n
  end.

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
  (match opt with
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
   end, e).

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
      res <- tmEval all mind_transfo.1 ;;
      curmodpath <- tmCurrentModPath tt ;;
      let R' := tInd {| inductive_mind := (curmodpath, fresh); inductive_ind := 0 |} [] in 
    (* empty instances of universe because no universe polymorphism and no mutuals so number 0 *)
      tmMkInductive true res ;;
      tmReturn (R', mind_transfo.2)
  end.

Definition erase_dep_transform_pred (l : list term) (R : term) :=
  res <- erase_type_in_indexes l ;;
  l <- tmEval all (List.combine res.1 res.2) ;;
  l' <- tmEval all ((List.map (fun x => (x.1, x.2.1))) l) ;;
  let indus := res.2 in
  p <- erase_deptypes_in_indrel indus R ;; 
  tmReturn (l', p.1, p.2). 

Fixpoint get_kernames (l : list (term*term)) :=
  match l with
    | (tInd {| inductive_mind := kn ; inductive_ind := 0 |} inst, 
      tInd {| inductive_mind := kn' ; inductive_ind := 0 |} inst') :: xs => (kn, kn') :: get_kernames xs
    | _ :: xs => get_kernames xs
    | [] => []
  end.

Definition erase_dep 
(lind : list term) (* the inductives we want to transform *)
(lindtransfo : list (term*term*term)) (* the inductives already transformed, their transformed counterpart 
and the transformation between them *)
(R: term) (* the relation mentioning the inductives *) :=
  let lkn1 :=  (get_kernames (List.map (fun x => x.1) lindtransfo)) in
  let lkn2 := List.map (fun x => x.1) lkn1 in
  let ltransfos := (List.map (fun x => x.2) lindtransfo) in 
  let lkn_transfos := List.combine ltransfos lkn2 in 
  res <- erase_type_in_indexes lind ;; 
  lcomb <- tmEval all (List.combine res.1 res.2) ;; 
  linduscreated <- tmEval all ((List.map (fun x => (x.1, x.2.1))) lcomb) ;;
  let indus := res.2 in 
  p <- erase_deptypes_in_indrel (indus++lkn1) R ;;
  tmReturn (linduscreated++lkn_transfos, p.1, p.2).
  

(** Statements ** : 
  - if elems = [] then there is only one statement to prove : 
  => forall Pis Xis Ais (tis : Iis Ais), 
      R Pis Xis Tys tis <-> R' Pis Xis (transfos tis) **)

Fixpoint find_term_assoc (n : nat) (l : list (nat*term)) :=
  match l with
  | (m, t) :: xs => if Nat.eqb n m then Some t else find_term_assoc n xs 
  | [] => None
end.

Definition R_app_to_R'_app 
(t : term) 
(R' : term)
(db_args_transformed : list (nat*term)) (* the list of de Brujin indexes which represents 
variables of a type which is a transformed inductive, and the corresponding transformation 
(applied to parameters) *)
(nb_argspars : nat) (*nparameters + narguments *)
(nb_tys : nat)
:=
  match t with
    | tApp (tInd indu inst) l => 
        tApp R' ((List.firstn nb_argspars l)++(List.map 
        (fun x => match x with
          | tRel n => match find_term_assoc n db_args_transformed with
              | Some transfo => tApp transfo [tRel n]
              | None => tRel n
              end
          | _ => x
          end) (List.skipn (nb_argspars+nb_tys) l)))
    | _ => t 
  end.

Fixpoint lookup_kername_term 
  (kn : kername) (l : list (term*kername)) :=
    match l with
      | [] => default_reif
      | (trm ,kn') :: xs => 
          if eq_kername kn kn' then trm else lookup_kername_term kn xs
    end.

Definition is_db_index (t : term) (n : nat) :=
  match t with
    | tRel k => Nat.eqb n k 
    | _ => false
  end.

(* in l, we get only the terms which are parameters *)
Definition filter_params (pars : list (aname*term*nat)) (l : list term) :=
List.filter (fun x => let fix aux pars x :=
                      match pars with
                        | [] => false
                        | (Na, Ty, n) :: xs => orb (is_db_index x n) (aux xs x)
                      end in aux pars x) l.

(* the term constructed is 
R Pars args tys @(indus, argsindus++tysindus) 
we look for @(indus, argsindus) because 
the transformation functions should be applied to their arguments *)

Definition find_db_args_transformed 
(e : env) (env_transfo : list (term*kername)) :=
let indus := env_inductives e in
let pars := (env_parameters e) in
let tys := (env_types e) in
let fix aux e env_transfo indus :=
  match indus with
    | (Na, x, db) :: xs => 
      match x with
        | tApp (tInd {| inductive_mind := kn ;
            inductive_ind := n |} inst) l => 
              let l' := filter_params (pars++tys) l in
              let transfo_app := tApp (lookup_kername_term kn env_transfo) l'
                in (db, transfo_app) :: aux e env_transfo xs
        | _ => (0, tVar "error during use of "%bs) :: aux e env_transfo xs
        end
    | [] => []
    end
in aux e env_transfo indus. 

(* The easy statement whenever there is no arguments of indexed types *)
Definition statement_elems_empty 
(env_transfo : list (term*kername)) (* the transformation associated to the inductive it transforms *) 
(e : env) 
(R : term) (* the relation R *)
(R' : term) (* the relation R' *)
:=
  let lpars := Datatypes.length (env_parameters e) in
  let largs := Datatypes.length (env_arguments e) in
  let ltypes := Datatypes.length (env_types e) in
  let linds := Datatypes.length (env_inductives e) in
  let R_app := tApp R (Rel_list (lpars+largs+ltypes+linds) 0) in
  let db_args_transformed := find_db_args_transformed e env_transfo in
  let R'_app := R_app_to_R'_app R_app R' db_args_transformed (lpars+largs) ltypes in
  mkProdsNamed (tApp <% iff %> [R_app; R'_app]) ((env_parameters e)++
(List.map (fun x => (x.1.1, unlift1 x.1.2, x.2)) (env_arguments e))++(env_types e)++
(mapi (fun i x => (x.1.1, unliftn x.1.2 (S i), x.2)) (env_inductives e))). (* unlift 1 because the type supposed that the variable
have been already introduced *)

Notation tmWait := (tmReturn tt%bs).

Definition erase_ty_erase_dep (l : list term) (R : term)
:= p <- erase_dep_transform_pred l R ;; 
  b <- tmEval all p.2 ;;
  if is_empty (env_elements b) then
  tmBind (
  statement <- tmEval all (statement_elems_empty p.1.1 p.2 R p.1.2) ;; 
  tmUnquoteTyped Prop statement) (fun st_unq : Prop =>
  fresh <- tmFreshName "equivalence"%bs ;;
  lem <- tmLemma fresh st_unq;; tmWait) else tmWait.

Require Import Coq.Program.Equality.

Ltac solve_implr :=
let H1 := fresh in
intro H1 ; induction H1 ; constructor ; repeat assumption.

Ltac has_arg_in_type x :=
  let T := type of x in match T with
    | ?u ?v => let T' := type of v in first [constr_eq T' Type | constr_eq T' Set]
    | _ => fail
  end. 

Goal False. assert (x: trm nat). exact (N 0). has_arg_in_type x. Abort.

Ltac solve_impll := 
  let H1 := fresh in
  intro H1 ; dependent induction H1 ; 
  repeat match goal with
  | x : _ |- _ => has_arg_in_type x ; try (destruct x)
  end ; 
  let Hyps := hyps in
  let rec aux Hyps := lazymatch Hyps with
    | (?x, ?y) => aux x ; aux y
    | ?z => try (inversion z)
    end in aux Hyps; subst; try (constructor; repeat assumption);
   let Hyps := hyps in 
  let rec aux Hyps := lazymatch Hyps with
    | (?x, ?y) => aux x ; aux y
    | ?z => try (apply z)
    end in aux Hyps; try (constructor; repeat assumption).

Obligation Tactic := first [intros; split ; [solve_implr | solve_impll] | idtac].

MetaCoq Run (erase_ty_erase_dep [<%Example%>] <%ExampleR1%>).
  
MetaCoq Run (erase_ty_erase_dep [<%trm%>] <%trm_le%>).
 
MetaCoq Run (erase_dep [] [(<%Example%>, <%Example'%>, <%transfo%>)]  <% ExampleR2 %>).

MetaCoq Run (erase_ty_erase_dep [<%bank_operation%>] <% bank_operation_correct %>).
  

