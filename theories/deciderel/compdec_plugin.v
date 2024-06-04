From MetaCoq.Template Require Import All.
From SMTCoq Require Import SMTCoq.
Import MCMonadNotation.
Require Import add_hypothesis_on_parameters.
Require Import utilities.
Require Import Lia.

Declare Scope string_scope2.
Notation "s1 ^ s2" := (bytestring.String.append s1 s2) : string_scope2.

Open Scope string_scope2.

(** This file transforms an inductive with prenex polymorphic parameters A1, ..., An
into a new one with supplementary hypothesis (HA1 : CompDec A1), ..., (HAn : CompDec An) 
taken as parameters *)

Unset MetaCoq Strict Unquote Universe Mode.

MetaCoq Quote Definition CompDec_reif := CompDec.

MetaCoq Quote Definition Prop_reif := Prop.

Section utilities.

Fixpoint Inb_term (x : term) (l : list term) :=
  match l with
    | [] => false
    | y :: ys => if eqb_term x y then true else Inb_term x ys
  end.

Definition get_list_of_rel (n : nat) := 
(* generates the list [tRel 2*n; tRel 2*n-2; ... ; tRel 0] *)
  let fix aux n n' acc :=
  match n with
    | 0 => acc
    | S n => aux n (n'-2) ((tRel n') :: acc)
  end in aux n (2*n-1)%nat [].

Fixpoint append_nodup_term (l1 l2 : list term) :=
  match l1 with
    | [] => l2
    | x :: xs => 
        if Inb_term x l2 then append_nodup_term xs l2 
        else x :: append_nodup_term xs l2
end.

(* append of a list of pair of a term and a list of term with no duplicates
for the first argument
In our case, this means that the parameters for 
the first argument could not be instantiated differently *)

Fixpoint append_nodup_term_list_term  (l1 l2 : list (term*(list term))) :=
  match l1 with
    | [] => l2
    | x :: xs => 
        if Inb_term  x.1 (split l2).1 then append_nodup_term_list_term xs l2 
        else x :: append_nodup_term_list_term xs l2
  end.

End utilities.

Section trm.
Variable trm : term.

Definition ctors_names_compdec (l : list constructor_body) := 
  List.map (fun x => x.(cstr_name)^(find_name_trm trm)) l.

End trm.

Definition dest_app (t : term) : term*list term :=
  match t with
    | tApp u v => (u, v)
    | _ => (t, [])
  end.


(* We look at the terms under a product and we keep the inductives, 
and the named variables *)
Definition find_list_var_and_terms (t : term) : list (term*(list term)) :=
  let fix aux acc t :=
  match t with
    | tProd _ Ty u => let p := dest_app Ty in
        match p.1 with
          | tInd _ _ => aux (p :: acc) u
          | tVar _ => aux (p :: acc) u
          | tConst _ _ => aux acc u
          | _ => aux acc u
        end
    | _ => acc
  end
  in aux [] t.

(* This function compute the new parameters of a new inductive declaration. 
To a parameter A of type Type (and not Prop) will be added a new parameter HA of type
trm A *)
Definition add_trm_params_list_aux (fuel : nat) (l : list context_decl) trm : (list context_decl) * nat := 
  let fix aux l n trm fuel :=
    match fuel with
      | 0 => ([], n)
      | S fuel' =>
          match l with
            | [] => ([], n)
            | x :: xs => 
                match x.(decl_type) with
                  | tSort s => 
                      if negb (is_prop s) then
                        let res := aux (List.map (fun x => let ty' := lift 1 0 x.(decl_type) in
                          {| decl_name := x.(decl_name) ; decl_body := x.(decl_body); decl_type := ty' |}) xs) (S n) trm fuel' in
                        let new_name := trm_aname trm x.(decl_name) in
                          (x :: (({| decl_name := new_name ; decl_body := None ; decl_type := P_app trm |})) :: res.1, res.2)
                      else 
                        let res := aux xs n trm fuel' in (x :: res.1, res.2)
                  | _ => let res := aux xs n trm fuel' in (x :: res.1, res.2)
                end
          end
    end
in aux l 0 trm fuel.

(* Same function with some fuel computed *)

Definition add_trm_params_list (l : list context_decl) trm := 
  let p := add_trm_params_list_aux (S (Datatypes.length l)) (rev l) trm in
  (rev p.1, p.2).

Fixpoint skipn_forall (t : term) (n : nat) : term := 
  match t, n with
    | tProd Na u v, S n => skipn_forall v n 
    | _, _ => t
  end.

Definition find_arity (t : term) (n : nat) trm : term :=
skipn_forall (add_trm_parameter trm t) n. 

(* Analyses the types of the constructors of an inductive in order to find
whose types should verify the property CompDec *)

Definition ctors_types_compdecs (l : list constructor_body) n trm lpars := 
  (List.map (fun x =>
    match lpars with
      | x' :: xs => subst lpars 1 x.(cstr_type)
      | [] => let ty:= x.(cstr_type) in skipn_forall (add_trm_parameter trm ty) n 
    end) l,
    match lpars with
      | x' :: xs => 
          List.fold_left (fun x y => let ty:= (subst lpars 0 (skipn_forall (y.(cstr_type)) (Datatypes.length lpars))) in 
          append_nodup_term_list_term (find_list_var_and_terms ty) x)
      | [] => 
          List.fold_left (fun x y => let ty:= y.(cstr_type) in append_nodup_term_list_term (find_list_var_and_terms ty) x)
    end l []).

(* Definition mk_oind_entry_compdec 
  (oind : one_inductive_body) 
  (n : nat)
  (trm : term)
  (idt : string) 
  (lpars : list term) : 
  one_inductive_entry * (list (term*(list term))):=
    let res := ctors_types_compdecs oind.(ind_ctors) n trm [] in
    let new_type := 
        match lpars with
          | [] => (* if l is empty then the inductive is applied to no parameters *)
              add_trm_parameter trm oind.(ind_type)
          | _ :: _ => 
              tApp (add_trm_parameter trm oind.(ind_type)) lpars
        end in
    let arity := find_arity oind.(ind_type) n trm in
      ({| mind_entry_typename := (oind.(ind_name)^"CompDec"^idt);
          mind_entry_arity := arity;
          mind_entry_consnames := ctors_names_compdec trm oind.(ind_ctors);
          mind_entry_lc := res.1
           |}, res.2). *)

Definition mk_oind_entry_compdec   (oind : one_inductive_body) n (trm : term)  (idt : string) (lpars : list term)  : 
one_inductive_entry * (list (term* (list term))):=
match lpars with 
| [] => (* if l is empty then the inductive is applied to no parameters *)
let res := ctors_types_compdecs   oind.(ind_ctors) n trm [] in
let new_type := add_trm_parameter trm oind.(ind_type) in
let arity := find_arity oind.(ind_type) n trm in
({| mind_entry_typename := (oind.(ind_name)^"CompDec"^idt);
   mind_entry_arity := arity;
   mind_entry_consnames := ctors_names_compdec trm oind.(ind_ctors);
   mind_entry_lc := res.1
|}, res.2)
| _ :: _ => 
let res := ctors_types_compdecs   oind.(ind_ctors) n trm lpars in
let new_type := tApp (add_trm_parameter trm oind.(ind_type)) lpars in
let arity := find_arity oind.(ind_type) n trm in
({| mind_entry_typename := (oind.(ind_name)^"CompDec"^idt);
   mind_entry_arity := arity;
   mind_entry_consnames := ctors_names_compdec trm oind.(ind_ctors);
   mind_entry_lc := res.1
|}, res.2)
end. 

Definition mk_oind_entry_compdec_list 
  (loind: list one_inductive_body) 
  n 
  trm 
  (idt : string) 
  (lpars : list term) : (list one_inductive_entry)*(list (term*(list term))) :=
    let fix aux loind acc1 acc2 n :=
    match loind with
      | x :: xs => let res := mk_oind_entry_compdec x n trm idt lpars in 
         aux xs (res.1 :: acc1) (append_nodup_term_list_term   res.2 acc2) n
      | [] => (acc1, acc2)
    end in aux loind [] [] n.

Definition mk_mind_entry_compdec (mind : mutual_inductive_body) trm (idt : string) (lpars : list term)
: mutual_inductive_entry*(list (term*(list term))) := 
let n := mind.(ind_npars) in
let params := add_trm_params_list mind.(ind_params) trm in
let params1 := params.1 in
let npars := params.2 + n in
let res := mk_oind_entry_compdec_list mind.(ind_bodies) npars trm idt lpars in
({|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := params1;
  mind_entry_inds := res.1;
  mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}, res.2).

Program Fixpoint gen_compdec_statement_aux (t : term) (l: list term) {measure (length l)} : term :=
match l with
| [] => t
| x :: xs =>
tProd {| binder_name := nAnon ; binder_relevance := Relevant |} (tSort (sType fresh_universe))
(tProd {| binder_name := nAnon ; binder_relevance := Relevant |} (tApp CompDec_reif [tRel 0]) 
 (gen_compdec_statement_aux (lift 1 0 t) (List.map (lift 1 0) xs) ))
end.
Next Obligation.
induction xs; simpl in *; auto.
unfold "<" in *.
assert (H : S #|map (lift0 1) xs| <= S #|xs|).
apply IHxs. intros. exact a.
inversion H. lia. lia. Qed.
Next Obligation.
unfold Wf.MR. destruct a as [ t l].
induction l. apply Acc_intro. intros ; simpl in *.
inversion H. apply Acc_intro. intros y H.
assert (H1 : #|y.π2|= #|l| \/  #|y.π2| < #|l|).
induction y; simpl in *; lia.
destruct H1 as [H2 | H3]; simpl in *.
- assert (H1 : forall t t' l l', Acc (fun x y : ∑ _ : term, list term => #|x.π2| < #|y.π2|) (t; l)
-> #|l| = #|l'| -> Acc (fun x y : ∑ _ : term, list term => #|x.π2| < #|y.π2|) (t'; l')).
intros t1 t2 l1 l2 H0 H0'.
inversion H0. simpl in *.
rewrite H0' in H1. apply Acc_intro. assumption.
destruct y as [a'  y].
apply H1 with (t' := a') (l' := y) in IHl.
apply IHl. symmetry in H2. simpl in H2. apply H2. 
- apply IHl. simpl. assumption. Qed.

Fixpoint gen_compdec_statement_aux2 (t : term) (l: list term) (fuel : nat) : term :=
match fuel with
| 0 => t
| S fuel' => 
match l with
| [] => t
| x :: xs =>
tProd {| binder_name := nAnon ; binder_relevance := Relevant |} (tSort (sType fresh_universe)) 
(tProd {| binder_name := nAnon ; binder_relevance := Relevant |} (tApp CompDec_reif [tRel 0]) 
 (gen_compdec_statement_aux2 t (List.map (lift 1 0) xs) fuel' ))
end
end.

Fixpoint contains_trel (l : list term) :=
match l with
| [] => false
| x :: xs => match x with
    | tRel _ => true
    | _ => contains_trel xs
    end
end.

(* warning: handles three cases only
- the term is not an application (t, []), the statement produced is CompDec t 
- the term is an application which contains variables then 
the statement produced is forall p in params t, CompDec p1 -> ... CompDec pn -> CompDec (t p1 ... pn)
- the term is an application (t, v), the statement produced is CompDec (t v)

this function returns the term of type compdec t and the number of parameters to be instantiated *)

Definition gen_compdec (p : term*(list term)) :=
match p with
| (t, x::xs) => if contains_trel (x::xs) then let n := Datatypes.length (x::xs) in
              let l := (get_list_of_rel n) in (gen_compdec_statement_aux2 (tApp CompDec_reif [tApp t l]) l (S (S n)), n)
              else (tApp CompDec_reif [tApp t (x::xs)], 0)
| (t, []) => (tApp CompDec_reif [t], 0) 
end.

(* we should trigger the transformation only if the inductive 
contains prenex polymorphism : we take the list of parameters 
The head of the list of parameters should be of type Type *) 

Definition contains_prenex_poly (l : list context_decl) :=
match l with
| [] => false
| x :: xs => match x.(decl_type) with
    | tSort s => if negb (is_prop s) then true else false
    | _ => false
    end
end. 

Definition contains_prenex_poly_mind (m : mutual_inductive_body) :=
let lpars := ind_params m in contains_prenex_poly (rev lpars). 

Section commands. 

(* Definition add_compdec_inductive (p : program*term)
  : TemplateMonad unit
  := match p.2 with
     | tInd ind0 _ => let   := (trans_global_env p.1.1) in
       decl <- tmQuoteInductive (inductive_mind ind0) ;; 
       fresh_ident <- match (ind_bodies decl) with
              | x :: xs => let x_name := ind_name x in tmFreshName x_name
              | [] => tmFreshName "empty_indu"
              end ;;
       if contains_prenex_poly_mind decl then 
       let ind' := (mk_mind_entry_compdec   decl CompDec_reif fresh_ident []) in
       tmMkInductive true ind'.1 
       else tmMsg "" (* does nothing if the inductive has not prenex polymorphism *)
     | _ => tmPrint p.2 ;; tmFail " is not an inductive"
     end.
 *)

(* Takes a list l of reified terms and for each t in l asserts and 
tries to prove CompDec (unquote t), this can be left as a goal to the user *) 
Fixpoint find_compdecs (l : list (term*(list term))) (acc: list (term*term*nat)) :=
match l with
| [] => tmReturn acc
| x :: xs => 
let res := gen_compdec x in
tmBind ( 
res' <- tmEval all res.1 ;; 
tmUnquoteTyped Type res') (fun unquot : Type =>
fresh <- tmFreshName ("compdec_hyp"%bs) ;; 
u <- tmLemma fresh unquot ;;
v <- tmQuote u ;;
res0' <- tmEval all res.2 ;;
x' <- tmEval all x.1 ;; 
npars <- tmEval all x.2 ;;
find_compdecs xs ((v, x', res0') :: acc))
end. 

Definition add_compdec_inductive_and_pose_compdecs_lemmas (t : term)  
  := match t with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;; 
       fresh_ident <- match (ind_bodies decl) with
              | x :: xs => let x_name := ind_name x in tmFreshName x_name
              | [] => tmFreshName "empty_indu"%bs
              end ;;
       let ind' := (mk_mind_entry_compdec decl CompDec_reif fresh_ident []) in
       res <- tmEval all ind'.2 ;; 
       res2 <- find_compdecs (ind'.2) [] ;;
     if contains_prenex_poly_mind decl then
       tmMkInductive true ind'.1 ;; tmReturn res2
       else tmReturn res2
     | tApp (tInd ind0 _) u =>
       (* inductive applied case, we do not consider partials applications *) 
       decl <- tmQuoteInductive (inductive_mind ind0) ;; 
       let ind' := (mk_mind_entry_compdec decl CompDec_reif "no_used"%bs u) in
       res <- tmEval all ind'.2 ;;
       res2 <- find_compdecs res [] ;;
       decl' <- tmEval all (mind_body_to_entry decl) ;;
       tmReturn res2
     | _ => tmFail "not an inductive"%bs
     end.

Definition monadic_compdec_inductive (t : term)
  := match t with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;; 
       fresh_ident <- match (ind_bodies decl) with
              | x :: xs => let x_name := ind_name x in tmFreshName x_name
              | [] => tmFreshName "empty_indu"%bs
              end ;;
       let ind' := (mk_mind_entry_compdec decl CompDec_reif fresh_ident []) in
       res <- tmEval all ind'.2 ;; 
       res2 <- find_compdecs res [] ;; 
       if contains_prenex_poly_mind decl then
       tmMkInductive true ind'.1 ;; tmReturn ((res2, []), ind'.1)
       else 
       decl' <- tmEval all (mind_body_to_entry decl) ;; 
       tmReturn ((res2, []), decl')
     | tApp (tInd ind0 _) u => 
       (* inductive applied case, we do not consider partials applications *) 
       decl <- tmQuoteInductive (inductive_mind ind0) ;; 
       let ind' := (mk_mind_entry_compdec decl CompDec_reif "no_used"%bs u) in
       res <- tmEval all ind'.2 ;; 
       res2 <- find_compdecs res [] ;;
       decl' <- tmEval all (mind_body_to_entry decl) ;;
       tmReturn ((res2, u), decl')
     | _ => tmFail "not an inductive"%bs
     end. 

Definition test_compdec {A : Type} (t: A) :=
t' <- tmQuote t ;;
res <- add_compdec_inductive_and_pose_compdecs_lemmas t' ;;
tmPrint res.

End commands.

(*
Require Import ZArith.
Section tests.

Inductive elt_list :=
 |Nil : elt_list
 |Cons : Z -> Z -> elt_list -> elt_list.

Inductive Inv_elt_list : Z -> elt_list -> Prop :=
 | invNil  : forall b, Inv_elt_list b Nil
 | invCons : forall (a b  j: Z) (q : elt_list),
     (j <= a)%Z -> (a <= b)%Z ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

MetaCoq Run (test_compdec (Inv_elt_list)). 

MetaCoq Run (test_compdec (@Add Z)). 
MetaCoq Run (test_compdec Add). 
MetaCoq Run (test_compdec nat).
MetaCoq Run (test_compdec prod).

Inductive Ind_test (A B : Type) : A*B -> Prop :=
| Ind1 : forall (x : A*B), Ind_test A B x.

MetaCoq Run (test_compdec Ind_test).
MetaCoq Run (tmQuote (@Add nat) >>= monadic_compdec_inductive). 

End tests.
 *)