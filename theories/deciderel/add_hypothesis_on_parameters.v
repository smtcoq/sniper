From MetaCoq.Template Require Import All.
Require Import String.
Require Import List. 
Import ListNotations.
Require Import utilities.
Unset MetaCoq Strict Unquote Universe Mode.

(** The purpose of this file is to transform an 
inductive of type [A1 -> ... -> An -> B1 -> ... Bm], 
(where the Ais are parameters and the Bjs are indexes)
into a new inductive of type 
[A1 -> P A1 -> ... -> An -> P An -> B1 ... -> Bm].
[P] is a property on types (think of [EqDec], or in the SMTCoq case, 
of [CompDec]) *)

Section P.

Variable P : term.
Definition P_app := 
tApp P [tRel 0].

(* As the source is the type A1 -> ... -> An 
and the target is the type A1 -> P A1 -> A2 -> P A2 ... -> An -> P An, 
we need to lift the first variable n times, the second variable n-1 times and so on *)
Fixpoint liftn_aux (n n' : nat) (t : term) :=
  match n with
    | 0 => t
    | S m => lift 1 n' (liftn_aux m (S n') t)
  end.

Definition liftn (n : nat) (t : term) := liftn_aux n 0 t.

Fixpoint add_trm_parameter_aux 
  (t : term) (* the term considered *)
  (n : nat) (* the db index of the inductive of interest *)
  (lrel : list term) (* the new parameters of the inductive considered (P A1) ... (P An) *)
  (fuel : nat) : term :=
let len := Datatypes.length lrel in
  match fuel with
    | 0 => default_reif
    | S m => 
      match t with
        | tProd Na u v => 
            let u' := match u with
              | tApp (tRel k) l => 
                  if Nat.eqb n k then tApp (tRel (k+ len)) (List.map (lift len 0) (List.firstn len l) ++ lrel ++ 
                      (List.map (lift len (n - 1)) (List.skipn len l))) 
                  else (liftn_aux len (n - len) u)
              | _ => (liftn_aux len (n - len) u)
            end in 
            tProd Na u' (add_trm_parameter_aux v (S n) (List.map (lift 1 0) lrel) m)
    | tApp u l => match u with
                    | tRel k => 
                        if Nat.eqb n k then tApp (tRel (k+ len)) (List.map (lift len 0) (List.firstn len l) ++ lrel ++ 
                            (List.map (lift len (n - 1)) (List.skipn len l)))
                        else tApp u l
                    | _ => lift len 0 t
                  end
    | _ => lift len 0 t
      end
end.

(* Auxiliary functions to find a new suitable name *)
Definition find_name_trm : ident :=
  match P with
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

Definition is_prop (s: sort) :=
  match s with
    | sProp => true
    | _ => false
  end.

Fixpoint add_trm_for_each_poly_var (t: term) (acc: list term) (fuel : nat) : term :=
  match t with
    | tProd Na u v => 
        match u with
          | tSort s => 
              if negb (is_prop s) then 
                let acc' := (List.map (lift 1 0) acc) ++ [tRel 0] in
                tProd Na (tSort s) (mkProdName (find_name_trm) P_app (add_trm_for_each_poly_var v acc' fuel))
              else 
                let len := Datatypes.length acc in (add_trm_parameter_aux t len acc fuel)
          | _ => let len := Datatypes.length acc in add_trm_parameter_aux t len acc fuel
        end
    | _ => let len := Datatypes.length acc in add_trm_parameter_aux t len acc fuel
   end. 
  
Fixpoint fuel_trm t  := 
  match t with
    | tProd _ u v => fuel_trm u + fuel_trm v + 1
    | _ => 1
  end.

Definition add_trm_parameter (t : term) :=
  let fuel := fuel_trm t in 
  add_trm_for_each_poly_var t [] fuel.

End P.

Section tests. 

Variable (P : Type -> Type).

MetaCoq Unquote Definition 
trm_unq :=  (add_trm_parameter <% P %> <% forall (A : Type) (a : A), list A -> list A -> Prop %>).

MetaCoq Unquote Definition 
trm_unq2 :=  (add_trm_parameter <% P %> <% forall (A : Type) (B: Type), A -> B -> Prop %>).

(* Print trm_unq. *)
(* Print trm_unq2. *)

End tests.
