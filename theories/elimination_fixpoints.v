(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import MetaCoq.Template.All.
Require Import utilities.
Require Import definitions.
Require Import expand.
Require Import List.
Import ListNotations.
Require Import String.
(* From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From elpi Require Import elpi.

Elpi Tactic print_args.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [trm Arg]) _ :- coq.say "yo".
}}.
Elpi Typecheck.


Set Default Proof Mode "Classic".

Ltac2 first (x: 'a*'b) := 
match x with
| (y, z) => y 
end.

Ltac2 second (x: 'a*'b) := 
match x with
| (y, z) => z 
end.

Ltac2 fail s := Control.backtrack_tactic_failure s. 

Ltac2 rec recursive_arg (f: constr) : int :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix recargs nbindu _ _ => Array.get recargs nbindu
  | Constr.Unsafe.Lambda _ body => Int.add 1 (recursive_arg body)
  | _ => 0
  end.

Ltac2 body_fixpoint (f: constr) : constr :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix _ nbindu _ constrs => Array.get constrs nbindu
  | _ => fail "not a fixpoint"
  end.

Ltac2 reduces_to_aux (f1 : constr) (f2: constr) :=
let f1' := (eval red in $f1) in
if Constr.equal f1' f2 then f1
else fail "not equal".

Ltac2 reduces_to (f1 : constr) (f2 : constr) :=
match Constr.Unsafe.kind f1 with
  | Constr.Unsafe.App f args => 
      if Constr.is_const f then reduces_to_aux f1 f2
      else 
        match Constr.Unsafe.kind f with
          | Constr.Unsafe.Var id => let f1' := Control.hyp id in reduces_to_aux f1' f2
          | _ => fail "not an applied constant or an applied variable"
        end
  | Constr.Unsafe.Constant _ _ => reduces_to_aux f1 f2
  | Constr.Unsafe.Var id => let f1' := Control.hyp id in reduces_to_aux f1' f2
  | _ => fail "not a constant"
end.

(* Looks for a constant in the goal 
or in the hypotheses which reduces to f, 
pose a local def if it fails to find one *)

Ltac2 rec find_term_reduces_to_in_goal (f : constr) (id : ident) :=
match! goal with
  | [ |- context [?t]] => reduces_to t f  
  | [ _ : context [?t] |- _ ] => reduces_to t f
  | [h : _ |-  _] => let f1 := Control.hyp h
     in reduces_to f1 f
  | [ |- _ ] => Std.pose (Some id) f ; find_term_reduces_to_in_goal f id
end.

Ltac2 some_or_fail (x : 'a option) : 'a :=
match x with
| None => fail "none"
| Some x' => x'
end.

Ltac2 print_subterms h := 
  match! h with
  | context [ ?t ]  => Message.print (Message.of_constr t)
  | _ => fail "foo"
  end. 

Ltac2 get_name c :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Prod b _ => Ltac2.Option.default @x (Constr.Binder.name b)
| _ => Control.throw Not_found
end.

Ltac generate_proof :=
match goal with 
| H : list _ |- _ => destruct H end.

Ltac2 prf_in_context (c : constr) () :=
let c' := Ltac1.of_constr c in
ltac1:(c' |- (refine ( _ : c'))) c' ; ltac1:(
repeat match goal with | H : list _ |- _ => destruct H end) ; reflexivity. 

Ltac2 mkProd (c: constr) (id : ident) (ty : constr) :=
Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.make (Some id) ty) c).

Ltac2 rec in_contexts (ids : (ident*constr) list) (c : constr) (tac : constr -> unit -> unit) :=
match ids with
| [] => c
| x :: xs => 
  match x with
    | (id, ty) => let c' := (in_contexts xs c tac) in
            Constr.in_context (Fresh.in_goal id) ty (tac c')
  end
end.

Ltac2 refine_bis (c : constr) () :=
refine c.


Ltac instantiate_evar_with_constr G :=
repeat match goal with 
| u : Prop |- _ => instantiate (u := G)
end.

Ltac2 rec under_forall (bd: binder list) (h: constr) :=
match Constr.Unsafe.kind h with
  | Constr.Unsafe.Prod bind h' =>
(*     let ty := Constr.Binder.type bind in *)
    let na := Constr.Binder.name bind in 
    let na' := some_or_fail na in
    under_forall (bind::bd) (Constr.Unsafe.closenl [na'] 1 h')
  | _ => (bd, h)
end.

Ltac2 rec binder_to_id_types (bd : binder list) : (ident*constr) list :=
match bd with
  | b :: bds => 
    let ty := Constr.Binder.type b in
    let na := Constr.Binder.name b in 
    let na' := some_or_fail na in
    (na', ty) :: binder_to_id_types bds
  | [] => []
end.

Ltac2 rec find_applied (h1 : constr) (h2 : constr) :=
match Constr.Unsafe.kind h1 with
  | Constr.Unsafe.Prod bind h1' =>  
    let ty := Constr.Binder.type bind in
    let na := Constr.Binder.name bind in
    let na' := some_or_fail na in
    Constr.in_context (Fresh.in_goal na') ty (find_applied h1' h2)
  | 


Ltac2 rec find_applied (il: (ident*constr) list) (h: constr) :=
match Constr.Unsafe.kind h with
  | Constr.Unsafe.Prod bind h' =>
    let ty := Constr.Binder.type bind in
    let na := Constr.Binder.name bind in
    let na' := some_or_fail na in
    find_applied ((na', ty)::il) h'
  | _ => match! h with
    | context c [ ?t ]  => 
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App f args => 
                if Constr.is_fix f then 
                (let recarg := recursive_arg f in
                  if Int.le recarg (Array.length args)
                  then 
                   let body := body_fixpoint f in
                   let const := 
                    find_term_reduces_to_in_goal f (some_or_fail (Ident.of_string "new_fix")) in 
                   let new_term := Constr.Unsafe.make (Constr.Unsafe.App 
                      (Constr.Unsafe.substnl [const] 0 body) args) in
                   let new_hyp := Pattern.instantiate c new_term in 
                   let new_hyp_beta := (eval cbv beta in $new_hyp) in 
                   let new_hyp_abstract := Constr.Unsafe.closenl 
                   let id := Fresh.in_goal @H in
                   assert (id : $new_hyp_beta) > [ltac1:(generate_proof) |
                   let proof_term := Control.hyp @id in print (of_constr proof_term) ;
                   let proof_term_quantif := in_contexts (List.rev il) proof_term refine_bis in
                   let proof_type_quantif := Constr.type proof_term_quantif in 
                   let tyltac1 := Ltac1.of_constr proof_type_quantif in
                   ltac1:(x |- instantiate_evar_with_constr x) tyltac1]
                  else fail "not applied enough")
                else fail "not a fixpoint"
      | _ => fail "not an application"
      end
    end
  end. 

Ltac2 rec list_of_dbindexes (n : int) :=
if Int.equal n 0 then []
else (Constr.Unsafe.make (Constr.Unsafe.Rel n)) :: list_of_dbindexes (Int.sub n 1).

Ltac2 rec print_list (l : constr list) :=
match l with
| [] => ()
| x :: xs => print (of_constr x) ; print_list xs 
end.


Ltac2 rec replace_binders_aux (acc : constr list) (c : constr) :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Prod bind c' => 
    let dbstart := Int.add (List.length acc) 1 in     
    let ty := Constr.Binder.type bind in 
    let ty' := Constr.Unsafe.substnl acc dbstart ty in
    replace_binders_aux (ty'::acc) c'
| _ => let dbstart := Int.add (List.length acc) 1 in
    Constr.Unsafe.substnl acc dbstart c
end.

Ltac2 replace_binders (c : constr) := replace_binders_aux [] c.

Ltac2 rec find_applied (il: (ident*constr) list) (t : constr) : unit :=
  match! goal with
  | [ |- forall _ : _, _ ] => 
    let x := Fresh.in_goal (get_name (Control.goal ())) in
    Std.intro (Some x) None ; 
    let h := Control.hyp x in 
    let t := Constr.type h in
    find_applied ((x, t)::il)
  | [ |- context c [ ?t ]]  => 
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App f args => 
                if Constr.is_fix f then 
                (let recarg := recursive_arg f in
                  if Int.le recarg (Array.length args)
                  then 
                   let body := body_fixpoint f in 
                   let const := 
                    find_term_reduces_to_in_goal f (some_or_fail (Ident.of_string "new_fix")) in 
                   let new_term := Constr.Unsafe.make (Constr.Unsafe.App 
                      (Constr.Unsafe.substnl [const] 0 body) args) in
                   let new_hyp := Pattern.instantiate c new_term in 
                   let new_hyp_beta := (eval cbv beta in $new_hyp) in 
                   let id := Fresh.in_goal @H in
                   assert (id : $new_hyp_beta) > [ltac1:(generate_proof) |
                   let proof_term := Control.hyp @id in 
                   let proof_term_quantif := in_contexts (List.rev il) proof_term refine_bis in
                   let proof_type_quantif := Constr.type proof_term_quantif in 
                   let len := List.length il in 
(*                    let proof_term_abstract := 
                    Constr.Unsafe.closenl (first (List.split il)) len proof_term_quantif in
                   let proof_type_abstract :=  
                    Constr.Unsafe.closenl (first (List.split il)) (Int.sub len 1) proof_type_quantif in *)
(*                    let prf_type := replace_binders proof_type_abstract in print (of_constr prf_type) ; *)
                    

                    (* (Constr.Unsafe.substnl (List.rev (list_of_dbindexes len)) (Int.add len 1) proof_type_abstract)  *)
                   let tyltac1 := Ltac1.of_constr proof_type_quantif in
                   ltac1:(x |- let x := metacoq_get_value (tmQuote x) in idtac x) tyltac1
                  (*  ltac1:(x |- instantiate_evar_with_constr x) tyltac1 *)]
                  else fail "not applied enough")
                else fail "not a fixpoint"
      | _ => fail "not an application"
      end
  end.  
Ltac pose_goal := 
let H := fresh in
let H_evar := fresh in
epose (H := ?[H_evar] : Prop).

Ltac2 eliminate_fix_hyp (h : constr) :=
ltac1:(pose_goal);
let t := Constr.type h in
let x := Fresh.in_goal @H in
assert (x : False -> $t) > 
[Std.intro (Some @HFalse) None;  
find_applied [] ; destruct HFalse
| clear x ].

Goal True.
Proof.
get_def Datatypes.length; expand_hyp length_def.
run_template_program (tmQuote I) ltac:(fun x => idtac x).
ltac2:(eliminate_fix_hyp 'H). 

exact I. Qed.
ltac1:(let T := type of H in assert (H1 : False -> T) ; [
intro HFalse | ..]).  find_applied []. let t := find_applied @A in assert $t.
destruct l; reflexivity. ltac1:(generalize dependent A). intros.
 
destruct l; auto.
revert l ; revert A.




destruct l0 ; cbv fix ; fold (@Datatypes.length A0)

 |..]).

 let h := Control.hyp @H in
let t := Constr.type h in
 find_applied t.


print_subterms '(fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end).

 ltac1:(get_def length; expand_hyp length_def).
let h' := Control.hyp @H in 
let t := (Constr.type h') in 
let x:= find_applied t in Message.print (Message.of_constr x). *)

(* remove the nth last elements of a list *)
Fixpoint rem_last_elem {A} (n : nat) (l : list A) := match l, n with 
| nil, _ => nil
| cons _ _, 0 => l
| cons x xs, S n' => rem_last_elem n' xs
end.


Definition find_args (t1 t2 : term) := 
match t2 with
| tApp v l => 
    let n:= Datatypes.length l in 
    match t1 with 
      | tApp u l' => (lift n 0 (tApp u (rem_last_elem n l')), v, l)
      | _ => (t1, t2, l)
    end
| _ => (t1, t2, nil)
end.

Fixpoint under_forall_aux (t : term) (l : list (aname*term)) :=
match t with 
| tProd na T u => under_forall_aux u ((na, T)::l)
| _ => (t, l)
end.

Definition under_forall t := under_forall_aux t [].

Fixpoint create_forall (t : term) (l : list (aname*term)) :=
match l with 
| nil => t
| (na, T):: xs => create_forall (tProd na T t) xs
end.

Definition params_eq (t : term) := match t with 
| tApp u l => match l with 
            | [x1; x2; x3] => (u, (x1, x2, x3))
            | _ => (u, (u, u, u))
            end
| _ => (t, (t, t, t))
end.


(* Returns the definition in a fixpoint *)
Definition get_def_in_fix (f: term) := 
match f with 
| tFix l _ => match l with 
          | [] => f
          | x :: xs => x.(dbody)
          end
| _ => f
end.

Definition replace_tFix_by_def (t : term) (def : term) := match t with 
| tFix _ _ => (subst10 def (get_def_in_fix t))
| _ => t
end.


(* replace an anonymous fix by its definition *)
Ltac eliminate_fix_hyp H := 
let T := type of H in let T := metacoq_get_value (tmQuote T) in
let p := eval cbv in (under_forall T) in 
let eq := eval cbv in p.1 in
let list_quantif := eval cbv in p.2 in
let get_info_eq := eval cbv in (params_eq eq) in 
let eq_reif := eval cbv in get_info_eq.1 in 
let A := eval cbv in get_info_eq.2.1.1 in 
let t := eval cbv in get_info_eq.2.1.2 in 
let u := eval cbv in get_info_eq.2.2 in
let prod := eval cbv in (find_args t u) in 
let args := eval cbv in prod.2 in (* the arguments of u *)
let def := eval cbv in prod.1.1 in 
let u_no_app := eval cbv in prod.1.2 in 
let u_no_fix := eval cbv in (replace_tFix_by_def u_no_app def) in
let eq_no_fix := eval cbv in (create_forall (mkEq A t (tApp u_no_fix args)) list_quantif) in
let z := metacoq_get_value (tmUnquote eq_no_fix) in
let H' := fresh in let w := eval hnf in z.(my_projT2) 
in assert (H' :w) 
by (repeat (let x := fresh in intro x ; try (destruct x ; auto))).

Ltac eliminate_fix_cont H := fun k =>
first [
let T := type of H in
let T := metacoq_get_value (tmQuote T) in
let p := eval cbv in (under_forall T) in 
let eq := eval cbv in p.1 in
let list_quantif := eval cbv in p.2 in
let get_info_eq := eval cbv in (params_eq eq) in 
let eq_reif := eval cbv in get_info_eq.1 in 
let A := eval cbv in get_info_eq.2.1.1 in 
let t := eval cbv in get_info_eq.2.1.2 in 
let u := eval cbv in get_info_eq.2.2 in
let prod := eval cbv in (find_args t u) in 
let args := eval cbv in prod.2 in (* the arguments of u *)
let def := eval cbv in prod.1.1 in 
let u_no_app := eval cbv in prod.1.2 in 
let u_no_fix := eval cbv in (replace_tFix_by_def u_no_app def) in 
let eq_no_fix := eval cbv in (create_forall (mkEq A t (tApp u_no_fix args)) list_quantif) in
let z := metacoq_get_value (tmUnquote eq_no_fix) in
let H' := fresh in let w := eval hnf in z.(my_projT2)
in assert (H' :w) 
by (repeat (let x := fresh in intro x ; try (destruct x ; auto))) ; k H' ; clear H| k H].

Section tests.

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
expand_hyp add_def.
assert (H3 : True -> forall n : nat,
   id (Nat.add n) =
    id ((fix add (n0 m0 : nat) {struct n0} : nat :=
       match n0 with
       | 0 => m0
       | S p => S (add p m0)
       end)) n) by reflexivity.
eliminate_fix_hyp H3.
eliminate_fix_hyp H.
expand_hyp length_def.
eliminate_fix_hyp H1.
Abort.

Goal False.
get_def @Datatypes.length.
get_def Nat.add.
expand_hyp add_def.
eliminate_fix_cont H ltac:(fun H0 => let t := type of H0 in idtac).
expand_hyp length_def.
eliminate_fix_hyp H.
Abort.



Goal False.
get_def @Datatypes.length.
expand_hyp length_def.
eliminate_fix_hyp H.
get_def Nat.add.
expand_hyp add_def.
eliminate_fix_hyp H1.
Abort.


End tests.



