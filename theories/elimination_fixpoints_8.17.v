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

(* Require Import utilities.
Require Import definitions.
Require Import expand. *)
Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.


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

Ltac2 get_name c :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Prod b _ => Ltac2.Option.default @x (Constr.Binder.name b)
| _ => Control.throw Not_found
end.

Ltac instantiate_evar_with_constr G :=
repeat match goal with 
| u : Prop |- _ => instantiate (u := G) ; let T := type of u in idtac T
end.

Ltac2 rec bind (il : (ident*constr) list) (t : constr) :=
match il with
| (id, ty) :: xs => 
    Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make (Some id) Constr.Binder.Relevant ty) (bind xs t))
| [] => t
end. 

Ltac2 rec find_applied (il: (ident*constr) list): constr :=
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
                   let ids := List.map first il in
                   let tys := (List.map second il) in
                   let new_hyp_abstract := (Constr.Unsafe.closenl ids 1 new_hyp_beta) in
                   let tysabstract := List.map (fun x => Constr.Unsafe.closenl ids 0 x) tys in
                   let new_binders := List.combine ids tysabstract in
                   bind (List.rev new_binders) new_hyp_abstract
                  else fail "not applied enough")
                else fail "not a fixpoint"
      | _ => fail "not an application"
      end
  end.  

Ltac last_type_of_hypothesis :=
match goal with
| H := ?x |- _ =>  x
end.

Ltac eliminate_fix_hyp h :=
let H := fresh in
let H_evar := fresh in
epose (H := ?[H_evar]) ;
let H1 := fresh in
let t := type of h in 
assert (H1 : False -> t) ; 
[ let Hfalse := fresh in intro Hfalse ;
  ltac2:(let c := find_applied [] in pose $c) ;
  let x := last_type_of_hypothesis in 
  instantiate (H_evar := x);
  destruct Hfalse | clear H1 ; let H' := eval unfold H in H
in assert H' by (repeat (let x := fresh in intro x ; try (destruct x ; auto)))]. 


Goal True. Print length.
Proof.
assert (H : forall (A : Type) (l: list A), 
length l = (fix length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end) l) by reflexivity.
eliminate_fix_hyp H. 
exact I. Qed.

Goal Nat.add = (fun n m : nat => match n with
                            | 0 => m
                            | S p => S (p + m)
                            end).
Proof.
unfold Nat.add.
Abort.

Goal False. Print Nat.add.
assert (H : forall n m, Nat.add n m =
(fix add (n m : nat) :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) n m) by reflexivity.
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



