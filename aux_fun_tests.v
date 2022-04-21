Add Rec LoadPath "/home/pierre/depots/sniper" as Sniper.
(* \Q why is this line needed? *)

Require Import utilities. 
Require Import interpretation_algebraic_types.
Require Import elimination_polymorphism.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.



Open Scope string_scope.  

Import ListNotations MonadNotation. 

Inductive my_type :=
  | A : my_type
  | B : my_type -> my_type
  | C : my_type -> my_type.

MetaCoq Quote Definition mt_reif := my_type.  
MetaCoq Quote Definition A_reif := A. 
MetaCoq Quote Definition B_reif := B.
MetaCoq Quote Definition C_reif := C.



