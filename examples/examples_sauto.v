(* Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper. *)
From Sniper Require Import Sniper.
From Sniper Require Import tree.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Require Import OrderedType Psatz.
Import ListNotations.

From Hammer Require Import Tactics.


(* For now, only one transformation of scope is useful for sauto.
Adding lemmas in the context can slow down the tactic and even 
make it run forever. 
We only need the generation lemmas, already instantiated *) 

Ltac scope_sauto := intros ;
get_gen_statement_for_variables_in_context ; sauto.

Section Paper_examples.

  Section Simple_examples.

  Variable A: Type.

  Lemma app_eq_nil_destruct_sauto (l l' : list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof.
    destruct l; sauto.
  Qed.

  Lemma app_eq_nil_scope_sauto (l l' : list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof. Fail sauto. scope_sauto. Qed.

  End Simple_examples.


  Section CompCert.

  Local Open Scope Z_scope.

  Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

    Definition memory_chunk_to_Z mc :=
      match mc with
      | Mint8signed => 0%Z
      | Mint8unsigned => 1
      | Mint16signed => 2
      | Mint16unsigned => 3
      | Mint32 => 4
      | Mint64 => 5
      | Mfloat32 => 6
      | Mfloat64 => 7
      | Many32 => 8
      | Many64 => 9
      end.

    Lemma memory_chunk_to_Z_eq x y : x = y <-> memory_chunk_to_Z x = memory_chunk_to_Z y.
    Proof. Fail sauto. scope_sauto.
    Qed.

End CompCert.

End Paper_examples.


