From Ltac2 Require Import Init Message Int Bool.

(* Ref.v *)
Ltac2 Type 'a ref := 'a Init.ref.

Ltac2 ref (v : 'a) : 'a ref := { contents := v}.
Ltac2 get (r : 'a ref) : 'a := r.(contents).
Ltac2 set (r : 'a ref) (v : 'a) : unit := r.(contents) := v.

Ltac2 update (r : 'a ref) (f : 'a -> 'a) : unit :=
  r.(contents) := f (r.(contents)).


(* Ça commence ici *)
Ltac2 Type refs := [ .. ].

Ltac2 Type refs ::= [ IR (int ref) ].
Ltac2 bar r :=
  match r with
  | IR r =>
      set r (Int.add (get r) 1);
      ltac1:(idtac "youpi");
      set r (Int.add (get r) 1);
      print (of_int (get r))
  | _ => ltac1:(idtac "pas la bonne réf")
  end.
Ltac2 initbar () : refs := IR (ref 3).

Ltac2 Type refs ::= [ BR (bool ref) ].
Ltac2 foo r :=
  match r with
  | BR b =>
      set b (Bool.neg (get b));
      print (of_string (if (get b) then "true" else "false"))
  | _ => ltac1:(idtac "pas la bonne réf")
  end.
Ltac2 initfoo () : refs := BR (ref true).

Ltac2 rec ordoSimplet transfos :=
  match transfos with
  | [] => ltac1:(idtac "finito pipo !")
  | (t, i)::transfos' =>
      let r := i () in
      t r;
      ordoSimplet transfos'
  end.

Ltac2 transfos := [ (bar, initbar); (foo, initfoo) ].
Ltac2 Eval (ordoSimplet transfos).