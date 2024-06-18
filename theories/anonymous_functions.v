Require Import utilities.
Require Import List.
From Ltac2 Require Import Ltac2.

Ltac anonymous_fun f_body := 
  let f' := fresh "f" in pose (f' := f_body); 
  try fold f';
  let tac := 
  ltac2:(f' |-
    let hs := Control.hyps () in
    List.iter (fun (x, _, _) => 
      ltac1:(f' x |- try (fold f' in x)) f' (Ltac1.of_ident x)) hs) 
  in tac f'.

Section tests.

Set Default Proof Mode "Classic".

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
assert (H : (fun x => x + 1) 42 = 43) by reflexivity.
anonymous_fun (fun x : nat => x + 1).
anonymous_fun (fun x : A => g (f x)).
Abort.
  
Goal (forall (A: Type) (n : nat) (l : list A) (x : A), 
(fun (n : nat) (l : list A) (default : A) => nth n l default) n l x = x ->
(n >= (fun (l : list A) => length l) l)).
Proof. intros. 
anonymous_fun (fun (A: Type) (n: nat) (l : list A) (d : A) =>
nth n l d). 
anonymous_fun (fun l0 : list A => length l0). Abort.

End tests.


