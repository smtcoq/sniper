Ltac bar T := match T with
| forall z, ?H' => bar H' ; idtac H'
| context C[match ?x with _ => _ end] => idtac x
end.

Ltac foo H := let T := type of H in bar T.

Ltac toto H := let T := type of H in match T with
| forall y, ?P => idtac P
end.

Goal forall A (l : list A), length l = 0 -> (forall A (x : list A), length x = match x with 
| nil => 0
| _ => 1 
end) -> False.
intros A l H H1.
 rewrite H1 in H. toto H1. foo H.
foo H1.

