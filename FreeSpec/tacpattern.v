Require Import sniper.
From MetaCoq Require Import All.


Print lookup_env.
Print Ast.

MetaCoq Quote Definition nat_reif := nat.

Print nat_reif.


Definition get_nb_constructors i Σ := 
match i with 
| tInd indu _ => match lookup_env Σ indu.(inductive_mind) with
                | Some (InductiveDecl decl) => match ind_bodies decl with 
                          | nil => 0
                          | x :: _ => length (ind_ctors x)
                          end
                | _ => 0
end
| _ => 0
end.

MetaCoq Quote Recursively Definition list_reif_rec := list.

Compute get_nb_constructors list_reif_rec.2 list_reif_rec.1.



(* Ltac get_nb_constructors_tac i k :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => 
k constr:(get_nb_constructors i_reif_rec.2 i_reif_rec.1)). *)

Ltac get_nb_constructors_tac i id :=
run_template_program (tmQuoteRec i) ltac:(fun i_reif_rec => let n := 
eval cbv in (get_nb_constructors i_reif_rec.2 i_reif_rec.1) in
pose (id := n)).

(* NOTE : il faut donner en paramètre de la continuation une vraie tactique c'est à dire une pas 
value_tactic *)


Goal True.
get_nb_constructors_tac bool ident:(foo).
exact I. Qed.


Goal False.
let H := fresh in get_nb_constructors_tac bool H.
Abort.




Ltac eliminate_pattern_matching H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) ; let T := type of x in 
run_template_program (tmQuoteRec T) ltac:(fun T_reif_rec => 
let n := eval cbv in (get_nb_constructors T_reif_rec.2 T_reif_rec.1) in 
)
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct_applied A n) in 
let l_ctor_and_ty_ctor := eval cbv in (combine l_ctors l_ty_ctors) in
let list_of_hyp := eval cbv in (get_equalities E l_ctor_and_ty_ctor l) in
 unquote_list list_of_hyp ; prove_hypothesis H )] ; clear H.