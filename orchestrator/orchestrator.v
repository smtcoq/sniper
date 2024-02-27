From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Printf.
Require Import List.
Import ListNotations.
Require Import printer.
Require Import triggers.
Require Import filters.
Require Import triggers_tactics.

Ltac2 Type all_tacs :=
  { mutable all_tacs : (string * trigger * filter) list }.

(* 

Reminder in triggers.v file : 

pair between tactics and arguments and their type on which it was already triggered 

Ltac2 Type already_triggered :=
  { mutable already_triggered : (string * ((constr * constr) list)) list }. *)

Ltac2 rec list_pair_equal (eq : 'a -> 'a -> bool) l1 l2  :=
  match l1, l2 with
    | [], [] => true
    | (x1, y1) :: l1', (x2, y2) :: l2' => 
        Bool.and (Bool.and (eq x1 x2) (eq y1 y2)) (list_pair_equal eq l1' l2')
    | _ => false
  end.

(** Checks if the tactic was already triggered *)

Ltac2 already_triggered
(l : (string * ((constr*constr) list)) list) 
(p : string * constr list) :=
  let (nametac, largs) := p in
  let tyargs := List.map type largs in
  let largstyargs := List.combine largs tyargs in
  let rec aux l :=
      match l with
        | (s, llc) :: l' =>
          if String.equal s nametac then
            if list_pair_equal equal largstyargs llc then true else aux l'
          else aux l'
        | [] => false
      end in aux l.

Ltac2 hyp_equal h h' :=
let (id1, opt1, c1) := h in
let (id2, opt2, c2) := h' in
if Ident.equal id1 id2 then
  if Constr.equal c1 c2 then
    match opt1, opt2 with
      | Some x, Some y => Constr.equal x y
      | None, Some _ => false
      | Some _, None => false
      | None, None => true
    end
  else false
else false.

Ltac2 rec diff_hyps hs1 hs2 :=
  match hs1, hs2 with
    | [], hs2' => hs2'
    | x :: xs, y :: ys => 
      if hyp_equal x y then diff_hyps xs ys 
      else y :: diff_hyps xs ys
    | x :: xs, [] => [] (* we do not consider removed hypotheses *)
  end.

Ltac2 is_tonetime t :=
  match t with
  | TOneTime => true
  | _ => false
  end.

Ltac2 filter_onetime lt :=
  List.filter_out is_tonetime lt. 
 

Ltac2 Type verbosity :=
[ Nothing | Info | Debug | Full ].

Ltac2 leq_verb (v1 : verbosity) (v2 : verbosity) :=
  match v1 with
    | Nothing => true
    | Info => 
        match v2 with
          | Nothing => false
          | _ => true
        end
    | Debug =>
        match v2 with
          | Nothing => false
          | Info => false
          | _ => true
        end 
    | Full => 
        match v2 with
          | Full => true
          | _ => false
        end
   end. 

Ltac2 print_tactic_not_triggered (v : verbosity) (s : string) :=
if leq_verb v Debug then () else
printf "NONE: The following tactic was not triggered: %s" s.

Ltac2 print_tactic_already_applied (v : verbosity) (s : string) (l : constr list) :=
if leq_verb v Debug then () else
(printf "%s was already applied with the following args :" s ; 
List.iter (fun x => printf "%t" x) l).

Ltac2 print_tactic_already_applied_once (v : verbosity) (s : string) :=
if leq_verb v Debug then () else
printf "%s was already applied one time" s.

Ltac2 print_tactic_global_in_local (v : verbosity) (s : string) :=
if leq_verb v Debug then () else
printf "%s is global and cannot be applied in a local state" s.

Ltac2 print_state_verb (v : verbosity) it :=
if leq_verb v Debug then () else
print_state (it.(local_env)).

Ltac2 print_applied_tac (v : verbosity) (s : string) (l : constr list) :=
if leq_verb v Nothing then () else
(printf "Automatically applied %s with the following args" s ;
List.iter (fun x => printf "%t" x) l).

Ltac2 print_tactic_trigger_filtered (v : verbosity) (s : string) (l : constr list) :=
if leq_verb v Debug then () else
(printf "The tactic %s was filtered with the following args" s ;
List.iter (fun x => printf "%t" x) l).


Ltac2 rec orchestrator_aux
  alltacs (* the mutable field of all tactics *)
  fuel
  it (* the interpretation state (see [triggers.v]) *)
  env (* local triggers variables *)
  (trigstacsfis : (trigger*string* filter) list) 
  (trigtacs : already_triggered) (* Triggered tactics, pair between a string and a list of arguments and their types *) 
  (v: verbosity) : (* number of information required *) unit := 
  print_state_verb v it ;
  match trigstacsfis with
    | [] => 
        if (it).(global_flag) then () 
        else orchestrator (Int.sub fuel 1) alltacs trigtacs v
    | (trig, name, fi) :: trigstacsfis' => 
         (it).(name_of_tac) := "name" ;
         let interp := interpret_trigger it env trigtacs trig in
         match interp with
          | None =>
             print_tactic_not_triggered v name ;
             orchestrator_aux alltacs fuel it env trigstacsfis' trigtacs v
          | Some ll =>
            let rec aux ll :=
              match ll with
                | [] => orchestrator_aux alltacs fuel it env trigstacsfis' trigtacs v
                | l :: ll' =>
                    let lnotempty := Bool.neg (Int.equal (List.length l) 0) in
                    if Bool.and lnotempty (* instead: istonetime trig *)
                      ((already_triggered ((trigtacs).(already_triggered)) (name, l))) then 
                      print_tactic_already_applied v name l ;
                      aux ll'
                    else if Bool.and (is_tonetime trig) ((already_triggered ((trigtacs).(already_triggered)) (name, l))) then
                      print_tactic_already_applied_once v name ;
                      aux ll'
                    else if Bool.and (Bool.neg lnotempty) (Bool.neg ((it).(global_flag))) then
                      print_tactic_global_in_local v name ;
                      orchestrator_aux alltacs fuel it env trigstacsfis' trigtacs v               
                    else if Bool.neg (pass_the_filter l fi) then
                      print_tactic_trigger_filtered v name l ;
                      let ltysargs := List.map (fun x => type x) l in
                      let argstac := List.combine l ltysargs in
                      trigtacs.(already_triggered) := (name, argstac) :: (trigtacs.(already_triggered)) ;
                    aux ll'
                    else
                      (run name l; (* Control.hyps / Control.goal before the run to compute the diff *)
                      print_applied_tac v name l ;
                      let _ := 
                      if Bool.or lnotempty (is_tonetime trig) then
                        let ltysargs := List.map (fun x => type x) l in
                        let argstac := List.combine l ltysargs in
                        trigtacs.(already_triggered) := (name, argstac) :: (trigtacs.(already_triggered)) 
                      else () in
                      Control.enter (fun () =>
                      let cg' := (it).(local_env) in
                      let (hs1, g1) := cg' in
                      let hs2 := Control.hyps () in
                      let g2 := Control.goal () in
                      let g3 :=
                        match g1 with
                        | None => None
                        | Some g1' => if Constr.equal g1' g2 then None else Some g2 
                      end in it.(local_env) := (diff_hyps hs1 hs2, g3) ;     
                      orchestrator_aux alltacs fuel it env trigstacsfis trigtacs v))
              end in aux ll
        end
  end
 with orchestrator n alltacs trigtacs v :=
  if Int.equal n 0 then () else
  let g := Control.goal () in
  let hyps := Control.hyps () in 
  let env := { env_triggers := [] } in
  let it := { subterms_coq_goal := ([], None) ; local_env := (hyps, Some g); global_flag := true ; name_of_tac := ""} in
  let _ := orchestrator_aux alltacs n it env alltacs trigtacs v in
  Control.enter (fun () => orchestrator (Int.sub n 1) alltacs trigtacs v).

(* orchestrator / orchestrator_aux : redundant with global_flag *)

(** 
- TODO : essayer avec les tactiques de Sniper en les changeant le moins possible (scope)
- position des arguments
- Ltac2 notations (thunks)
- idée de Matthieu Sozeau, tag pour ce qui doit être unfoldé ou non, plutôt que de le mettre à l'intérieur des triggers
- regarder crush ou le crush des software foundations
- essayer d'ajouter autoinduct à Snipe
- 2 types de tactiques: celles qui disent ce qu'elles font et celles qui ne le disent pas 
- relancer sur Actema
*)

