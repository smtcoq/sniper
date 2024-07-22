From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Init.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Std.
From Ltac2 Require Import Env.
From Ltac2 Require Import Message.
From Ltac2 Require Import Printf.
Import Unsafe.
Set Default Proof Mode "Classic".

Ltac2 rec print_interp_trigger (ll : constr list list) := 
  match ll with
    | [] => printf "no more triggers to print" 
    | l :: ll' => printf "trigger interpreted:" ; List.iter (fun x => printf "%t" x) l ; print_interp_trigger ll'
  end. 

(* The default fail of Ltac2 is of type unit -> unit 
so use this version with a message *)

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 id (a : 'a) := a.

Ltac2 fst (x : 'a*'b) := let (y, _) := x in y.

Ltac2 snd (x : 'a*'b) := let (_, y) := x in y.

Ltac2 Type exn ::= [ NotClosed(string) ].

(* Marks some parameter of the trigger as arguments for the tactic triggered 
or not 
(Arg f) t returns f t as argument *)  

Ltac2 Type flag :=
  [ Arg (constr -> constr) | NotArg ]. 

(* goals, hypotheses, local definitions, hypotheses of type T : Prop, bound variables *)
Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp | TSomeDef | TSomeHypProp | TNamed (string) ].

(* environment for named triggers variables, associated to a constr *)

Ltac2 Type env_triggers := 
  { mutable env_triggers : (string*constr) list }.

(* pair between tactics and arguments and their type on which it was already triggered *)

Ltac2 Type already_triggered :=
  { mutable already_triggered : (string * ((constr * constr) list)) list }.

Ltac2 Type trigger_sort :=
[ TProp | TSet | TBigType].

(* allows to specify the type of local variable considered *)
Ltac2 Type trigger_local_var :=
[ TAnyLocalVar | TLocalDef | TLocalHyp | TLocalNamed (string) ].

(* warning:
does not handle universe hierarchy, native arrays, integers, 
projections or floats *)
Ltac2 Type rec trigger_term := [

(* follows the constr type *)
| TRel (int, flag)
| TVar (trigger_local_var, flag) (* local variable or section variable *)
| TSort (trigger_sort, flag) (* simplification of universes *)
| TProd (trigger_term, trigger_term, flag)
| TLambda (trigger_term, trigger_term, flag)
| TLetIn (trigger_term, trigger_term, trigger_term, flag)
| TApp (trigger_term, trigger_term, flag)
| TConstant (string option, flag)
| TInd (string option, flag)
| TConstructor (string option, flag)
| TCase (trigger_term, trigger_term, trigger_term list option, flag) 
| TFix (trigger_term, trigger_term, flag)
| TCoFix (trigger_term, trigger_term, flag)

(* specific to triggers *)
| TType (constr, flag)
| TTerm (constr, flag)
| TTrigVar (trigger_var, flag)
| TAny (flag) 

(* less fine-grained structure *)
| TEq (trigger_term, trigger_term, trigger_term, flag)
| TAnd (trigger_term, trigger_term, flag)
| TOr (trigger_term, trigger_term, flag)
].
 
Ltac2 tArg := TAny (Arg id).
Ltac2 tArgType := TAny (Arg type).
Ltac2 tDiscard := TAny NotArg.

Ltac2 Type rec trigger := [
  | TIs ((trigger_var*flag), trigger_term) 
  | TPred ((trigger_var*flag), constr -> bool) (* the trigger_var should verify the user-defined Ltac2 predicate *)
  | TContains ((trigger_var*flag), trigger_term)
  | TConj (trigger, trigger) (* two triggers need to be present at the same time *)
  | TDisj (trigger, trigger) (* one of the two triggers needs to be present *)
  | TNot (trigger) (* negation of a trigger *)
  | TMetaLetIn (trigger, string list, trigger) (* TMetaLetIn t1 s t2 binds all constrs produced by interpret_trigger t1
and gives them the corresponding names in s, adds thems to the environment and interprets t2 that may contain some TNamed "foo" *)
  | TAlways (* always triggers the tactic *)
  | TNever (* never triggers the tactic *)
  ]. 

(* Notations *)

Ltac2 tTrivial := TIs (TGoal, NotArg) tDiscard.

Ltac2 tGetArg (s: string) := TIs (TNamed s, Arg id) tDiscard.

(* Associates a name of ls to a constr *)
Ltac2 rec bind_triggers env (lc : constr list) (ls : string list) :=
  match lc, ls with
    | [], [] => ()
    | _, [] => fail "you have more terms to bind than binders' names"
    | [], _ => fail "you have more binders than terms to bind"
    | c :: lc, s :: ls => env.(env_triggers) := (s, c) :: (env.(env_triggers)) ; bind_triggers env lc ls
  end.

Ltac2 Type hyps_or_letins_or_goal_or_constr := [
  | Hyps ((ident*constr option*constr) list) 
  | LetIns ((ident*constr*constr) list)
  | Goal (constr option)
  | Constr (constr) ].

(* Filter "real" hypotheses 
(in the sense that we filter out local definitions) *)
Ltac2 filter_hyps hyps :=
  List.filter (fun (h, opt, c) => 
    match opt with
      | Some _ => false
      | None => true
    end) hyps.

Ltac2 filter_defs hyps :=
  let l :=
  List.filter (fun (h, opt, c) => 
    match opt with
      | Some _ => true
      | None => false
    end) hyps in List.map (fun (x, y, z) => (x, Option.get y, z)) l.

Ltac2 filter_hyps_prop hyps :=
  List.filter (fun (h, opt, c) => 
    match opt with
      | Some _ => false
      | None => equal (type c) 'Prop
    end) hyps.

Ltac2 interpret_trigger_var cg env (tv: trigger_var) :=
  let (hyps, g) := cg in
    match tv with
      | TSomeHyp => Hyps (filter_hyps hyps)
      | TSomeHypProp => Hyps (filter_hyps_prop hyps)
      | TSomeDef => LetIns (filter_defs hyps)
      | TGoal => Goal g
      | TNamed s => Constr (List.assoc String.equal s env)
    end. 
 
Ltac2 interpret_trigger_var_with_constr cg env tv c :=
  let itv := interpret_trigger_var cg env tv in
    match itv with
      | Hyps hyps => 
          let l := List.find_all (fun (_, _, z) => equal z c) hyps in 
            match l with
              | [] => None
              | (_, _, z) :: xs => Some z 
            end
      | LetIns defs =>
          let l := List.find_all (fun (_, bod, _) => equal bod c) defs in 
            match l with
              | [] => None
              | (_, bod, _) :: xs => Some bod
            end
      | Goal (Some g) => if equal g c then Some g else None
      | Goal None => None
      | Constr c' => if equal c c' then Some c else None

    end.

Ltac2 destruct_eq (c : constr) :=
  match kind c with
    | App c' ca => 
        if Bool.and (equal c' '(@eq)) (Int.equal (Array.length ca) 3)  then 
          let ty := Array.get ca 0 in
          let c1 := Array.get ca 1 in
          let c2 := Array.get ca 2 in
          Some (ty, c1, c2)
        else None
    | _ => None
  end. 

Ltac2 destruct_and (c : constr) :=
  match kind c with
    | App c' ca => 
        if Bool.and (equal c' 'and) (Int.equal (Array.length ca) 2) then 
          let c1 := Array.get ca 0 in
          let c2 := Array.get ca 1 in
          Some (c1, c2)
        else None
    | _ => None
  end.

Ltac2 destruct_or (c : constr) :=
  match kind c with
    | App c' ca => 
        if Bool.and (equal c' 'or) (Int.equal (Array.length ca) 2) then 
          let c1 := Array.get ca 0 in
          let c2 := Array.get ca 1 in
          Some (c1, c2)
        else None
    | _ => None
  end.

Ltac2 curry_app (c : constr) (ca : constr array) :=
  let cl := Array.to_list ca in
  let rec tac_rec c cl := 
    match cl with
      | [] => c
      | x :: xs => tac_rec (make (App c (Array.of_list [x]))) xs
    end
  in tac_rec c cl. 

Ltac2 ref_equal_upto_univs (r1 : reference) (r2 : reference) :=
  match r1, r2 with
    | VarRef id1, VarRef id2 => Ident.equal id1 id2
    | ConstRef c1, ConstRef c2 => 
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | IndRef _, IndRef _ =>
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | ConstructRef _, ConstructRef _ => 
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | _ => false
  end.

(* Does it exist a matching reference whose name is an expansion
of the optional string given as first argument *)
Ltac2 matching_ref (o : string option) (r : reference) : bool :=
  match o with
    | Some s =>
        let o' := Ident.of_string s in
          match o' with
            | None => false
            | Some id =>
                let refs := expand [id] in
                List.exist (ref_equal_upto_univs r) refs
          end
    | None => true
  end.

Ltac2 interpret_flag (c : constr) (f : flag) :=
  match f with
    | Arg g => Some (g c)
    | NotArg => None
  end.

Ltac2 cons_option (c : constr option) (l : constr list) :=
  match c with
    | Some c => c :: l
    | None => l
  end.

Ltac2 is_some (a : 'a option) :=
  match a with
    | None => false
    | Some _ => true
  end.

Ltac2 is_local_def (c : constr) :=
  match kind c with
    | Var id => 
        let hs := Control.hyps () in 
        List.exist (fun (x, y, z) => Bool.and (Ident.equal x id) (is_some y)) hs
    | _ => false
  end.

Ltac2 is_local_hyp (c : constr) :=
  match kind c with
    | Var id => 
        let hs := Control.hyps () in 
        List.exist (fun (x, y, z) => Bool.and (Ident.equal x id) (Bool.neg (is_some y))) hs
    | _ => false
  end.

(* Matches a trigger against a constr and returns the potential arguments 
of the tactic *)

Ltac2 rec interpret_trigger_term_with_constr
 (cg: (ident * constr option * constr) list * constr
  option) env (c : constr) (tte : trigger_term) : constr list option:=
  match kind c, tte with
    | App _ arr, TEq tte1 tte2 tte3 fl => 
        if Int.equal (Array.length arr) 3 then
        match destruct_eq c with
          | Some (c1, c2, c3) => 
              match interpret_trigger_term_with_constr cg env c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg env c2 tte2 with
                      | Some l' => 
                          match interpret_trigger_term_with_constr cg env c3 tte3 with
                            | Some l'' => Some (cons_option (interpret_flag c fl) (List.append (List.append l l') l''))
                            | None => None
                          end
                      | None => None
                    end
                | None => None
              end
          | None => None
        end else None
    | App _ arr, TAnd tte1 tte2 fl =>
        if Int.equal (Array.length arr) 2 then 
        match destruct_and c with
          | Some (c1, c2) =>
              match interpret_trigger_term_with_constr cg env c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg env c2 tte2 with
                      | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                      | None => None
                    end
                | None => None
              end
          | None => None
        end else None
    | App _ arr, TOr tte1 tte2 fl =>
        if Int.equal (Array.length arr) 2 then 
        match destruct_or c with
          | Some (c1, c2) =>
              match interpret_trigger_term_with_constr cg env c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg env c2 tte2 with
                      | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                      | None => None
                    end
                | None => None
              end
          | None => None
        end else None
(* De Brujin indexes: cannot be given as arguments to the tactic triggered. Otherwise 
the variable would escape its scope. *)
    | Rel n1, TRel n2 fl => if Int.equal n1 n2 then Some (cons_option (interpret_flag c fl) []) else None 
(* Local (or section) variables *)
    | Var id, TVar tlv fl => 
        match tlv with
          | TLocalNamed s =>
              match Ident.of_string s with
                | Some id' =>
                    if Ident.equal id id' then Some (cons_option (interpret_flag c fl) [])
                    else None
                | None => None
              end
          | TAnyLocalVar => Some (cons_option (interpret_flag c fl) [])
          | TLocalDef => if is_local_def c then  Some (cons_option (interpret_flag c fl) []) else None
          | TLocalHyp => if is_local_hyp c then  Some (cons_option (interpret_flag c fl) []) else None
          end
(* Sorts: we do not want to deal with universes, as we are afraid 
this may introduce difficulties which are unrelated to our main goal, 
but we want to distinguish between Prop, Set and Type_i, i >= 0 *)
    | Sort s, TSort ts fl =>
        match ts with
          | TProp => if equal c 'Prop then Some (cons_option (interpret_flag c fl) []) else None
          | TSet => if equal c 'Set then Some (cons_option (interpret_flag c fl) []) else None
          | TBigType => 
              if Bool.and (Bool.neg (equal c 'Prop)) (Bool.neg (equal c 'Set))
                then Some (cons_option (interpret_flag c fl) []) else None
        end
    | Prod bi t, TProd tte1 tte2 fl => 
        let ty := Binder.type bi in
        let res := interpret_trigger_term_with_constr cg env ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg env t tte2 in
                  match res' with
                    | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                    | None => None
                  end
            | None => None
          end
    | Lambda bi t, TLambda tte1 tte2 fl => 
        let ty := Binder.type bi in
        let res := interpret_trigger_term_with_constr cg env ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg env t tte2 in
                  match res' with
                    | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                    | None => None
                  end
            | None => None
          end
    | LetIn bi t t', TLetIn tte1 tte2 tte3 fl => 
        let ty := Binder.type bi in
        let res := interpret_trigger_term_with_constr cg env ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg env t tte2 in
                  match res' with
                    | Some l' => 
                        let res'' := interpret_trigger_term_with_constr cg env t' tte3 in
                          match res'' with
                            | Some l'' => Some (cons_option (interpret_flag c fl) (List.append (List.append l l') l''))
                            | None => None
                          end
                    | None => None
                  end
            | None => None
          end
(* Application case : Some adjustments are made to be sure 
that we have binary apps on both sides *)  
    | App c ca, TApp tte1 tte2 fl => 
       if Int.le (Array.length ca) 1 then
        let res := interpret_trigger_term_with_constr cg env c tte1 in
          match res with
            | Some l => 
                let c' := Array.get ca 0 in
                let res' := interpret_trigger_term_with_constr cg env c' tte2 in
                  match res' with
                    | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                    | None => None
                  end
            | None => None
          end
       else 
        let c' := curry_app c ca in interpret_trigger_term_with_constr cg env c' tte
(* Constant, inductives, constructors : 
only equalities up to universes in order to simplify 
the interpretation of our triggers *)
    | Constant cst _, TConstant o fl =>
        if matching_ref o (ConstRef cst) then Some (cons_option (interpret_flag c fl) [])
        else None
    | Ind ind _, TInd o fl =>
        if matching_ref o (IndRef ind) then Some (cons_option (interpret_flag c fl) [])
        else None
    | Constructor cstr _, TConstructor o fl =>
        if matching_ref o (ConstructRef cstr) then Some (cons_option (interpret_flag c fl) [])
        else None
    | Case _ (ty, _) _ t ca, TCase tte1 tte2 o fl =>
       let res := interpret_trigger_term_with_constr cg env ty tte1 in
        match res with
          | Some l => 
              let res' := interpret_trigger_term_with_constr cg env ty tte2 in
                match res' with
                  | Some l' =>
                      match o with
                        | Some lc =>
                            let branchs := Array.to_list ca in
                            let rec aux branchs lc acc :=
                              match branchs, lc with
                                | [], [] => Some acc
                                | x :: xs, y :: ys => 
                                    let res'' := interpret_trigger_term_with_constr cg env x y in
                                      match res'' with
                                        | Some l'' => aux xs ys (List.append l'' acc)
                                        | None => None
                                      end
                                | _, _ => None
                              end 
                            in 
                              match aux branchs lc [] with
                                | Some l'' => Some (cons_option (interpret_flag c fl) (List.append (List.append l l') l''))
                                | None => None
                              end
                        | None => Some (cons_option (interpret_flag c fl) (List.append l l'))
                      end
                  | None => None
                end
          | None => None
        end
    | Fix _ nbmut binds ca, TFix tte1 tte2 fl => 
        let ty := Binder.type (Array.get binds nbmut) in
        let res := interpret_trigger_term_with_constr cg env ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg env (Array.get ca nbmut) tte2 in
                  match res' with
                    | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                    | None => None
                  end
            | None => None
          end
    | CoFix nbmut binds ca, TCoFix tte1 tte2 fl =>
        let ty := Binder.type (Array.get binds nbmut) in
        let res := interpret_trigger_term_with_constr cg env ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg env (Array.get ca nbmut) tte2 in
                  match res' with
                    | Some l' => Some (cons_option (interpret_flag c fl) (List.append l l'))
                    | None => None
                  end
            | None => None
          end
    | _, TTerm c' fl =>
      if equal c c' then Some (cons_option (interpret_flag c fl) [])
      else None
    | _, TType t fl => 
        if equal (type c) t then Some (cons_option (interpret_flag t fl) [])
        else None
    | _, TTrigVar v fl => 
      let opt := interpret_trigger_var_with_constr cg env v c in
        match opt with
          | Some t => Some (cons_option (interpret_flag c fl) [])
          | None => None
        end
    | _, TAny fl => Some (cons_option (interpret_flag c fl) [])
    | _, _ => None
  end.

(* Intermediate interpretation whose return type is the pair 
between the hypothesis, the goal or the constr interpreted with 
the trigger and the result of the interpretation of this term with the trigger *)
Ltac2 interpret_trigger_is cg env a b : (constr * constr list) list  :=
  let a' := interpret_trigger_var cg env a in
    match a' with
      | Hyps hyps =>
          let rec aux cg h b := 
            match h with
              | [] => []
              | (x, y, z) :: xs => 
                  let opt := interpret_trigger_term_with_constr cg env z b in 
                    match opt with
                      | None => aux cg xs b
                      | Some l => 
                          let res := aux cg xs b in (Control.hyp x, l) :: res
                    end
            end in aux cg hyps b
      | Goal None => []
      | LetIns defs => 
          let rec aux cg h b := 
            match h with
              | [] => []
              | (x, y, z) :: xs => 
                  let opt := interpret_trigger_term_with_constr cg env y b in 
                    match opt with
                      | None => aux cg xs b
                      | Some l => 
                          let res := aux cg xs b in (Control.hyp x, l)::res
                    end
            end in aux cg defs b
      | Goal (Some x) => 
          let opt := interpret_trigger_term_with_constr cg env x b in 
            match opt with
              | None => []
              | Some y => [(x, y)]
            end
      | Constr c => 
          let opt := interpret_trigger_term_with_constr cg env c b in 
            match opt with
              | None => []
              | Some y => [(c, y)]
            end
    end. 

Ltac2 rec build_arrays_aux (l : constr list) :=
  match l with
    | [] => []
    | [x] => [Array.of_list [x]]
    | x :: xs => 
        let xs' := List.removelast xs in
        Array.of_list (x :: xs) :: build_arrays_aux (x :: xs') 
  end.

Ltac2 all_partial_apps (c : constr) (l : constr list) :=
  let arrs := build_arrays_aux l in
  List.append [c] (List.map (fun ar => make (App c ar)) arrs).

Ltac2 rec subterms (c : constr) : constr list :=
  match kind c with
    | Rel _ => [c]
    | Var _ => [c]
    | Meta _ => [c]
    | Evar _ ca =>
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in List.append [c] res'
    | Sort _ => [c]
    | Cast c1 _ c2 => List.append [c] (List.append (subterms c1) (subterms c2))
    | Prod bd c2 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms c1) (subterms c2))
    | Lambda bd c2 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms c1) (subterms c2))
    | LetIn bd c2 c3 =>
        let c1 := Binder.type bd in List.append [c] (List.append (subterms c1) (List.append (subterms c2) (subterms c3)))
    | App c1 ca => 
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        List.append (all_partial_apps c1 l) (List.append (subterms c1) res')
    | Constant _ _ => [c]
    | Ind _ _ => [c]
    | Constructor _ _ => [c]
    | Case _ (c1, _) _ c2 ca => 
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        List.append [c] (List.append (List.append (subterms c1) (subterms c2)) res')
    | Fix _ _ ba ca => 
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        let l' := Array.to_list ba in
        let res1 := List.map (fun x => subterms (Binder.type x)) l' in
        let res1' := List.flatten res1 in
        List.append [c] (List.append res' res1')
    | CoFix _ ba ca =>
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        let l' := Array.to_list ba in
        let res1 := List.map (fun x => subterms (Binder.type x)) l' in
        let res1' := List.flatten res1 in
        List.append [c] (List.append res' res1')
    | Proj _ _ c1 => List.append [c] (subterms c1)
    | Uint63 _ => [c]
    | Float _ => [c]
    | String _ => [c]
    | Array _ ca c1 c2 => 
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        List.append [c] (List.append (List.append (subterms c1) (subterms c2)) res')
  end.

Ltac2 closed_subterms c := List.filter is_closed (subterms c).

(* warning: no arguments returned for the interpretation of this trigger 
except the toplevel one *)
Ltac2 interpret_trigger_pred cg env a fl (p : constr -> bool) :=
  let a' := interpret_trigger_var cg env a in
    match a' with
      | Hyps hyps => 
          match List.find_all (fun (x, y, z) => p z) hyps with 
            | [] => []
            | l => (List.map (fun (x, y, z) => (cons_option (interpret_flag &x fl) [])) l)
          end 
      | LetIns defs =>
          match List.find_all (fun (x, y, z) => p y) defs with 
            | [] => []
            | l => (List.map (fun (x, y, z) => (cons_option (interpret_flag &x fl) [])) l)
          end 
      | Goal None => []
      | Goal (Some x) => if p x then [(cons_option (interpret_flag x fl) [])] else []
      | Constr c => if p c then [(cons_option (interpret_flag c fl) [])] else []
    end.

Ltac2 rec interpret_trigger_contains_aux cg env lc tf :=
    match lc with 
      | [] => []
      | x :: xs => 
        match interpret_trigger_term_with_constr cg env x tf with
          | None => interpret_trigger_contains_aux cg env xs tf
          | Some success => 
              let res := interpret_trigger_contains_aux cg env xs tf in
              success :: res
        end
    end. 

Ltac2 Type interpretation_state  := 
  (* subterms already computed in the goal *)
  { mutable subterms_coq_goal : (ident*constr list) list * (constr list) option ;
  (* hypotheses or/and goal considered *)
    mutable local_env : (ident * constr option * constr) list * constr option ; 
  (* are all the hypotheses considered ? *)
    mutable global_flag : bool ;
  (* name of the tactic interpreted *)
    mutable name_of_tac : string }.

Ltac2 look_for_subterms_hyps (id : ident) (s : (ident*constr list) list * (constr list) option) :=
  let (hyps, o) := s in
  let rec aux id hyps :=
    match hyps with
      | [] => None
      | (id', l) :: xs => 
        if Ident.equal id id' then Some l else aux id xs
    end in aux id hyps.

Ltac2 look_for_subterms_goal (s : (ident*constr list) list * (constr list) option) :=
  let (hyps, o) := s in
    match o with
      | None => None
      | Some lc => Some lc
    end.

Ltac2 interpret_trigger_contains 
  (it : interpretation_state)  (envref: env_triggers) tv tf : (constr * constr list list) list := 
  let scg := (it).(subterms_coq_goal) in
  let cg := (it).(local_env) in
  let env := (envref).(env_triggers) in
  let v := interpret_trigger_var cg env tv in
    match v with
      | Hyps hyps => 
          let rec aux cg h b := 
            match h with
              | [] => []
              | (x, y, z) :: xs => 
                  match look_for_subterms_hyps x scg with
                    | None =>
                        let lc := subterms z in
                        let (hyps, o) := scg in
                        let _ := (it).(subterms_coq_goal) := ((x, lc)::hyps, o) in
                        let l := interpret_trigger_contains_aux cg env lc b in 
                        let res := aux cg xs b in (Control.hyp x, l):: res
                    | Some lc => 
                        let l := interpret_trigger_contains_aux cg env lc b in 
                        let res := aux cg xs b in (Control.hyp x, l):: res
                    end
             end in aux cg hyps tf
      | LetIns defs => 
          let rec aux cg h b := 
            match h with
              | [] => []
              | (x, y, z) :: xs => 
                  match look_for_subterms_hyps x (it.(subterms_coq_goal)) with
                    | None =>
                        let lc := subterms y in
                        let (hyps, o) := it.(subterms_coq_goal) in
                        let _ := it.(subterms_coq_goal) := ((x, lc)::hyps, o) in
                        let l := interpret_trigger_contains_aux cg env lc b in 
                        let res := aux cg xs b in (Control.hyp x, l):: res
                    | Some lc => 
                        let l := interpret_trigger_contains_aux cg env lc b in 
                        let res := aux cg xs b in (Control.hyp x, l):: res
                    end
             end in aux cg defs tf
      | Goal None => []
      | Goal (Some g) =>
          match look_for_subterms_goal (it.(subterms_coq_goal)) with
            | None =>
              let lc := subterms g in
              let (hyps, o) := it.(subterms_coq_goal) in
              let _ := it.(subterms_coq_goal) := (hyps, Some lc) in
              let l := interpret_trigger_contains_aux cg env lc tf in 
                match l with
                  | [] => []
                  | x :: xs => [(g, l)]
                end
            | Some lc =>
                match interpret_trigger_contains_aux cg env lc tf with
                  | [] => []
                  | res => [(g, res)]
                end
          end
      | Constr c => 
          let lc := subterms c in
          let l := interpret_trigger_contains_aux cg env lc tf in 
            match l with
              | [] => []
              | _ => [(c, l)]
            end
    end.

Ltac2 interpret_trigger_always () := [[]].

Ltac2 interpret_trigger_never () := [].

Ltac2 rec cartesian_product (l1 : 'a list list) (l2 : 'a list list) :=
  match l1 with
    | [] => [] 
    | x :: xs => 
        let res := List.map (fun y => List.append x y) l2 in List.append res (cartesian_product xs l2) 
  end.

(* Ltac2 Eval cartesian_product [] [[1; 2]; [3; 4]].
Ltac2 Eval cartesian_product [[1; 2]; [3; 4]] []. *)

(* returns the list of arguments and their type of a tactic named [nametac] *)
Ltac2 find_args_of_tac alr_trig nametac : (string * (constr*constr) list) list :=
  List.filter (fun (x, y) => String.equal x nametac) ((alr_trig).(already_triggered)).

(* remove the old types registered for the list of arguments given to a tactic when there was a change
made by a side effect
for instance, there was H: T in the context, but H was cleared by some tactic and 
a new hypothesis H: T' was introduced *)

Ltac2 remove_old_assoc alr_trig nametac trm :=
  let res := find_args_of_tac alr_trig nametac in
  let res' := List.filter_out (fun (_, l) => List.exist (fun (x, y) => equal y trm) l) res in
  let res'' := List.filter_out (fun (x, y) => String.equal x nametac) ((alr_trig).(already_triggered)) in
  List.append res' res''.

(* among a list of list of pair between terms and their types, finds the corresponding type of a given constr *)
Ltac2 rec find_old_type 
  (llc : (constr * constr) list list)
  (c : constr) : constr option :=
  match llc with
    | [] => None
    | lc :: llc' => 
        let told := List.assoc_opt equal c lc in
        match told with
          | None => find_old_type llc' c 
          | Some told => Some told
        end
  end.

(* returns true when all the arguments given to a tactic have the same type as before
- if these arguments were never used returns false
- if they were used but one of them with a type which is not the current one (changed by a side-effect such as hypotheses renamings) returns false *)
(* 
 
                    let _ := (alr_trig).(already_triggered) := (nametac, List.combine l (List.map type l))::(remove_old_assoc alr_trig nametac x) in *)

Ltac2 same_types_as_before (l: constr list) alr_trig nametac :=
  let res := List.map (fun (x, y) => y) (find_args_of_tac alr_trig nametac) in
  let rec aux l' :=
    match l' with 
      | [] => true
      | x :: xs => 
          let t := type x in
          let told := find_old_type res x in
            match told with
              | None => false
              | Some told' => if equal t told' then aux xs else false
            end
      end in aux l.

Ltac2 filter_out_same_types (llc : constr list list) alr_trig nametac :=
List.filter_out (fun l => same_types_as_before l alr_trig nametac) llc. 

Ltac2 interpret_trigger
  (it : interpretation_state)  
  (env: env_triggers)
  (alr_trig: already_triggered) 
  (t : trigger) : (constr list) list :=
  let scg := (it).(subterms_coq_goal) in
  let cg := (it).(local_env) in
  let nametac := (it).(name_of_tac) in
  let rec interpret_trigger cg (env : env_triggers) alr_trig scg flag_letin nametac t := 
  match t with
    | TIs (a, fl) b =>
        let l := interpret_trigger_is cg ((env).(env_triggers)) a b in
        let res := (List.map (fun (x, l) => cons_option (interpret_flag x fl) l) l) in
        if flag_letin then res 
        else filter_out_same_types res alr_trig nametac
    | TPred (a, fl) p => 
        let l := interpret_trigger_pred cg ((env).(env_triggers)) a fl p in
        if flag_letin then l 
        else filter_out_same_types l alr_trig nametac
    | TContains (a, fl) b => 
        let l := interpret_trigger_contains it env a b in
        let res := (List.flatten (List.map (fun (x, l1) => List.map (fun l2 => cons_option (interpret_flag x fl) l2) l1) l)) in 
        if flag_letin then res 
        else filter_out_same_types res alr_trig nametac
    | TConj t1 t2 => 
        let res := interpret_trigger cg env alr_trig scg flag_letin nametac t1 in
        let res' := interpret_trigger cg env alr_trig scg flag_letin nametac t2 in
        let l := cartesian_product res res' in
        if flag_letin then l 
        else filter_out_same_types l alr_trig nametac           
    | TDisj t1 t2 => 
        let res := interpret_trigger cg env alr_trig scg flag_letin nametac t1 in
        let res' := interpret_trigger cg env alr_trig scg flag_letin nametac t2 in
        List.append res res'
(* warning: "not" is not involutive (intuitionnistic not) *)
    | TNot t' => 
        match interpret_trigger cg env alr_trig scg flag_letin nametac t' with
          | x :: xs => []
          | [] => [[]]
        end
    | TAlways => interpret_trigger_always ()
    | TNever => interpret_trigger_never ()
    | TMetaLetIn t1 ls t2 =>
       let it1 := interpret_trigger cg env alr_trig scg true nametac t1 in (* the result is a constr constr list, all the possibilities to bind the arguments *)
         let rec aux it1 cg env scg ls t2 :=
          match it1 with
            | [] => []
            | lc :: lcs => (*  List.iter (fun x => Message.print (Message.of_constr x)) lc ; *)
                let _ := bind_triggers env lc ls in
                let it2 := interpret_trigger cg env alr_trig scg flag_letin nametac t2 in
                let _ := env.(env_triggers) := List.skipn (List.length ls) (env.(env_triggers)) in
                match it2 with
                  | _ :: _ => 
                      if flag_letin then it2
                      else filter_out_same_types it2 alr_trig nametac
                  | [] => 
                      match aux lcs cg env scg ls t2 with
                        | [] => []
                        | l =>
                      if flag_letin then l
                      else filter_out_same_types l alr_trig nametac
                      end
                end
         end in aux it1 cg env scg ls t2
    end 
in List.filter (List.for_all is_closed) (interpret_trigger cg env alr_trig scg true nametac t).

(* Return the list of list of args instead of only a list, because the orchestrator will need it *)

(** Notations *)

Ltac2 Notation "AnyHyp" := TSomeHyp.

Ltac2 Notation "AnyHypProp" := TSomeHypProp.

Ltac2 Notation "triggered" "when" "(" tv(tactic) ")" "is" t(tactic) :=
  TIs (tv, NotArg) t.

Ltac2 Notation "triggered" "when" "(" tv(tactic) ")" "is" "(" t(tactic) ")"  "on" a(tactic) :=
  TIs (tv, a) t.

Ltac2 Notation "triggered" "when" "(" tv(tactic) ")" "contains" t(tactic) :=
  TContains (tv, NotArg) t.

Ltac2 Notation "triggered" "when" "(" tv(tactic) ")" "contains" "(" t(tactic) ")"  "on" a(tactic) :=
  TContains (tv, a) t.

Ltac2 Notation "tlet" ids(list1(ident, ";")) ":=" "(" t1(tactic) ")" "in" t2(tactic)  :=
  let ids := List.map Ident.to_string ids in
  TMetaLetIn t1 ids t2.

(* Ltac2 Eval (triggered when (TSomeHyp) is tDiscard).

Ltac2 Eval (triggered when (TSomeHyp) is (tDiscard) on NotArg).

Ltac2 Eval (triggered when (AnyHypProp) contains TTerm 'Set NotArg).

Ltac2 Eval (triggered when (AnyHypProp) contains (TTerm 'Set NotArg) on (Arg type)). *)

Ltac2 toto () :=
(tlet H := (triggered when (TSomeHyp) is (tDiscard) on (Arg (fun x => type x))) in 
triggered when (TNamed "H") is tDiscard).

(* TODO : a constr_to_trigger function to have nice notations for triggers *)




