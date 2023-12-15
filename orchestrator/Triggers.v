From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Init.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Std.
From Ltac2 Require Import Env.
Import Unsafe.
Set Default Proof Mode "Classic".


Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 id (a : 'a) := a.

Ltac2 fst (x : 'a*'b) := let (y, _) := x in y.

Ltac2 snd (x : 'a*'b) := let (_, y) := x in y.

Ltac2 Type exn ::= [ NotClosed(string) ].

Ltac2 Type flag :=
  [ Arg (constr -> constr) | NotArg ]. (* TODO add int as position *)

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp | TNamed (string) ].

(* environment for named triggers variables, associated to a constr *)

Ltac2 Type env_triggers := 
{ mutable env_triggers : (string*constr) list }.

(* arguments on which the transformation was already applied *)

Ltac2 Type args_used :=
{ mutable args_used : constr list list }.

(* TODO ask the diff between meta and evar in Constr.v file *)

Ltac2 Type trigger_sort :=
[ TProp | TSet | TBigType].

(* warning:
does not handle universe hierarchy, native arrays, integers, 
projections or floats *)
Ltac2 Type rec trigger_term := [

(* follows the constr type *)
| TRel (int, flag)
| TVar (string option, flag) (* local variable or section variable *)
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
  ].

Ltac2 rec bind_triggers env (lc : constr list) (ls : string list) :=
  match lc, ls with
    | [], [] => ()
    | _, [] => fail "you have more terms to bind than binders' names"
    | [], _ => fail "you have more binders than terms to bind"
    | c :: lc, s :: ls => env.(env_triggers) := (s, c) :: (env.(env_triggers)) ; bind_triggers env lc ls
  end.

Ltac2 Type hyps_or_goal_or_constr := [
  | Hyps ((ident*constr option*constr) list) 
  | Goal (constr option)
  | Constr (constr) ].


Ltac2 interpret_trigger_var cg env (tv: trigger_var) :=
  let (hyps, g) := cg in
    match tv with
      | TSomeHyp => Hyps hyps
      | TGoal => Goal g
      | TNamed s => Constr (List.assoc String.equal s (env.(env_triggers)))
    end.

(* warning: does not take local defs (in Coq context) into account 
warning 2: returns only the first suitable hypothesis *)
Ltac2 interpret_trigger_var_with_constr cg env tv c :=
  let itv := interpret_trigger_var cg env tv in
    match itv with
      | Hyps hyps => 
          let l := List.find_all (fun (_, _, z) => equal z c) hyps in 
            match l with
              | [] => None
              | (_, _, z) :: xs => Some z 
            end
      | Goal (Some g) => if equal g c then Some g else None
      | Goal None => None
      | Constr c => Some c

    end.

Ltac2 destruct_eq (c : constr) :=
  match kind c with
    | App c' ca => 
        if equal c' '(@eq) then 
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
        if equal c' 'and then 
          let c1 := Array.get ca 0 in
          let c2 := Array.get ca 1 in
          Some (c1, c2)
        else None
    | _ => None
  end.

Ltac2 destruct_or (c : constr) :=
  match kind c with
    | App c' ca => 
        if equal c' 'or then 
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

Ltac2 matching_ref (o : string option) (r : reference) :=
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

Ltac2 rec interpret_trigger_term_with_constr
 cg env (c : constr) (tte : trigger_term) : constr list option:=
  match kind c, tte with
    | App _ _, TEq tte1 tte2 tte3 fl => 
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
        end
    | App _ _, TAnd tte1 tte2 fl => 
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
        end
    | App _ _, TOr tte1 tte2 fl => 
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
        end
(* De Brujin indexes: cannot be given as arguments to the tactic triggered. Otherwise 
the variable would escape its scope. *)
    | Rel n1, TRel n2 fl => if Int.equal n1 n2 then Some (cons_option (interpret_flag c fl) []) else None 
(* Local (or section) variables *)
    | Var id, TVar o fl => 
        match o with
          | Some s =>
              match Ident.of_string s with
                | Some id' =>
                    if Ident.equal id id' then Some (cons_option (interpret_flag c fl) [])
                    else None
                | None => None
              end
          | None => Some (cons_option (interpret_flag c fl) [])
          end
(* Sorts: we do not want to deal with universes, as we are afraid 
this may introduce difficulties which are unrelated to our main goal, 
but we want to distinguish between Prop, Set and Type_i, i >= 0 *)
    | Sort s, TSort ts fl =>
        match ts with
          | TProp => if equal c 'Prop then Some (cons_option (interpret_flag c fl) []) else None
          | TSet => if equal c 'Set then Some (cons_option (interpret_flag c fl) []) else None
          | TBigType => 
            if Bool.and (equal c 'Type) (Bool.neg (equal c 'Set))
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
    | Case _ ty _ t ca, TCase tte1 tte2 o fl =>
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

Ltac2 interpret_trigger_is cg env a b :=
  let a' := interpret_trigger_var cg env a in
    match a' with
      | Hyps hyps =>
          let rec aux cg h b := 
            match h with
              | [] => None
              | (x, y, z) :: xs => 
                  let opt := interpret_trigger_term_with_constr cg env z b in 
                    match opt with
                      | None => aux cg xs b
                      | Some l => 
                          let res := aux cg xs b in 
                            match res with
                              | None => Some [(Control.hyp x, l)]
                              | Some res' => Some ((Control.hyp x, l)::res')
                            end
                    end
            end in aux cg hyps b
      | Goal None => None
      | Goal (Some x) => 
          let opt := interpret_trigger_term_with_constr cg env x b in 
            match opt with
              | None => None
              | Some y => Some [(x, y)]
            end
      | Constr c => 
          let opt := interpret_trigger_term_with_constr cg env c b in 
            match opt with
              | None => None
              | Some y => Some [(c, y)]
            end
    end.

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
        List.append [c] (List.append (subterms c1) res')
    | Constant _ _ => [c]
    | Ind _ _ => [c]
    | Constructor _ _ => [c]
    | Case _ c1 _ c2 ca => 
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
    | Proj _ c1 => List.append [c] (subterms c1)
    | Uint63 _ => [c]
    | Float _ => [c]
    | Array _ ca c1 c2 => 
        let l := Array.to_list ca in
        let res := List.map subterms l in
        let res' := List.flatten res in 
        List.append [c] (List.append (List.append (subterms c1) (subterms c2)) res')
  end.

Ltac2 closed_subterms c := List.filter is_closed (subterms c).


(* warning: no arguments for this tactic except the toplevel one *)
Ltac2 interpret_trigger_pred cg env a fl (p : constr -> bool) :=
  let a' := interpret_trigger_var cg env a in
    match a' with
      | Hyps hyps => 
          match List.find_all (fun (x, y, z) => p z) hyps with 
            | [] => None
            | l => Some (List.map (fun (x, y, z) => (cons_option (interpret_flag &x fl) [])) l)
          end 
      | Goal None => None
      | Goal (Some x) => if p x then Some [(cons_option (interpret_flag x fl) [])] else None
      | Constr c => if p c then Some [(cons_option (interpret_flag c fl) [])] else None
    end.

Ltac2 rec interpret_trigger_contains_aux cg env lc tf :=
    match lc with 
      | [] => None
      | x :: xs => 
        match interpret_trigger_term_with_constr cg env x tf with
          | None => interpret_trigger_contains_aux cg env xs tf
          | Some success =>  
              match interpret_trigger_contains_aux cg env xs tf with
                | None => Some [success]
                | Some success' => Some (success::success')
              end
        end
    end.

Ltac2 Type subterms_coq_goal := { mutable subterms_coq_goal : (ident*constr list) list * (constr list) option }.

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

Ltac2 interpret_trigger_contains cg env (scg : subterms_coq_goal) tv tf : (constr * constr list list) list option:= 
  let v := interpret_trigger_var cg env tv in
    match v with
      | Hyps hyps => 
          let rec aux cg h b := 
            match h with
              | [] => None
              | (x, y, z) :: xs => 
                  match look_for_subterms_hyps x (scg.(subterms_coq_goal)) with
                    | None =>
                        let lc := subterms z in
                        let (hyps, o) := scg.(subterms_coq_goal) in
                        let _ := scg.(subterms_coq_goal) := ((x, lc)::hyps, o) in
                        let opt := interpret_trigger_contains_aux cg env lc b in 
                          match opt with
                            | None => aux cg xs b
                            | Some l => 
                                let res := aux cg xs b in
                                  match res with
                                    | Some res' => Some ((Control.hyp x, l):: res')
                                    | None => Some [(Control.hyp x, l)]
                                  end
                          end
                    | Some lc => 
                        let opt := interpret_trigger_contains_aux cg env lc b in 
                          match opt with
                            | None => aux cg xs b
                            | Some l =>
                                let res := aux cg xs b in
                                  match res with
                                    | Some res' => Some ((Control.hyp x, l):: res')
                                    | None => Some [(Control.hyp x, l)]
                                  end
                        end
                    end
             end in aux cg hyps tf
      | Goal None => None
      | Goal (Some g) =>
          match look_for_subterms_goal (scg.(subterms_coq_goal)) with
            | None =>
              let lc := subterms g in
              let (hyps, o) := scg.(subterms_coq_goal) in
              let _ := scg.(subterms_coq_goal) := (hyps, Some lc) in
              let opt := interpret_trigger_contains_aux cg env lc tf in 
                match opt with
                  | None => None
                  | Some l => Some [(g, l)]
                end
            | Some lc =>
                match interpret_trigger_contains_aux cg env lc tf with
                  | None => None
                  | Some res => Some [(g, res)]
                end
          end
      | Constr c => 
          let lc := subterms c in
          let opt := interpret_trigger_contains_aux cg env lc tf in 
            match opt with
              | None => None
              | Some l => Some [(c, l)]
            end
    end.

Ltac2 rec cartesian_product (l1 : 'a list list) (l2 : 'a list list) :=
  match l1 with
    | [] => [] 
    | x :: xs => 
        let res := List.map (fun y => List.append x y) l2 in List.append res (cartesian_product xs l2) 
  end.

(* Ltac2 Eval cartesian_product [[1; 2] ; [3; 4]] [[5; 6]; [7]]. *)

Ltac2 interpret_trigger cg env env_args scg (t : trigger) : constr list option :=
  let rec interpret_trigger cg env env_args scg flag_letin t := 
  match t with
    | TIs (a, fl) b =>
        match interpret_trigger_is cg env a b with
          | Some l => 
              let res := (List.map (fun (x, l) => cons_option (interpret_flag x fl) l) l) in
              if flag_letin then Some res 
              else let res' := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) res) in
              if Int.equal 0 (List.length res') then None else Some res'
          | None => None
        end
    | TPred (a, fl) p => 
        match interpret_trigger_pred cg env a fl p with
          | Some l => 
              if flag_letin then Some l 
              else let res := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) l) in
              if Int.equal 0 (List.length res) then None else Some res
          | None => None
        end
    | TContains (a, fl) b =>
        match interpret_trigger_contains cg env scg a b with
          | Some l => 
              let res := (List.flatten (List.map (fun (x, l1) => List.map (fun l2 => cons_option (interpret_flag x fl) l2) l1) l)) in 
              if flag_letin then Some res 
              else let res' := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) res) in
              if Int.equal 0 (List.length res') then None else Some res'
          | None => None
        end
    | TConj t1 t2 => 
      match interpret_trigger cg env env_args scg flag_letin t1 with
        | Some res => 
          match interpret_trigger cg env env_args scg flag_letin t2 with
            | Some res' => 
                let l := cartesian_product res res' in
                if flag_letin then Some l 
                else let l' := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) l) in
                if Int.equal 0 (List.length l') then None else Some l'
            | None => None
          end
        | None => None
      end              
    | TDisj t1 t2 => 
      match interpret_trigger cg env env_args scg flag_letin t1 with 
        | Some res => 
            match interpret_trigger cg env env_args scg flag_letin t1 with
               | None => Some res
               | Some res' => Some (List.append res res')
            end 
        | None => 
          match interpret_trigger cg env env_args scg flag_letin t2 with
            | Some res' => Some res'
            | None => None
          end
      end
(* warning: "not" works only with no arguments *)
    | TNot t' => 
        match interpret_trigger cg env env_args scg flag_letin t' with
          | Some _ => None
          | None => Some [[]]
        end
    | TMetaLetIn t1 ls t2 =>
       let it1 := interpret_trigger cg env env_args scg true t1 in (* the result is a constr constr list, all the possibilities to bind the arguments *)
         let rec aux it1 cg env scg ls t2 :=
          match it1 with
            | Some [] => None
            | Some (lc :: lcs) => 
                let _ := bind_triggers env lc ls in
                let it2 := interpret_trigger cg env env_args scg flag_letin t2 in 
                let _ := env.(env_triggers) := List.skipn (List.length ls) (env.(env_triggers)) in
                match it2 with
                  | Some l =>
                      if flag_letin then Some l
                      else let res := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) l) in
                      if Int.equal 0 (List.length res) then None else Some res
                  | None => 
                      match aux (Some lcs) cg env scg ls t2 with
                        | None => None
                        | Some l =>
                      if flag_letin then Some l
                      else let res := (List.filter_out (fun x => List.mem (List.equal equal) x (env_args.(args_used))) l) in
                      if Int.equal 0 (List.length res) then None else Some res 
                      end
                end
           | None => None
         end in aux it1 cg env scg ls t2
    end 
in match interpret_trigger cg env env_args scg false t with
    | None => None
    | Some l => let l' := List.hd l in if List.for_all is_closed l' then Some l' 
        else Control.throw (NotClosed "the interpretation of a trigger cannot return open terms")
  end.

(* TODO : improve the selection of args by designating their order (an integer) and an Ltac2 function f: constr -> constr.
eg : (1, id) (1, type) etc *) 




