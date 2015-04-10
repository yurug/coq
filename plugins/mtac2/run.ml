open Declarations

module TOps = Termops
module ROps = Reductionops

module CMap = Map.Make (struct
  type t = Constr.constr
  let compare x y = Constr.compare x y
end)

type lazy_map = Constr.constr Lazy_list.t CMap.t

(** Notation conventions used in this file:
    - env stands for a local context.
    - sigma stands for the evar context.
*)

(** Module to create constructors given their coq name *)
module MyConstr = struct
  let mkConstr name = lazy (
    Universes.constr_of_global
      (Nametab.global_of_path (Libnames.path_of_string name))
  )

  let isConstr = fun r c -> TOps.eq_constr (Lazy.force r) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)
end

(** Module to create coq lists *)
module CoqList = struct
  let mkNil  = MyConstr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = MyConstr.mkConstr "Coq.Init.Datatypes.cons"

  let makeNil ty = Term.mkApp (Lazy.force mkNil, [| ty |])
  let makeCons t x xs = Term.mkApp (Lazy.force mkCons, [| t ; x ; xs |])

  let isNil  = MyConstr.isConstr mkNil
  let isCons = MyConstr.isConstr mkCons

  let rec to_list (env, sigma as ctx) cterm =
    let (constr, args) = ROps.whd_betadeltaiota_stack env sigma cterm in
    if isNil constr then [] else
    if not (isCons constr) then invalid_arg "not a list" else
    let elt = List.nth args 1 in
    let ctail = List.nth args 2 in
    elt :: to_list ctx ctail

  let to_list_opt ctx cterm =
    try Some (to_list ctx cterm)
    with Invalid_argument _ -> None
end

(** Module to create equality type *)
module CoqEq = struct
  let mkEq = MyConstr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = MyConstr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = Term.mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = Term.mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqUnit = struct
  let ty = MyConstr.mkConstr "Coq.Init.Datatypes.unit"
  let mkTT = MyConstr.mkConstr "Coq.Init.Datatypes.tt"
end

module CoqBool = struct

  let mkTrue = MyConstr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = MyConstr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = MyConstr.isConstr mkTrue

end


(** Module with names of Mtac2 *)
module MtacNames = struct
  let mtacore_name = "Coq.mtac2.Mtac2"
  let mtac_module_name = mtacore_name
  let mkLazyConstr e = MyConstr.mkConstr (mtac_module_name ^ "." ^ e)
  let mkConstr e = Lazy.force (MyConstr.mkConstr (mtac_module_name ^ "." ^ e))
  let mkT_lazy = lazy (mkConstr "Mtac2")

  let mkLocalTele = mkLazyConstr "local_telescope"
  let mklTele = mkLazyConstr "lTele"

  let mkGoal = mkLazyConstr "Mgoal"
  let mkBase = mkLazyConstr "Mbase"
  let mkTele = mkLazyConstr "Mtele"
  let isBase = MyConstr.isConstr mkBase
  let isTele = MyConstr.isConstr mkTele
  let isGoal = MyConstr.isConstr mkGoal
end

(** There are two types of exception in Mtac2: those raised by the application
    and those coming from invalid operations (blocked terms). *)
module Exceptions = struct

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e =
    Term.mkApp (MtacNames.mkConstr "raise", [|Term.mkProp; Lazy.force e|])

  type reason = string
  let error_stuck : reason = "Cannot reduce term, perhaps an opaque definition?"
  let error_no_match : reason = "No pattern matches"
  let error_param = "Parameter appears in returned value"
  let error_abs = "Cannot abstract non variable"
  let error_abs_env = "Cannot abstract variable in a context depending on it"
  let error_abs_type = "Variable is appearing in the returning type"

  let block reason = Errors.error reason
end

(** For the moment, unification is done using the algorithm in
    Evarconv, but tomorrow we hope to have other options.
*)
module UnificationStrategy = struct

  (* Since there may be delayed evars, and we don't want that, this function
     searches for them. It is slow, but hopefully there shouldn't be many
     delayed evars.
  *)
  let find_pbs sigma evars =
    let (_, pbs) = Evd.extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e -> Termops.occur_term e c1 || Termops.occur_term e c2)
        evars
    ) pbs

  let no_delayed_evars sigma evars = List.length (find_pbs sigma evars) = 0

  let unify rsigma env evars t1 t2 =
    try
      let sigma = Evarconv.the_conv_x env t2 t1 !rsigma in
      rsigma := Evarconv.consider_remaining_unif_problems env sigma ;
      no_delayed_evars !rsigma evars
    with _ -> false
end



(** The returning value is either a new evar context and a term, or
    an error *)
type data = Val of (Evd.evar_map * lazy_map * Term.constr) | Err of Term.constr

(** Monad for execution values *)
let (>>=) v g = Proofview.tclBIND v (function Val v' -> g v' | _ -> v)

let return s m t = Proofview.tclUNIT (Val (s, m, t))

let fail t = Proofview.tclUNIT (Err t)

(** Given a pattern [p], it returns:
    - a new sigma context containing all the evars created,
    - the list of newly created evars,
    - the pattern with all the pattern variables replaced by evars,
    - the body of the pattern.
*)
let open_pattern (env, sigma) p =
  let rec op_patt sigma p evars =
    let (patt, args) = ROps.whd_betadeltaiota_stack env sigma p in
    let nth = List.nth args in
    if MtacNames.isBase patt then
      let p = nth 3 in
      let b = nth 4 in
      `Base (sigma, evars, p, b)
    else if MtacNames.isGoal patt then
      let hyps = nth 3 in
      let goal = nth 4 in
      let body = nth 5 in
      `Goal (sigma, evars, hyps, goal, body)
    else if MtacNames.isTele patt then
      let c = nth 2 in
      let f = nth 4 in
      let (sigma', evar) = Evarutil.new_evar env sigma c in
      op_patt sigma' (Term.mkApp (f, [|evar|])) (evar :: evars)
    else
      `None
  in op_patt sigma p []

(** Given a list of patterns [patts], it tries to unify the term [t]
    (with type [ty]) with each of the patterns. If it succeeds, then
    it returns the body of the pattern applied to the reflexivity
    proof that [t] is equal to itself. *)
let rec runmatch' (env, sigma as ctxt) t ty = function
  | [] -> Exceptions.block Exceptions.error_no_match
  | patt :: tail ->
    match open_pattern ctxt patt with
    | `None | `Goal _ -> Exceptions.block Exceptions.error_stuck
    | `Base (sigma', evars, p, body) ->
      let rsigma' = ref sigma' in
      if not (UnificationStrategy.unify rsigma' env evars p t) then
        runmatch' ctxt t ty tail
      else
        let body = Evarutil.nf_evar !rsigma' body in
        let body = Term.mkApp (body, [| CoqEq.mkAppEqRefl ty t |]) in
        (!rsigma', body)


let runmatch (env, sigma as ctxt) t ty patts =
  match CoqList.to_list_opt ctxt patts with
  | None -> Exceptions.block Exceptions.error_stuck
  | Some patt_list -> runmatch' ctxt t ty patt_list

let rec print_env lst =
  List.iter (fun (name, _body, ty) ->
    Pp.pperr (Names.Id.print name) ;
    Pp.pperr (Pp.str " : ") ;
    Pp.pperr (Printer.prterm ty) ;
    Pp.pperrnl (Pp.str "\n")
  ) lst ;
  Pp.pperr_flush ()

module HypPattern = struct
  let constr' c name : int option =
    if Term.isConstruct c then
      let (m, _) = Term.destConstruct c in
      if MyConstr.eq_ind m (Term.destInd name) then
        Some (snd m)
      else
        None
    else
      Exceptions.block Exceptions.error_stuck

  let destruct_sigT_or_unit ty =
    let fail () = Exceptions.block Exceptions.error_stuck in
    let local_tele = MtacNames.mkLocalTele in
    let sigma_ind = Universes.constr_of_global Coqlib.((build_sigma_type ()).typ) in
    if not (Term.isApp ty) then (
      (* it cannot be a sigma here *)
      if Term.isInd ty
        && MyConstr.eq_ind (Term.destInd ty) (Term.destInd (Lazy.force CoqUnit.ty))
      then
        `Unit
      else (* it's not even unit *)
        fail ()
    ) else
      let (ty_name, params) = Term.destApp ty in
      if not (Term.isInd ty_name) then fail () else
      let my_ind = Term.destInd ty_name in
      if MyConstr.eq_ind my_ind (Term.destInd sigma_ind) then
        `SigT (params.(0), params.(1))
      else if MyConstr.eq_ind my_ind (Term.destInd (Lazy.force local_tele)) then
        `LocalTele (params.(0), params.(1))
      else
        fail ()

  let constr c =
    match constr' c (MtacNames.mkConstr "hyp_pattern") with
    | None -> Exceptions.block Exceptions.error_stuck
    | Some ix -> ix

  (* See the matching Coq types in Mtac2.v *)
  type named = { elt : Term.constr ; ntyp : Term.constr }
  type local_telescope = {
    name : Names.name ;
    evar : Term.constr ; (* The evar we introduced *)
    typ  : Term.constr ;
  }

  (* See below for an explaination. *)
  type builder =
    Evd.evar_map ->
      Evd.evar_map * local_telescope list * named list * Term.constr list
      (* Remark of a guy looking back to the code 6 months later: the last
         element of the returned pair is used to construct the type of elements
         of the lazy list. This seems redundant. *)

  (* The OCaml twin of the Coq [hyp_pattern] type. (see Mtac2.v) *)
  type t =
    | Named of named
      (* [Enum] represent star patterns, when you have a pattern of the form
             [(H1, H2, ...)* as l]
         [l] will be the second parameter of the matching [Enum] value.
         The reason why the first parameter is not simply a [named list] is
         because we can't simply introduce evars in the ambiant environment
         (i.e. sigma) since we want to match multiple configurations.
         So instead we return a function which given a sigma will introduce the
         necessary evars and return a list of telescopes and a list of named. *)
    | Enum of builder * Term.constr

  let convert_named (env, sigma) named =
    let (_constr, args) = ROps.whd_betadeltaiota_stack env sigma named in
    match args with
    | ntyp :: elt :: [] -> Named { elt ; ntyp }
    | _ -> Exceptions.block Exceptions.error_stuck

  (** Given a Coq term of type [hyp_pattern] turns it in a term of type [t].
      See above. *)
  let convert (env, sigma as ctx) patt =
    let (c, args) = ROps.whd_betadeltaiota_stack env sigma patt in
    match constr c with
    | 1 -> (* Simple *)
      begin match args with
      | [ named ] -> convert_named ctx named
      | _ -> Exceptions.block Exceptions.error_stuck
      end

    | 2 -> (* Enum *)
      begin match args with
      | [ sig_typ ; lazy_list ] ->
        let builder sigma =
          let rec aux sigma typ =
            match destruct_sigT_or_unit typ with
            | `Unit -> sigma, [], [], []
            | `LocalTele (typ, lam) ->
              let (name, xty, body) = Term.destLambda lam in
              (* assert (Term.eq_constr ty xty) ; *)
              (* FIXME: the check above fails saying "Type != Type", I'm
               * assuming the universes are different but I don't understand
               * why. *)
              let (sigma', evar) = Evarutil.new_evar env sigma typ in
              let typ =
                (* questionable. *)
                ROps.whd_betadeltaiota env sigma' (Term.mkApp (lam, [| evar |]))
              in
              let sigma, teles, lst, families = aux sigma' typ in
              sigma, {name; evar; typ} :: teles, lst, lam :: families
            | `SigT (ty, lam) ->
              let (x, xty, body) = Term.destLambda lam in
              assert (Term.eq_constr ty xty) ;
              let (sigma', evar) = Evarutil.new_evar env sigma ty in
              let typ =
                (* questionable. *)
                ROps.whd_betadeltaiota env sigma' (Term.mkApp (lam, [| evar |]))
              in
              let sigma, teles, lst, families = aux sigma' typ in
              sigma, teles, { ntyp = ty ; elt = evar } :: lst, lam :: families
          in
          try aux sigma sig_typ
          with Invalid_argument "destruct_sigT_or_unit" ->
            Exceptions.block Exceptions.error_stuck
        in
        Enum (builder, lazy_list)
      | _ -> Exceptions.block Exceptions.error_stuck
      end

    | _ -> Exceptions.block Exceptions.error_stuck
end

let find_hypotheses lazy_map env sigma evars hyps patterns =
  let open Lazy_list in
  let rec all_matches sigma (term, typ as patt) =
    function
    | [] -> nil
    | (name, _body, ty as hyp) :: tail ->
      let rsigma = ref sigma in
      let other_configs = (* Ugly *)
        map (fun (s, matched, hyps) -> (s, matched, hyp :: hyps))
          (all_matches sigma patt tail)
      in
      if
        UnificationStrategy.unify rsigma env evars typ ty
        && UnificationStrategy.unify rsigma env evars term (Term.mkVar name)
      then
        cons (!rsigma, (name, ty), tail) other_configs
      else
        other_configs
  in
  let rec first_match sigma (term, typ as patt) =
    function
    | [] -> None
    | (_name, _body, ty as hyp) :: tail ->
      let rsigma = ref sigma in
      if
        UnificationStrategy.unify rsigma env evars typ ty
        && UnificationStrategy.unify rsigma env evars term (Term.mkVar _name)
      then
        Some (!rsigma, tail)
      else
        match first_match sigma patt tail with
        | None -> None
        | Some (sigma, remaining_hyps) -> Some (sigma, hyp :: remaining_hyps)
  in
  let rec helper lazy_map sigma hyps =
    let open HypPattern in
    function
    | [] ->
      Some (sigma, lazy_map)
    | Named { ntyp ; elt } :: hyp_patts ->
      begin match first_match sigma (elt, ntyp) hyps with
      | None -> Some (sigma, lazy_map)
      | Some (sigma, hyps) -> helper lazy_map sigma hyps hyp_patts
      end
    | [ Enum (gen, binder) ] ->
      let sigma', teles, patts, families = gen sigma in
      let families = List.rev families in
      let rec aux acc sigma hyps = function
        | [] -> return (sigma, acc)
        | { ntyp ; elt } :: hyp_patts ->
          all_matches sigma (elt, ntyp) hyps
          >>= fun (sigma, matched, hyps) ->
          aux ((matched, elt)::acc) sigma hyps hyp_patts
      in
      let lazy_list =
        let build teles (sigma, lst) =
          let sigT, existT =
            let x = Coqlib.build_sigma_type () in
            Universes.constr_of_global x.Coqlib.typ, Universes.constr_of_global (x.Coqlib.intro)
          in
          let local_telescope = Lazy.force_val MtacNames.mkLocalTele in
          let lTele = Lazy.force MtacNames.mklTele in
          let existT, sigT, families =
            List.fold_left
              (fun (acc, acc_ty, families) ((name, ty), evar) ->
                match families with
                | [] -> assert false
                | family :: families ->
                  (* FIXME: really necessary? *)
                  let t = Evd.existential_value sigma (Term.destEvar evar) in
                  let family = Termops.replace_term evar t family in
                  let acc = Termops.replace_term evar t acc in
                  Term.mkApp (existT, [| ty ; family ; Term.mkVar name ; acc |]),
                  Term.mkApp (sigT, [| ty ; family |]),
                  families
              )
              (Lazy.force CoqUnit.mkTT, Lazy.force CoqUnit.ty, families) lst
          in
          let (lTele, local_teles, _) =
            List.fold_left
              (fun (acc, acc_ty, families) {name; evar; typ} ->
                match families with
                | [] -> assert false
                | family :: families ->
                  let t = Evd.existential_value sigma (Term.destEvar evar) in
                  let family = Termops.replace_term evar t family in
                  let acc = Termops.replace_term evar t acc in
                  Term.mkApp (lTele, [| typ ; family ; t ; acc |]),
                  Term.mkApp (local_telescope, [| typ ; family |]),
                  families
              ) (existT, sigT, families) (List.rev teles)
          in
          lTele, local_teles
        in
        map (fun x -> build teles x) (aux [] sigma' hyps (List.rev patts))
      in
      let lazy_map = CMap.add binder (map fst lazy_list) lazy_map in
      Some (sigma, lazy_map)
    | Enum _ :: hyp_patts ->
      assert false (* TODO *)
  in
  helper lazy_map sigma hyps patterns


let rec rungmatch' lazy_map (_env, sigma as ctxt) (_evar, ev_info as egoal) =
  function
  | [] ->
    let env_hyps  = Environ.named_context_of_val ev_info.Evd.evar_hyps in
    print_env env_hyps ;
    Exceptions.block Exceptions.error_no_match
  | patt :: tail ->
    (* We run all that follows in the env associated to the goal (read "evar")
       we want to inspect.
       That's a first approximation, it doesn't feel completly right. *)
    let env = Evd.evar_env ev_info in
    match open_pattern (env, sigma) patt with
    | `None | `Base _ -> Exceptions.block Exceptions.error_stuck
    | `Goal (sigma', evars, hyps, goal, body) ->
      let rsigma' = ref sigma' in
      let env_hyps  = Environ.named_context_of_val ev_info.Evd.evar_hyps in
      let hyp_patts =
        let lst = CoqList.to_list (env, sigma') hyps in
        List.map (HypPattern.convert (env, sigma')) lst
      in
      if not (UnificationStrategy.unify rsigma' env evars goal ev_info.Evd.evar_concl) then
        rungmatch' lazy_map ctxt egoal tail
      else
        match find_hypotheses lazy_map env !rsigma' evars env_hyps hyp_patts with
        | None -> rungmatch' lazy_map ctxt egoal tail
        | Some (sigma, lazy_map) ->
          let body = Evarutil.nf_evar sigma body in
          (sigma, env, lazy_map, body)

let rungmatch lazy_map ctx egoal patts =
  match CoqList.to_list_opt ctx patts with
  | None -> Exceptions.block Exceptions.error_stuck
  | Some patt_list -> rungmatch' lazy_map ctx egoal patt_list

(** To execute a fixpoint we just applied the function to the fixpoint of itself *)
let runfix h a b s i f x =
  let fixf = Term.mkApp(h, Array.append a [|b;s;i;f|]) in
  Term.mkApp (f, Array.append [|fixf|] x)

(** Executes [f x] in the context [env] extended with [x : a]. Before
    returning it must check that [x] does not occur free in the
    returned value (or exception). *)
let runnu run' (env, sigma) a f =
  (* if [f] is a function, we use its variable to get the name, otherwise we
     apply [f] to a fresh new variable. *)
  let v, fx =
    if Term.isLambda f then
      let (arg, _, body) = Term.destLambda f in
      match arg with
      | Names.Anonymous -> arg, body
      | Names.Name var ->
        let v = Namegen.next_ident_away_in_goal var (TOps.ids_of_context env) in
        if v == var then arg, body else
        Names.Name v, TOps.replace_term (Term.mkVar var) (Term.mkVar v) body
    else
      Names.Anonymous, Term.mkApp(Vars.lift 1 f, [|Term.mkRel 1|])
  in
  Proofview.tclBIND (run' (Environ.push_rel (v, None, a) env, sigma) fx) (
    function
    | Val (sigma', lazy_map, e) ->
      if Int.Set.mem 1 (TOps.free_rels e) then
        Exceptions.block Exceptions.error_param
      else
        return sigma' lazy_map (TOps.pop e)
    | Err e ->
      if Int.Set.mem 1 (TOps.free_rels e) then
        Exceptions.block Exceptions.error_param
      else
        fail (TOps.pop e)
  )


(* checks that no variable in env to the right of i (that is, smaller
   to i) depends on i. *)
let noccurn_env env i =
  let rec noc n =
    if n = 1 then true
    else
      let (_, t, a) = Environ.lookup_rel (i-n+1) env in
      Vars.noccurn (n-1) a
      && (match t with None -> true | Some t' -> Vars.noccurn (n-1) t')
      && noc (n-1)
  in noc i

(* Performs substitution c{t/n}, increasing by one the free indices in [c].  *)
let mysubstn t n c =
  let rec substrec depth c = match Term.kind_of_term c with
    | Term.Rel k    ->
      if k<=depth then c
      else if k = depth+n then
        Vars.lift depth t
      else Term.mkRel (k+1)
    | _ -> Term.map_constr_with_binders succ substrec depth c in
  substrec 0 c

(** Abstract *)
let abs map (env, sigma) a p x y =
  let x = ROps.whd_betadeltaiota env sigma x in
  (* check if the type p does not depend of x, and that no variable
     created after x depends on it.  otherwise, we will have to
     substitute the context, which is impossible *)
  if Term.isRel x then
    let rel = Term.destRel x in
    if Vars.noccurn rel p then
      if noccurn_env env rel then
        let y' = mysubstn (Term.mkRel 1) rel y in
        let t = Term.mkLambda (Names.Anonymous, a, y') in
        return sigma map t
      else
        Exceptions.block Exceptions.error_abs_env
    else
      Exceptions.block Exceptions.error_abs_type
  else
    Exceptions.block Exceptions.error_abs

(* TODO: document *)
let recover_goal sigma goal_term =
  let _constr, params = Term.destApp goal_term in
  if not (Term.isEvar params.(0)) then `Not_a_goal else
  let evar, args = Term.destEvar params.(0) in
  try `Found (evar, args, Evd.find sigma evar)
  with Not_found -> `Unknown_goal


let dest_Case (env, sigma) t_type t =
  let nil = MyConstr.mkConstr "Coq.Init.Datatypes.nil" in
  let cons = MyConstr.mkConstr "Coq.Init.Datatypes.cons" in
  let mkCase = MtacNames.mkConstr "mkCase" in
  let dyn = MtacNames.mkConstr "dyn" in
  let mkDyn = MtacNames.mkConstr "Dyn" in
  try
    let t = ROps.whd_betadeltaiota env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let branch_dyns = Array.fold_left (
      fun l t -> 
        let dyn_type = Retyping.get_type_of env sigma t in
        Term.applist (Lazy.force cons, [dyn; Term.applist (mkDyn, [dyn_type; t]); l])
      ) (Lazy.force nil) branches in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    (* (sigma, (Term.applist(mkCase, [t_type; t; ind_type; discriminant; branch_dyns]))) *)
    (sigma, (Term.applist(mkCase, 
      [ind_type; discriminant; t_type;
       Term.applist(mkDyn, [return_type_type; return_type]); 
       branch_dyns
      ])
      )
      )
  with
   | Not_found -> 
        Exceptions.block "Something specific went wrong. TODO: find out what!"
   | Term.DestKO -> 
        Exceptions.block "This is not a case construct."
   | _ -> 
        Exceptions.block "Something not so specific went wrong."

let make_Case (env, sigma) case =
  let map = MyConstr.mkConstr "List.map" in
  let elem = MtacNames.mkConstr "elem" in
  let mkDyn = MtacNames.mkConstr "Dyn" in
  let case_ind = MtacNames.mkConstr "case_ind" in
  let case_val = MtacNames.mkConstr "case_val" in
  let case_type = MtacNames.mkConstr "case_type" in
  let case_return = MtacNames.mkConstr "case_return" in
  let case_branches = MtacNames.mkConstr "case_branches" in
  let repr_ind = Term.applist(case_ind, [case]) in
  let repr_val = Term.applist(case_val, [case]) in
  let repr_val_red = ROps.whd_betadeltaiota env sigma repr_val in
  let repr_type = Term.applist(case_type, [case]) in
  let repr_return = Term.applist(case_return, [case]) in
  let repr_return_unpack = Term.applist(elem, [repr_return]) in
  let repr_return_red = ROps.whd_betadeltaiota env sigma repr_return_unpack in
  let repr_branches = Term.applist(case_branches, [case]) in
  let repr_branches_list = CoqList.to_list (env, sigma) repr_branches in
  let repr_branches_dyns = 
      List.map (fun t -> Term.applist(elem, [t])) repr_branches_list in
  let repr_branches_red =       
    List.map (fun t -> ROps.whd_betadeltaiota env sigma t) repr_branches_dyns in
  let t_type, l = Term.decompose_app (ROps.whd_betadeltaiota env sigma repr_ind) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind ((mind, ind_i), _) -> 
      let mbody = Environ.lookup_mind mind env in
      let ind = Array.get mbody.mind_packets ind_i in
      let case_info = Inductiveops.make_case_info env (mind, ind_i)
      Term.LetPatternStyle in
      let match_term = Term.mkCase (case_info, repr_return_red, repr_val_red,
      Array.of_list (List.rev repr_branches_red)) in
      let match_type = Retyping.get_type_of env sigma match_term in
      (sigma, Term.applist(mkDyn, [match_type;  match_term]))
    | _ -> assert false
  else
    Exceptions.block "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  let t_type, l = Term.decompose_app (ROps.whd_betadeltaiota env sigma t) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind ((mind, ind_i), _) -> 
      let mbody = Environ.lookup_mind mind env in
      let ind = Array.get (mbody.mind_packets) ind_i in
      let dyn = MtacNames.mkConstr "dyn" in
      let mkDyn = MtacNames.mkConstr "Dyn" in
      let l = Array.fold_left 
          (fun l i ->
              let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
              let coq_constr = Term.applist (mkDyn, [CoqList.makeNil dyn]) in (* what is the sense of this line? it's being shadowed in the next one *)
              let coq_constr = Term.mkConstruct constr in
	      let ty = Retyping.get_type_of env sigma coq_constr in 
              let dyn_constr = Term.applist (mkDyn, [ty; coq_constr]) in
              CoqList.makeCons dyn dyn_constr l 
          )
              (CoqList.makeNil dyn )  
          (* this is just a dirty hack to get the indices of constructors *)
          (Array.mapi (fun i t -> i+1) ind.mind_consnames)
      in  
      (sigma, l)
    | _ -> assert false
  else
    Exceptions.block "The argument of Mconstrs is not an inductive type"




let rec run' lazy_map (env, sigma as ctxt) t =
  let t = ROps.whd_betadeltaiota env sigma t in
  let (h, args) = Term.decompose_app t in
  let nth = List.nth args in
  let constr c =
    if Term.isConstruct c then
      let ((m, ix), _) = Term.destConstruct c in
      if Names.eq_ind m (fst (Term.destInd (Lazy.force MtacNames.mkT_lazy))) then
        ix
      else
        Exceptions.block Exceptions.error_stuck
    else
      Exceptions.block Exceptions.error_stuck
  in
  match constr h with
  | 1 -> (* ret *)
    return sigma lazy_map (nth 1)

  | 2 -> (* bind *)
    run' lazy_map ctxt (nth 2) >>= fun (sigma', lazy_map, v) ->
    let t' = Term.mkApp(nth 3, [|v|]) in
    run' lazy_map (env, sigma') t'

  | 3 -> (* try *)
    Proofview.tclBIND (run' lazy_map ctxt (nth 1)) (
      function
      | Val (sigma', lazy_map, v) -> return sigma' lazy_map v
      | Err i ->
        let t' = Term.mkApp(nth 2, [|i|]) in
        run' lazy_map ctxt t'
    )

  | 4 -> (* raise *)
    fail (nth 1)

  | 5 -> (* fix1 *)
    let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
    run' lazy_map ctxt (runfix h [|a|] b s i f [|x|])

  | 6 -> (* fix 2 *)
    let a1, a2, b, s, i, f, x1, x2 =
      nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
    run' lazy_map ctxt (runfix h [|a1; a2|] b s i f [|x1; x2|])

  | 7 -> (* fix 3 *)
    let a1, a2, a3, b, s, i, f, x1, x2, x3 =
      nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
    run' lazy_map ctxt (runfix h [|a1; a2; a3|] b s i f [|x1; x2; x3|])

  | 8 -> (* match *)
    let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
    run' lazy_map (env, sigma') body

  | 9 -> (* print *)
    Pp.pperrnl (Printer.pr_constr_env env sigma (nth 1));
    Pp.flush_all () ;
    return sigma lazy_map (Lazy.force CoqUnit.mkTT)

  | 10 -> (* nu *)
    let a, f = nth 0, nth 2 in
    runnu (run' lazy_map) ctxt a f

  | 11 -> (* is_param *)
    let e = ROps.whd_betadeltaiota env sigma (nth 1) in
    if Term.isRel e then
      return sigma lazy_map (Lazy.force CoqBool.mkTrue)
    else
      return sigma lazy_map (Lazy.force CoqBool.mkFalse)

  | 12 -> (* abs *)
    let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
    abs lazy_map ctxt a p x y

  | 13 -> (* evar *)
    let t = nth 0 in
    let (sigma', ev) = Evarutil.new_evar env sigma t in
    return sigma' lazy_map ev

  | 14 -> (* is_evar *)
    let e = ROps.whd_betadeltaiota env sigma (nth 1) in
    if Term.isEvar e then
      return sigma lazy_map (Lazy.force CoqBool.mkTrue)
    else
      return sigma lazy_map (Lazy.force CoqBool.mkFalse)

  | 15 -> (* goals *)
    (* We could get goals directly from the [fold_undefined] but the goal order
       would be reversed, which is sad.
    
       N.B. the evar_info contains the origin of the evar, which can be
       [GoalEvar] and we might want to keep only those. But we appear to receive
       [InternalHole] where I would expect the [GoalEvar] ...  *)
    let evars = Evd.fold_undefined (fun ev _info acc -> ev :: acc) sigma [] in
    let goals =
      let ty = MtacNames.mkConstr "goal" in
      List.fold_left (fun coq_list evar ->
        let ev_info = Evd.find sigma evar in
        let args =
          Context.instance_from_named_context
            (Environ.named_context_of_val ev_info.Evd.evar_hyps)
        in
        let args = Array.of_list args in
        let evar = Term.mkEvar (evar, args) in
        let g = Term.mkApp (MtacNames.mkConstr "opaque", [| evar |]) in
        CoqList.makeCons ty g coq_list
      ) (CoqList.makeNil ty) evars
    in
    return sigma lazy_map goals

  | 16 -> (* refine *)
    let goal = ROps.whd_betadeltaiota env sigma (nth 1) in
    let constr = nth 2 in
    begin match recover_goal sigma goal with
    | `Not_a_goal -> Exceptions.block "Not a refinable goal"
    | `Unknown_goal -> Exceptions.block "Unknown goal"
    | `Found (evar, args, ev_info) ->
      let () =
        (* That could be relaxed. *)
        match ev_info.Evd.evar_body with
        | Evd.Evar_empty -> ()
        | Evd.Evar_defined _ ->
          Exceptions.block "Cannot refine an already \"solved\" goal"
      in
      let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
      match
        Evarsolve.solve_simple_eqn (Evarconv.evar_conv_x ts) ~choose:true env sigma
          (None, (evar, args), constr)
      with
      | Evarsolve.Success sigma' ->
        let sigma' = Evarconv.consider_remaining_unif_problems env ~ts sigma' in
        assert (Evd.is_defined sigma' evar) ;
        let goal_set = Evarutil.undefined_evars_of_term sigma' constr in
        let goals, comb =
          let ty = MtacNames.mkConstr "goal" in
          Evar.Set.fold (fun evar (coq_list, comb) ->
            let ev_info =
              try Evd.find sigma' evar
              with Not_found ->
                Exceptions.block (Evd.string_of_existential evar ^ " wasn't found in sigma")
            in
            let args =
              (* Context.instance_from_named_context *)
              List.map (fun (id,_,_) -> Term.mkVar id)
                (Evd.evar_filtered_context ev_info)
            in
            let args = Array.of_list args in
            let evar_trm = Term.mkEvar (evar, args) in
            let g = Term.mkApp (MtacNames.mkConstr "opaque", [|evar_trm|]) in
            CoqList.makeCons ty g coq_list, evar :: comb
          ) goal_set (CoqList.makeNil ty, [])
        in
        Proofview.tclTHEN (Proofview.register_goals comb) (return sigma' lazy_map goals)
      | Evarsolve.UnifFailure (em, err) ->
        let existential = Term.mkEvar (evar, args) in
        let explanation =
          Himsg.explain_pretype_error env em
            (Pretype_errors.CannotUnify (existential, constr, Some err))
        in
        Errors.alreadydeclared explanation
    end

  | 17 -> (* gmatch *)
    let goal = ROps.whd_betadeltaiota env sigma (nth 1) in
    begin match recover_goal sigma goal with
    | `Not_a_goal -> Exceptions.block "Not a matchable goal"
    | `Unknown_goal -> Exceptions.block "Unknown goal"
    | `Found (evar, args, ev_info) ->
      let (sigma', env, lazy_map, body) =
        rungmatch lazy_map (env, sigma) ((evar, args), ev_info) (nth 2)
      in
      run' lazy_map (env, sigma') body
    end

  | 18 -> (* next *)
    let ty = ROps.whd_betadeltaiota env sigma (nth 0) in
    let lazy_ty = Term.mkApp (MtacNames.mkConstr "LazyList", [|ty|]) in
    let ret_ty =
      Term.mkApp (
        Lazy.force (MyConstr.mkConstr "Coq.Init.Datatypes.prod"),
        [| ty ; lazy_ty |]
      )
    in
    let ll = nth 1 in
    begin match try Some (CMap.find ll lazy_map) with Not_found -> None with
    | None -> Exceptions.block "Unknown lazy list"
    | Some lazy_list ->
      match Lazy_list.destruct lazy_list with
      | None -> 
        return sigma lazy_map (
          Term.mkApp (
            (Lazy.force (MyConstr.mkConstr "Coq.Init.Datatypes.None")), [| ret_ty |]
          )
        )
      | Some (elt, lazy_list') ->
        let sigma, key = Evarutil.new_evar env sigma lazy_ty in
        let map = CMap.add key lazy_list' lazy_map in
        let elt = 
          Term.mkApp (
            Lazy.force (MyConstr.mkConstr "Coq.Init.Datatypes.Some"), [|
              ret_ty ;
              Term.mkApp (
                Lazy.force (MyConstr.mkConstr "Coq.Init.Datatypes.pair"),
                [| ty ; lazy_ty ; elt ; key|]
              )
            |]
          )
        in
        return sigma map elt
    end

  | 19 -> (* show *)
    let goal = ROps.whd_betadeltaiota env sigma (nth 0) in
    begin match recover_goal sigma goal with
    | `Not_a_goal -> Exceptions.block "Not a real goal??"
    | `Unknown_goal -> Exceptions.block "Unknown goal"
    | `Found (evar, _, ev_info) ->
      Pp.pperrnl (Pp.str "==================================================") ;
      let () =
        let env_hyps  = Environ.named_context_of_val ev_info.Evd.evar_hyps in
        print_env env_hyps
      in
      begin match ev_info.Evd.evar_body with
      | Evd.Evar_empty -> Pp.pperr (Pp.str "Goal: ")
      | Evd.Evar_defined cstr ->
        let x = Printer.prterm cstr in
        let cstr = ROps.nf_evar sigma cstr in
        let y = Printer.prterm cstr in
        Pp.pperr Pp.(str "Already solved with: " ++ y ++ str " (was: ") ;
        Pp.pperr Pp.(x ++ str ")\n") ;
        Pp.pperr (Pp.str "Goal was: ") ;
      end ;
      let pp_std = Printer.prterm ev_info.Evd.evar_concl in
      Pp.pperrnl pp_std ;
      Pp.pperrnl (Pp.str "==================================================") ;
      Pp.flush_all () ;
      return sigma lazy_map (Lazy.force CoqUnit.mkTT)
    end

  | 20 -> (* dest case *) 
    let t_type = nth 0 in
    let t = nth 1 in
    let (sigma', case) = dest_Case (env, sigma) t_type t in
    return sigma' lazy_map case

  | 21 -> (* get constrs *) 
    let t = nth 1 in
    let (sigma', constrs) = get_Constrs (env, sigma) t in
    return sigma' lazy_map constrs

  | 22 -> (* make case *) 
    let case = nth 0 in
    let (sigma', case) = make_Case (env, sigma) case in
    return sigma' lazy_map case

  | _ ->
    Exceptions.block "I have no idea what is this Mtac2 construct that you have here"


let run (env, sigma) t  =
  let lazy_map = CMap.empty in
  Proofview.tclBIND (run' lazy_map (env, sigma) (Evarutil.nf_evar sigma t)) (
    function
    | Err i -> fail i
    | Val (sigma', lazy_map, v) ->
      return sigma' lazy_map (Evarutil.nf_evar sigma' v)
  )

