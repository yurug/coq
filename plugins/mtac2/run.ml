module TOps = Termops
module ROps = Reductionops


(** Notation conventions used in this file:
    - env stands for a local context.
    - sigma stands for the evar context.
*)

(** Module to create constructors given their coq name *)
module Constr = struct
  let mkConstr name = lazy (
    Globnames.constr_of_global
      (Nametab.global_of_path (Libnames.path_of_string name))
  )

  let isConstr = fun r c -> TOps.eq_constr (Lazy.force r) c
end

(** Module to create coq lists *)
module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let makeNil ty = Term.mkApp (Lazy.force mkNil, [| ty |])
  let makeCons t x xs = Term.mkApp (Lazy.force mkCons, [| t ; x ; xs |])

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons

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
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = Term.mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = Term.mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end


(** Module with names of Mtac2 *)
module MtacNames = struct
  let mtacore_name = "Coq.mtac2.Mtac2"
  let mtac_module_name = mtacore_name
  let mkLazyConstr = fun e-> Constr.mkConstr (mtac_module_name ^ "." ^ e)
  let mkConstr = fun e-> Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e))
  let mkT_lazy = lazy (mkConstr "Mtac2")

  let mkBase = mkLazyConstr "Mbase"
  let mkTele = mkLazyConstr "Mtele"
  let isBase = Constr.isConstr mkBase
  let isTele = Constr.isConstr mkTele

  let mkgBase = mkLazyConstr "Mgbase"
  let mkgTele = mkLazyConstr "Mgtele"
  let isgBase = Constr.isConstr mkgBase
  let isgTele = Constr.isConstr mkgTele

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
type data = Val of (Evd.evar_map * Term.constr) | Err of Term.constr

(** Monad for execution values *)
let (>>=) v g =
  match v with
  | Val v' -> g v'
  | _ -> v

let return s t = Val (s, t)

let fail t = Err t

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
      Some (sigma, evars, p, b)
    else if MtacNames.isTele patt then
      let c = nth 2 in
      let f = nth 4 in
      let (sigma', evar) = Evarutil.new_evar sigma env c in
      op_patt sigma' (Term.mkApp (f, [|evar|])) (evar :: evars)
    else
      None
  in op_patt sigma p []

let open_gpattern (env, sigma) p =
  let rec op_patt sigma p evars =
    let (patt, args) = ROps.whd_betadeltaiota_stack env sigma p in
    let nth = List.nth args in
    if MtacNames.isgBase patt then
      let hyps = nth 2 in
      let goal = nth 3 in
      let body = nth 4 in
      Some (sigma, evars, hyps, goal, body)
    else if MtacNames.isgTele patt then
      let b = nth 1 in
      let f = nth 2 in
      let (sigma', evar) = Evarutil.new_evar sigma env b in
      op_patt sigma' (Term.mkApp (f, [|evar|])) (evar :: evars)
    else
      None
  in op_patt sigma p []


(** Given a list of patterns [patts], it tries to unify the term [t]
    (with type [ty]) with each of the patterns. If it succeeds, then
    it returns the body of the pattern applied to the reflexivity
    proof that [t] is equal to itself. *)
let rec runmatch' (env, sigma as ctxt) t ty = function
  | [] -> Exceptions.block Exceptions.error_no_match
  | patt :: tail ->
    match open_pattern ctxt patt with
    | None -> Exceptions.block Exceptions.error_stuck
    | Some (sigma', evars, p, body) ->
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

(** [find_hypotheses] always selects the first hypothesis matching a given
 *  pattern *)
let rec find_hypotheses env rsigma evars hyps =
  (* hyps          = named_context
   * named_context = (id * constr option * constr) list *)
  let rec first_match sigma patt = function
    | [] -> None
    | (_name, _body, ty as hyp) :: tail ->
      let rsigma = ref sigma in
      if not (UnificationStrategy.unify rsigma env evars patt ty) then (
        match first_match sigma patt tail with
        | None -> None
        | Some (lst, sigma) -> Some (hyp :: lst, sigma)
      ) else
        Some (tail, !rsigma)
  in
  function
  | [] -> true
  | (_name, ty) :: hyp_patts ->
    match first_match !rsigma ty hyps with
    | None -> false
    | Some (lst, sigma) ->
      rsigma := sigma ;
      find_hypotheses env rsigma evars lst hyp_patts

let rec rungmatch' (_env, sigma as ctxt) (_evar, ev_info as egoal) = function
  | [] -> Exceptions.block Exceptions.error_no_match
  | patt :: tail ->
    (* We run all that follows in the env associated to the goal (read "evar")
       we want to inspect.
       That's a first approximation, it doesn't feel completly right. *)
    let env = Evd.evar_env ev_info in
    match open_gpattern (env, sigma) patt with
    | None -> Exceptions.block Exceptions.error_stuck
    | Some (sigma', evars, hyps, goal, body) ->
      let rsigma' = ref sigma' in
      let env_hyps  = Environ.named_context_of_val ev_info.Evd.evar_hyps in
      let hyp_patts =
        let lst = CoqList.to_list (env, sigma') hyps in
        List.map (fun patt -> 
          let (_constr, args) = ROps.whd_betadeltaiota_stack env sigma' patt in
          match args with
          | typ :: elt :: [] -> (elt, typ)
          | _ -> Exceptions.block Exceptions.error_stuck
        ) lst
      in
      (* FIXME: Will the following work?
       * Some elements of [evars] won't appear in the conclusion but only in the 
       * hypotheses. I'm afraid that the check performed in [UnificationStrategy]
       * will then fail. *)
      if not (UnificationStrategy.unify rsigma' env evars goal ev_info.Evd.evar_concl) then
        rungmatch' ctxt egoal tail
      else if not (find_hypotheses env rsigma' evars env_hyps hyp_patts) then
        rungmatch' ctxt egoal tail
      else
        let body = Evarutil.nf_evar !rsigma' body in
        (!rsigma', env, body)

let rungmatch ctx egoal patts =
  match CoqList.to_list_opt ctx patts with
  | None -> Exceptions.block Exceptions.error_stuck
  | Some patt_list -> rungmatch' ctx egoal patt_list

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
  let v, fx = if Term.isLambda f then
      let (arg, _, body) = Term.destLambda f in
      arg, body
    else
      Names.Anonymous, Term.mkApp(Vars.lift 1 f, [|Term.mkRel 1|])
  in
  match run' (Environ.push_rel (v, None, a) env, sigma) fx with
  | Val (sigma', e) ->
    if Int.Set.mem 1 (TOps.free_rels e) then
      Exceptions.block Exceptions.error_param
    else
      return sigma' (TOps.pop e)
  | Err e ->
    if Int.Set.mem 1 (TOps.free_rels e) then
      Exceptions.block Exceptions.error_param
    else
      fail (TOps.pop e)


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
let abs (env, sigma) a p x y =
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
        return sigma t
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

let rec run' (env, sigma as ctxt) t =
  let t = ROps.whd_betadeltaiota env sigma t in
  let (h, args) = Term.decompose_app t in
  let nth = List.nth args in
  let constr c =
    if Term.isConstruct h then
      let (m, ix) = Term.destConstruct h in
      if Names.eq_ind m (Term.destInd (Lazy.force MtacNames.mkT_lazy)) then
        ix
      else
        Exceptions.block Exceptions.error_stuck
    else
      Exceptions.block Exceptions.error_stuck
  in
  match constr h with
  | 1 -> (* ret *)
    return sigma (nth 1)

  | 2 -> (* bind *)
    run' ctxt (nth 2) >>= fun (sigma', v) ->
    let t' = Term.mkApp(nth 3, [|v|]) in
    run' (env, sigma') t'

  | 3 -> (* try *)
    begin
      match run' ctxt (nth 1) with
      | Val (sigma', v) -> return sigma' v
      | Err i ->
        let t' = Term.mkApp(nth 2, [|i|]) in
        run' ctxt t'
    end

  | 4 -> (* raise *)
    fail (nth 1)

  | 5 -> (* fix1 *)
    let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
    run' ctxt (runfix h [|a|] b s i f [|x|])

  | 6 -> (* fix 2 *)
    let a1, a2, b, s, i, f, x1, x2 =
      nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
    run' ctxt (runfix h [|a1; a2|] b s i f [|x1; x2|])

  | 7 -> (* fix 3 *)
    let a1, a2, a3, b, s, i, f, x1, x2, x3 =
      nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
    run' ctxt (runfix h [|a1; a2; a3|] b s i f [|x1; x2; x3|])

  | 8 -> (* match *)
    let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
    run' (env, sigma') body

  | 9 -> (* print *)
    Pp.msg_info (Printer.pr_constr_env env (nth 1));
    return sigma (Lazy.force CoqUnit.mkTT)

  | 10 -> (* nu *)
    let a, f = nth 0, nth 2 in
    runnu run' ctxt a f

  | 11 -> (* is_param *)
    let e = ROps.whd_betadeltaiota env sigma (nth 1) in
    if Term.isRel e then
      return sigma (Lazy.force CoqBool.mkTrue)
    else
      return sigma (Lazy.force CoqBool.mkFalse)

  | 12 -> (* abs *)
    let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
    abs ctxt a p x y

  | 13 -> (* evar *)
    let t = nth 0 in
    let (sigma', ev) = Evarutil.new_evar sigma env t in
    return sigma' ev

  | 14 -> (* is_evar *)
    let e = ROps.whd_betadeltaiota env sigma (nth 1) in
    if Term.isEvar e then
      return sigma (Lazy.force CoqBool.mkTrue)
    else
      return sigma (Lazy.force CoqBool.mkFalse)

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
    return sigma goals

  | 16 -> (* refine *)
    let goal = ROps.whd_betadeltaiota env sigma (nth 1) in
    let constr = nth 2 in
    begin match recover_goal sigma goal with
    | `Not_a_goal -> Exceptions.block "Not a refinable goal"
    | `Unknown_goal -> Exceptions.block "Unknown goal"
    | `Found (evar, args, ev_info) ->
      let () =
        match ev_info.Evd.evar_body with
        | Evd.Evar_empty -> ()
        | Evd.Evar_defined _ ->
          Exceptions.block "Cannot refine an already \"solved\" goal"
      in
      (* FIXME: we need to check that [constr] does not refer to things outside
       * the evar environment.
       * Is this done by [solve_simple_eq]? *)
      let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
      match
        Evarsolve.solve_simple_eqn (Evarconv.evar_conv_x ts) env sigma
          (None, (evar, args), constr)
      with
      | Evarsolve.Success sigma' ->
        assert (Evd.is_defined sigma' evar) ;
        let goal_set = Evarutil.undefined_evars_of_term sigma' constr in
        let goals =
          let ty = MtacNames.mkConstr "goal" in
          Evar.Set.fold (fun evar coq_list ->
              let fake_rel = Term.mkRel (Evar.repr evar) in
              let g = Term.mkApp (MtacNames.mkConstr "opaque", [| fake_rel |]) in
              CoqList.makeCons ty g coq_list
            ) goal_set (CoqList.makeNil ty)
        in
        return sigma' goals
      | Evarsolve.UnifFailure (em, err) ->
        (* FIXME: Not sure if using [Himsg] here is "clean". But it does give
         * some meaningful error messages. *)
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
      let (sigma', env, body) =
        rungmatch (env, sigma) ((evar, args), ev_info) (nth 2)
      in
      run' (env, sigma') body
    end

  | 18 ->
    let goal = ROps.whd_betadeltaiota env sigma (nth 0) in
    begin match recover_goal sigma goal with
    | `Not_a_goal -> Exceptions.block "Not a real goal??"
    | `Unknown_goal -> Exceptions.block "Unknown goal"
    | `Found (evar, _, ev_info) ->
      begin match ev_info.Evd.evar_body with
      | Evd.Evar_empty -> Pp.pperr (Pp.str "Goal: ")
      | Evd.Evar_defined cstr ->
        let pp_std = Printer.prterm cstr in
        Pp.pperr (Pp.str "Already solved with: ") ;
        Pp.pperrnl pp_std ;
        Pp.pperr (Pp.str "Goal was: ") ;
      end ;
      let pp_std = Printer.prterm ev_info.Evd.evar_concl in
      Pp.pperrnl pp_std ;
      Pp.flush_all () ;
      return sigma (Lazy.force CoqUnit.mkTT)
    end

  | _ ->
    Exceptions.block "I have no idea what is this Mtac2 construct that you have here"


let run (env, sigma) t  =
  match run' (env, sigma) (Evarutil.nf_evar sigma t) with
  | Err i ->
    Err i
  | Val (sigma', v) ->
    Val (sigma', Evarutil.nf_evar sigma' v)

