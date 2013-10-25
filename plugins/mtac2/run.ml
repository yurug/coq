open List
open String

open Term
open Termops
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure
open Util
open Evarconv
open Libnames

let reduce_value = Tacred.compute

module Constr = struct
  let mkConstr name = lazy (Globnames.constr_of_global (Nametab.global_of_path (path_of_string name)))

  let isConstr = fun r c -> eq_constr (Lazy.force r) c
end

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

end

module Exceptions = struct

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e = mkApp(MtacNames.mkConstr "raise", [|mkProp; Lazy.force e|]) 

  let error_stuck = "Cannot reduce term, perhaps an opaque definition?"
  let error_no_match = "No pattern matches"

  let raise = Errors.error
end

module UnificationStrategy = struct

  (* since there may be delayed evars, and we don't want that, this function search for them *)
  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) -> 
      List.exists (fun e -> 
	Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let unify rsigma env evars t1 t2 =
    try
      let sigma = the_conv_x env t2 t1 !rsigma in
      rsigma := consider_remaining_unif_problems env sigma;
      List.length (find_pbs !rsigma evars) = 0 (* there should be no delayed evar *)
    with _ -> false

end

let mkT () = Lazy.force MtacNames.mkT_lazy

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons
end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end


type data = Val of (evar_map * constr) | Err of constr

let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

let return s t = Val (s, t)

let fail t = Err t


(** Given a pattern [p] and a list of evars *)
let rec open_pattern (env, sigma) p evars =
  let (patt, args) = whd_betadeltaiota_stack env sigma p in
  let nth = List.nth args in
  if MtacNames.isBase patt then
    let p = nth 3 in
    let b = nth 4 in
    Some (sigma, evars, p, b)
  else if MtacNames.isTele patt then
    let c = nth 2 in
    let f = nth 4 in
    let (sigma', evar) = Evarutil.new_evar sigma env c in
    open_pattern (env, sigma') (mkApp (f, [|evar|])) (evar :: evars)
  else
    None



let rec runmatch' (env, sigma as ctxt) t ty patts' i =
  let (patts, args) =  whd_betadeltaiota_stack env sigma patts' in
  if CoqList.isNil patts then
    Exceptions.raise Exceptions.error_no_match
  else if CoqList.isCons patts then
    match open_pattern ctxt (List.nth args 1) [] with
        Some (sigma', evars, p, body) ->
          let rsigma' = ref sigma' in
          begin
            if UnificationStrategy.unify rsigma' env evars p t  then
              let body = nf_evar !rsigma' body in
	      let body' = mkApp(body, [|CoqEq.mkAppEqRefl ty t|]) in
              (!rsigma', body')
            else
              runmatch' ctxt t ty (List.nth args 2) (i+1)
          end
      | None -> Exceptions.raise Exceptions.error_stuck
  else
    Exceptions.raise Exceptions.error_stuck


let runmatch (env, sigma as ctxt) t ty patts = 
  runmatch' ctxt t ty patts 0
   

let rec run' (env, sigma as ctxt) t =
  let t = whd_betadeltaiota env sigma t in
  let (h, args) = decompose_app t in
  let nth = List.nth args in
  let constr c = 
    if isConstruct h then
      let (m, ix) = destConstruct h in
      if eq_ind m (destInd (mkT ())) then
	ix
      else
	Exceptions.raise Exceptions.error_stuck
    else
      Exceptions.raise Exceptions.error_stuck
  in
  match constr h with
      | 1 -> (* ret *)        
	return sigma (nth 1)

      | 2 -> (* bind *)
	run' ctxt (nth 2) >>= fun (sigma', v) ->
	let t' = mkApp(nth 3, [|v|]) in
	run' (env, sigma') t'

      | 3 -> (* try *)
	begin
	match run' ctxt (nth 1) with
	  | Val (sigma', v) -> return sigma' v
	  | Err i -> 
            let t' = mkApp(nth 2, [|i|]) in
            run' ctxt t'
	end

      | 4 -> (* raise *)
	fail (nth 1)

      | 5 -> (* fix1 *)
	let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
	run_fix ctxt h [|a|] b s i f [|x|]

      | 6 -> (* fix 2 *)
	let a1, a2, b, s, i, f, x1, x2 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
	run_fix ctxt h [|a1; a2|] b s i f [|x1; x2|]

      | 7 -> (* fix 3 *)
	let a1, a2, a3, b, s, i, f, x1, x2, x3 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
	run_fix ctxt h [|a1; a2; a3|] b s i f [|x1; x2; x3|]

      | 8 -> (* match *)
	let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
	run' (env, sigma') body

      | _ ->
	Exceptions.raise "I have no idea what is this Mtac2 construct that you have here"

and run_fix (env, sigma as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c


let run (env, sigma) t  = 
  match run' (env, sigma) (nf_evar sigma t) with
    | Err i -> 
      Err i
    | Val (sigma', v) -> 
      Val (sigma', nf_evar sigma' v)


(*

let pretypeT pretype tycon env evdref lvar c =
    let t = 
      match tycon with
      | Some (_, ty) -> ty
      | _ ->
        let sigma, univ = new_univ_variable !evdref in
        evdref := sigma;
        e_new_evar evdref env (mkType univ)
    in
    let tt = mkApp(mkT (), [|t|]) in
    t, pretype (mk_tycon tt) env evdref lvar c

let pretype_run pretype coerce_to_tycon tycon env evdref lvar loc c =
   let t, r = pretypeT pretype tycon env evdref lvar c in
   let d = run (env, !evdref) r.uj_val in
   match d with
       | Val (evmap, e) ->
         evdref := evmap ;
         let r = { uj_val = e; uj_type = t } in
         coerce_to_tycon loc env evdref r tycon
       | Err e -> 
         Pretype_errors.error_user_exception loc env !evdref e

	 *)
