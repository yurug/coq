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


(** Notation conventions used in this file:
    - env stands for a local context.
    - sigma stands for the evar context.
*)

(** Module to create constructors given their coq name *)
module Constr = struct
  let mkConstr name = lazy (
    Globnames.constr_of_global (Nametab.global_of_path (path_of_string name)))

  let isConstr = fun r c -> eq_constr (Lazy.force r) c
end

(** Module to create coq lists *)
module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons
end

(** Module to create equality type *) 
module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
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

end

(** There are two types of exception in Mtac2: those raised by the application
    and those coming from invalid operations (blocked terms). *)
module Exceptions = struct

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e = mkApp(MtacNames.mkConstr "raise", [|mkProp; Lazy.force e|]) 

  type reason = string
  let error_stuck : reason = "Cannot reduce term, perhaps an opaque definition?"
  let error_no_match : reason = "No pattern matches"

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
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) -> 
      List.exists (fun e -> 
	Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let no_delayed_evars sigma evars = List.length (find_pbs sigma evars) = 0

  let unify rsigma env evars t1 t2 =
    try
      let sigma = the_conv_x env t2 t1 !rsigma in
      rsigma := consider_remaining_unif_problems env sigma;
      no_delayed_evars !rsigma evars
    with _ -> false

end



(** The returning value is either a new evar context and a term, or
    an error *)
type data = Val of (evar_map * constr) | Err of constr

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
	op_patt sigma' (mkApp (f, [|evar|])) (evar :: evars)
    else
	None
  in op_patt sigma p []


(** Given a list of patterns [patts], it tries to unify the term [t]
    (with type [ty]) with each of the patterns. If it succeeds, then
    it returns the body of the pattern applied to the reflexivity
    proof that [t] is equal to itself. *)
let rec runmatch' (env, sigma as ctxt) t ty patts =
  let (patts, args) =  whd_betadeltaiota_stack env sigma patts in
  if CoqList.isNil patts then
    Exceptions.block Exceptions.error_no_match
  else if CoqList.isCons patts then
    let patt = List.nth args 1 in
    let tail = List.nth args 2 in
    match open_pattern ctxt patt with
        Some (sigma', evars, p, body) ->
          let rsigma' = ref sigma' in
          begin
            if UnificationStrategy.unify rsigma' env evars p t  then
		let body = nf_evar !rsigma' body in
		let body' = mkApp(body, [|CoqEq.mkAppEqRefl ty t|]) in
		(!rsigma', body')
            else
		runmatch' ctxt t ty tail
          end
	| None -> Exceptions.block Exceptions.error_stuck
  else
    Exceptions.block Exceptions.error_stuck
	

let runmatch (env, sigma as ctxt) t ty patts = 
  runmatch' ctxt t ty patts
    
(** To execute a fixpoint we just applied the function to the fixpoint of itself *)
let runfix h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  mkApp (f, Array.append [|fixf|] x)
  

let rec run' (env, sigma as ctxt) t =
  let t = whd_betadeltaiota env sigma t in
  let (h, args) = decompose_app t in
  let nth = List.nth args in
  let constr c = 
    if isConstruct h then
	let (m, ix) = destConstruct h in
	if eq_ind m (destInd (Lazy.force MtacNames.mkT_lazy)) then
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

    | _ ->
      Exceptions.block "I have no idea what is this Mtac2 construct that you have here"


let run (env, sigma) t  = 
  match run' (env, sigma) (nf_evar sigma t) with
    | Err i -> 
      Err i
    | Val (sigma', v) -> 
      Val (sigma', nf_evar sigma' v)

