(*i camlp4deps: "grammar/grammar.cma" i*)

open Term
open Reductionops

open Names
open Refiner
open Tacexpr
open Tactics
open Tacticals
open Tacmach

open Run

open Proofview.Notations

DECLARE PLUGIN "mtac2_plugin"

exception ExecFailed of constr

let run_tac t i =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
(*    let open Proofview.Notations in *)
    run (env, sigma) t
    >>= function
    | Val (sigma', lazy_map, v) ->
      let sigma' =
        let rm_evar key _elt sigma =
          let evar, _ = Term.destEvar key in
          Evd.remove sigma evar
        in
        CMap.fold rm_evar lazy_map sigma'
      in
      (Proofview.Unsafe.tclEVARS sigma')
      <*> (Tactics.letin_tac None (Name i) v None Locusops.nowhere)
    | Err e -> 
      raise (ExecFailed e)
  end

(*
let run_refine (s, t) =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let mconcl = Term.mkApp (Lazy.force Run.MtacNames.mkT_lazy, [| concl |]) in
    let sigma =
      try 
	let ty = Retyping.get_type_of env s t in
	Evarconv.the_conv_x env mconcl ty s
      with Retyping.RetypeError _ -> s
	 | Evarconv.UnableToUnify _ -> s
    in
(*    let open Proofview.Notations in *)
    run (env, sigma) t
    >>= function
    | Val (sigma', lazy_map, v) ->
      let sigma' =
        let rm_evar key _elt sigma =
          let evar, _ = Term.destEvar key in
          Evd.remove sigma evar
        in
        CMap.fold rm_evar lazy_map sigma'
      in
      (Proofview.V82.tclEVARS sigma')
      <*> (Proofview.tclUNIT v)
    | Err e -> 
      raise (ExecFailed e)
  end
  *)
let run_effectful_tac t =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
(*    let open Proofview.Notations in *)
    run (env, sigma) t
    >>= function
    | Val (sigma', lazy_map, v) ->
      let sigma' =
        let rm_evar key _elt sigma =
          let evar, _ = Term.destEvar key in
          Evd.remove sigma evar
        in
        CMap.fold rm_evar lazy_map sigma'
      in
      (Proofview.Unsafe.tclEVARS sigma')
    | Err e -> 
      raise (ExecFailed e)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
(*  | [ "run_refine" open_constr(c) ] -> [ run_refine c ] *)
END

TACTIC EXTEND run_eff
  | [ "run_eff" constr(c) ] -> [ run_effectful_tac c ]
END
