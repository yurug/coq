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

exception ExecFailed of constr

let run_tac t i =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let open Proofview.Notations in
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
      <*> (Tactics.letin_tac None (Name i) v None Locusops.nowhere)
    | Err e -> 
      raise (ExecFailed e)
  end

let run_effectful_tac t =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let open Proofview.Notations in
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
    | Err e -> 
      raise (ExecFailed e)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
  | [ "run_eff" constr(c) ] -> [ run_effectful_tac c ]
END
