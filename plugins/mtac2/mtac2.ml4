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
    match run (env, sigma) t with
    | Val (sigma', v) ->
      Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS sigma'))
        (Tactics.letin_tac None (Name i) v None Locusops.nowhere)
    | Err e -> 
      raise (ExecFailed e)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END
