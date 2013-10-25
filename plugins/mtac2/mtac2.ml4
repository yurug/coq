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

let run_tac t i gl =
  let env = pf_env gl in
  let sigma = project gl in
  match run (env, sigma) t with
  | Val (sigma', v) ->
    tclTHEN (tclEVARS sigma') (letin_tac None (Name i) v None Locusops.nowhere) gl
  | Err e -> 
    raise (ExecFailed e);;

TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END
