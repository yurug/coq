open Term
open Evd
open Environ

type data = Val of (evar_map * constr) | Err of constr

val run : (env * evar_map) -> constr -> data Proofview.tactic


(* debug *)
val run' : (env * evar_map) -> constr -> data Proofview.tactic
val runmatch' : Environ.env * Evd.evar_map -> 
  Term.constr -> Term.types -> Term.constr list -> Evd.evar_map * Term.constr
