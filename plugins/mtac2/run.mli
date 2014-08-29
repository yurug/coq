open Term
open Evd
open Environ

module LazyList : sig type 'a t end

module CMap : Map.S with type key = Term.constr

type lazy_map = constr LazyList.t CMap.t

type data = Val of (evar_map * lazy_map * constr) | Err of constr

val run : (env * evar_map) -> constr -> data Proofview.tactic


(*
(* debug *)
val run' : (env * evar_map) -> constr -> data Proofview.tactic
val runmatch' : Environ.env * Evd.evar_map -> 
  Term.constr -> Term.types -> Term.constr list -> Evd.evar_map * Term.constr
*)
