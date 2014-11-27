Require Import Mtac2.
Import Mtac2Notations.

Notation "'intro' i" := (Mnu (fun i : nat => r <- evar _; abs i r)) (at level 0, i at next level).
(*
Tactic Notation "r" constr(n) := refine (eval n).
*)
Goal forall x : nat, x >= 0.
refine (eval (intro y)).


MyBinder : string -> (forall x : A, P x) -> (forall x : A, P x).
MyBinder s f = fun s=>f s.



refine (eval (nu x : nat, G <- evar Type; r <- evar G; abs x r)).

Definition isnotvar (x : nat) := eq_refl _ : eval (is_var x) = false.

Definition isvar := (eq_refl _ : eval (nu x:nat, is_var x) = true).

Definition isevar := eval (
  e <- evar nat;
  b <- is_evar e;
  mmatch (e, b) with
  | (0, true) =>
    b' <- is_evar e;
    match b' with 
    | false => ret true 
    | _ => raise exception 
    end
  end).