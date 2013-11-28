Require Import Mtac2.
Import Mtac2Notations.


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