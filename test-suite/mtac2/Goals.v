Require Import Mtac2.
Require Import List.
Import Mtac2Notations.

Definition iter {A B : Type} (f : A -> M B) :=
  mfix1 y (lst : list A) : M unit :=
    match lst with
    | nil => ret tt
    | cons x xs =>
      _ <- f x ;
      y xs
    end.

Goal forall x : nat, x = x.
intro.
run (
  lst <- Mgoals ;
  iter (fun y => Mrefine y (eq_refl x)) lst
) as t.
Qed.

(*

(* Problematic: once [run] finishes, the evars we got from [Mgoals] are "defined".
   They point to new evars. Why is that? *)

Goal forall x : nat, x = x.
run Mgoals as H.
run (iter (fun x => Mshow x) H) as t ; clear t.
intro x.
run (iter (fun x => Mshow x) H) as t ; clear t.
run Mgoals as H'.
run (iter (fun x => Mshow x) H') as t ; clear t.
run (iter (fun x => _ <- (Mshow x) ; Mrefine x (@eq_refl nat)) H') as t ; clear t.
*)