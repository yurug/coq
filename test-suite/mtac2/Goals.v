Require Import Mtac2.
Require Import List.
Import Mtac2Notations.
Import ListNotations.

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

Goal forall x : nat, x >= 0.
intro.
destruct x.
run (
  lst <- Mgoals ;
  iter (fun g =>
    Mgmatch g [
      Mgbase nil (0 >= 0)(Mrefine g (Le.le_0_n 0)) ;
      Mgtele (fun z =>
        Mgbase [Named nat z] (S z >= 0) (Mrefine g (Le.le_0_n (S z))))
    ]
  ) lst
) as t.
Qed.

Lemma should_fail : forall x : nat, x = x.
Proof.
  intro.
  run (
    lst <- Mgoals ;
    iter (fun y => Mrefine y (eq_refl nat)) lst
  ) as t.
Qed.