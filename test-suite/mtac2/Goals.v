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

Goal forall x : nat, x >= 0.
intro.
destruct x.
run (
  Mgoals >>
  iter (fun g =>
    gmatch g with
    | {} 0 >= 0 => Mrefine g (Le.le_0_n 0)
    | [ z ] { z : nat } S z >= 0 => Mrefine g (Le.le_0_n (S z))
    end
  )
) as t.
Qed.

Goal forall (x : nat) (f: forall (A:Type), A -> A * A), (nat * nat) * (nat * nat).
Proof.
intros.
run (
  Mgoals >>
  iter (fun g =>
    gmatch g with
    | { x:nat , f : (forall (A:Type), A -> A * A) } (nat * nat) * (nat * nat) =>
      Mrefine g (f (nat * nat)%type (f nat x))
    end
  )
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
