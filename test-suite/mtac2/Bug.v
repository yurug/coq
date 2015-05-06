Require Import Mtac2.
Import Mtac2Notations.
Require Import String.

Definition Bug :=
    _ <- ret tt; (* dummy bind just to show the problem *)
    _ <- Mprint "hola"%string;
    @Mraise unit exception.

(* prints "hola" twice *)
Fail Let Bug := $(run (
    test <- Bug; ret test) as H; exact H)$.
  