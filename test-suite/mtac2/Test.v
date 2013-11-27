Require Import Mtac2.
Import Mtac2Notations.
Require Import List.
Import ListNotations.


Program
Definition search {A} (x : A) :=
  mfix1 f (s : list A) : M (In x s) :=
    mmatch s with
    | [l r] l ++ r =>
      mtry 
        p <- f l;
        ret _
      with
      | exception => 
        p <- f r;
        ret _
      end
    | [s'] x :: s' => ret (in_eq _ _)
    | [y s'] y :: s' => 
      r <- f s';
      ret (in_cons _ _ _ r)
    | _ => raise exception
    end. 
Next Obligation.
intros. fold (In x (l++r)). apply in_or_app.
left; assumption.
Qed.
Next Obligation.
intros. fold (In x (l++r)). apply in_or_app.
right; assumption.
Qed.


Goal forall s (x y z : nat), In x (s++[z;y;x]).
intros.
run (search x (s ++ [z;y;x])) as H.
exact H.
Qed.

Goal forall s (x y z : nat), In x (s++[z;y;x]).
intros.
apply (eval (search _ _)).
Qed.
