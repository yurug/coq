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


(** Defines [eval f] to execute after elaboration the Mtactic [f]. 
    It allows e.g. [rewrite (eval f)]. *)
Class runner A  (f : M A) := { eval : A }.
Arguments runner {A} _.
Arguments Build_runner {A} _ _.
Arguments eval {A} _ {_}.

Ltac run_matching f :=
  refine (Build_runner f _);
  let H := fresh "H" in
  run f as H;
  exact H.

Hint Extern 20 (runner ?f) => (run_matching f)  : typeclass_instances.

Goal forall s (x y z : nat), In x (s++[z;y;x]).
intros.
apply (eval (search _ _)).
Qed.
