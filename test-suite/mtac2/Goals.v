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
    | [ z ] { z ::: nat } S z >= 0 => Mrefine g (Le.le_0_n (S z))
    end
  )
) as t.
Qed.

Goal forall (A C B : Type) (a : A) (b : B) (c : C), A.
Proof.
  intros.
  run (
    Mgoals >>
    iter (fun g =>
      gmatch g with
      | [ X x ] { X ::: Type , x ::: X } A =>
        _ <- Mprint X ;
        Mprint x
      end
    )
  ) as H.
Admitted.








(*
Goal forall (A B C : Type) (a : A) (b : B) (c : C), B.
Proof.
  intros.
  set (I := fun g =>
      gmatch g with
      | [ (Res:Type) l ] { < { U:Type & { _ : U & unit } } >* as l }
                         Res =>
        (mfix1 y (lst : LazyList { U : Type & { _ : U & unit } }) : M unit :=
          res <- Mnext lst ;
         _ <- Mprint res ;
          mmatch res with
          | None => Mprint 0
          | [ x l' ] Some (x, l') =>
            mmatch x return M unit with
            | [ m ] (@existT Type (fun U : Type => {_ : U & unit}) m
      (@existT Type (fun _ : C => unit) C tt)) =>
              _ <- Mrefine g m ;
              ret tt
            | _ =>
              y l'
            end
          end
        ) l
      | _ => ret tt
      end
    ).
  Set Printing Implicit.
  run (
    Mgoals >>
    iter I
  ) as H.
  Show Proof.
Qed.

Goal forall x y : nat, x >= 0.
intros x y.
destruct x.
run (
  Mgoals >>
  iter (fun g =>
    gmatch g with
    | {} 0 >= 0 => Mrefine g (Le.le_0_n 0)
    | [ z ] { z ::: nat } S z >= 0 => Mrefine g (Le.le_0_n (S z))
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
    | { x ::: nat , f ::: (forall (A:Type), A -> A * A) } (nat * nat) * (nat * nat) =>
      Mrefine g (f (nat * nat)%type (f nat x))
    end
  )
) as t.
Qed.

Definition wait :=
  mfix1 Y (n : nat) : M unit :=
    _ <- Mprint n ;
    match n with
    | O => ret tt
    | S n => Y n
    end.

Goal forall (x : nat), nat.
Proof.
  intro.
  run (
    n <- ret 3 ;
    top_goals <- Mgoals ;
    iter (fun top =>
      e1 <- evar nat ;
      e2 <- evar nat ;
      subgoals <- Mrefine top (match x with O => e1 | S x0 => e2 end) ;
      iter (fun g =>
        Mrefine g n
      ) subgoals
    ) top_goals
  ) as H.
Qed.

(*
 * Anomaly: Uncaught exception Not_found(_). Please report.
Goal forall x : nat, nat.
Proof.
  intro.
  destruct x.
  pose (n := 3).
  run (
    Mgoals >>
    iter (fun g => 
      Mgmatch g [ Mgoal [] nat (Mrefine g n) ]
    )
  ) as Unused.
Qed.
*)

Definition fold {A B : Type} (f : A -> B -> M B) :=
  mfix2 y (acc : B) (lst : list A) : M B :=
    match lst with
    | nil => ret acc
    | cons x xs =>
      acc' <- f x acc ;
      y acc' xs
    end.

Goal forall (X : nat) (H : X = 3), nat.
Proof.
  intros.
  run (
    nu (n:nat) ,
      Mgoals >>
      fold (fun g acc => 
        gmatch g with
        | [ z H ] { z ::: nat, H ::: (z = acc) } nat => ret n
        end
      ) n
      >> (fun (_ : nat) => abs n (ret 3))
  ) as H2.
  exact 2.
  Show Proof.
Qed.

(*
 * Error: No pattern matches.
Goal forall (X : nat) (H : X = 3), nat.
Proof.
  intros.
  assert (n : nat) by exact O.
  run (
    Mgoals >>
    iter (fun g => 
      Mgmatch g [
        Mtele (fun z => Mtele (fun H0 =>
          Mgoal [Named nat z ; Named (z = n) H0] nat (ret tt)
        ))
      ]
    )
  ) as H.
Qed.
*)

Definition test (m : nat) :=
  Mgoals >>
  iter (fun g =>
    gmatch g with
    | {} nat => Mrefine g m
    end
  ).

(*
Goal forall x:nat, nat.
Proof.
  intro x.
  destruct x ; [ 
    (assert (n : nat) by exact O ; assert (t : Set) by exact nat) |
    (assert (t : Set) by exact nat ; assert (m : nat) by exact 1)
  ].
  run (test n) as Unused.
  Show Proof.
Qed.
*)

(*
Goal forall (X : nat) (H : X = 3), nat.
Proof.
  intros.
  run (
  ret (
    fun n =>
      G <- Mgoals ;
      iter (fun g => 
        Mgmatch g [
          Mtele (fun z => Mtele (fun H0 =>
            Mgoal [Named nat z ; Named (z = n) H0] nat (ret tt)
          ))
        ]
      ) G)
  ) as H'.
  Show Proof.
  (*
  run (
    G <- Mgoals ;
    iter (fun g => 
      Mgmatch g [ Mgoal [] nat (Mrefine g n) ]
    ) G
  ) as Unused.
*)
  Qed.
*)

Lemma should_fail : forall x : nat, x = x.
Proof.
  intro.
  run (
    lst <- Mgoals ;
    iter (fun y => Mrefine y (eq_refl nat)) lst
  ) as t.
Qed.
*)