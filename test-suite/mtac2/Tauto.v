Require Import List.
Import ListNotations.
Require Import Mtac2.
Import Mtac2Notations.

Module WithList.

  Definition dyn := { x : Prop | x}.
  Definition Dyn := @exist Prop (fun p=>p).

  Definition ProofNotFound : Exception.
    exact exception.
  Qed.

  Definition lookup (p : Prop) := 
    mfix1 f (s : list dyn) : M p :=
      mmatch s return M p with
      | [x s'] (Dyn p x) :: s' => ret x return M (fun _=>p)
      | [d s'] d :: s' => f s' return M (fun _=>p)
      | _ => raise ProofNotFound
      end.

  Definition tauto' :=
    mfix2 f (c : list dyn) (p : Prop) : M p :=
      mmatch p as p' return M (p' : Prop) with
      | True => ret I
      | [p1 p2] p1 /\ p2 =>
           r1 <- f c p1 ;
           r2 <- f c p2 ;
           ret (conj r1 r2)
      | [p1 p2]  p1 \/ p2 =>
           mtry 
             r1 <- f c p1 ;
             ret (or_introl r1)
           with _ =>
             r2 <- f c p2 ;
             ret (or_intror r2)
           end
      | [p1 p2 : Prop] p1 -> p2 =>
           nu (x:p1),
             r <- f (Dyn p1 x :: c) p2;
             abs x r
      | [A (q:A -> Prop)] (forall x:A, q x) =>
           nu (x:A),
             r <- f c (q x);
             abs x r
      | [A (q:A -> Prop)] (exists x:A, q x) =>
           X <- evar A;
           r <- f c (q X);
           b <- is_evar X;
           if b then 
             raise ProofNotFound
           else
             ret (ex_intro q X r) 
      | [p':Prop] p' => lookup p' c return M (fun p' : Prop=>p')
      end.
  
  Definition tauto P := 
    tauto' nil P.

End WithList.

Example ex1 : True /\ (True \/ False) := eval (WithList.tauto _).

Example ex_id (p : Prop) : 
  p -> p.
Proof.
  refine (eval (WithList.tauto _)).
Qed.

Example ex_first_order_2 (p q r : Prop) : 
  q -> p -> q.
Proof.
  refine (eval (WithList.tauto _)).
Qed.

Example ex_first_order_2'  : 
  forall (p q : nat -> Prop) x , p x -> q x -> p x /\ q x.
Proof. 
  refine (eval (WithList.tauto _)).
Qed.

Example ex_existential  : 
  forall (p q : nat -> Prop) x , p x -> q x -> exists y z, p y /\ q z.
Proof. 
  refine (eval (WithList.tauto _)).
Qed.

Ltac my_tauto :=
  repeat match goal with
           | [ H : ?P |- ?P ] => exact H

           | [ |- True ] => constructor
           | [ |- _ /\ _ ] => constructor
           | [ |- _ -> _ ] => intro

           | [ H : False |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ \/ _ |- _ ] => destruct H

           | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
         end.

Definition iter {A B : Type} (f : A -> M B) :=
  mfix1 y (lst : list A) : M unit :=
    match lst with
    | nil => ret tt
    | cons x xs =>
      _ <- f x ;
      y xs
    end.

Notation "f @@ x" := (r <- x; f r) (at level 70).

Require Import Mtactics.


Program Definition tauto_goal :=
  mfix1 f (l : list goal) : M unit :=
    iter (fun g =>
      Mprint g;;
      Mshow g;;
      gmatch g with
      | [ X H ] { H ::: X } X => Mprint X;; f @@ Mrefine g H
      | { } True => Mprint True;; f @@ Mrefine g I
      | [P Q : Prop] { } P /\ Q =>
        Mprint (P /\ Q);;
        X <- evar P; Y <- evar Q;
        f @@ Mrefine g (conj X Y)
(*
      | [P Q : Prop] { } P \/ Q =>
        mtry
          X <- evar P;
          f @@ Mrefine g (or_introl Q X)
        with _ =>
          X <- evar Q;
          f @@ Mrefine g (or_intror P X)
        end
*)
      | [P Q : Prop] { } P -> Q =>
        Mprint (P -> Q);;
        r <- intro g;
        f [r]
(*
      | [H (G : Prop)] { H ::: False } G =>
        f @@ Mrefine g (match H with end : G)
      | [P Q H (G : Prop)] { H ::: (P /\ Q) } G =>
        X <- evar (P -> Q -> G);
        f @@ Mrefine g (match H with conj x y => X x y end)
      | [P Q H (G : Prop)] { H ::: (P \/ Q) } G => 
        X <- evar (P -> G);
        Y <- evar (Q -> G);
        f @@ Mrefine g (match H with or_introl x => X x | or_intror y
        => Y y end)
                                        
      | [P Q H1 H2 G] {H1 ::: (P -> Q), H2 ::: P} G =>
        X <- evar (Q -> G);
        f @@ Mrefine g ((fun x:Q=>X x) (H1 H2))
*)
      end) l.


Example tauto1 (P Q R : Prop) : P -> Q -> P /\ Q.
(* it's looping forever :( *)
(*  run_eff (Mgoals >> tauto_goal). *)
(* but each bit works *)
  run_eff (Mgoals >> get >> intro).
  run_eff (Mgoals >> get >> intro).
  run_eff (Mgoals >> get >> fun g => (X <- evar P; Y <- evar Q;
        Mrefine g (conj X Y))).
  run_eff (Mgoals >> iter assumption).
Qed.