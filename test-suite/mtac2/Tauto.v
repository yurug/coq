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

