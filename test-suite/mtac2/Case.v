Require Import Mtac2.
Require Import List.

Goal True.
Proof.
  (* Opaque value so that our matches don't reduce. *) 
  assert (n : nat) by constructor.
  (* We begin with a simple case construct: *)
  pose (M1 := (match n with 0 => true | S n' => false end)).
  run (Mdestcase M1) as S1.
  run (Mmakecase S1) as M1'.
  (* 
    The resulting match should match (hehe) the one we had in the beginning. 
    Note that we only get a dyn value. This is because our types are too weak
    to support a stronger specification for Mmakecase. This is highly unfortunate
    and definitely a candidate for future work.
  *)
  assert (C1 : elem M1' = M1) by reflexivity.
  
  
  (* Nested cases - we only care about the outer one *)
  pose (M2 := (match n with 1 => true | _ => false end)).
  run (Mdestcase M2) as S2.
  run (Mmakecase S2) as M2'.
  (* The resulting match must be equivalent to the one we started with *)
  assert (C2 : elem M2' = M2) by reflexivity.
  
  (* Types are values, too. *)
  pose (M3 := (match n with 0 => (False:Type) | S _ => (unit:Type) end)).
  run (Mdestcase M3) as S3.
  run (Mmakecase S3) as M3'.
  (* Again, the resulting match should be equivalent the one we had in the beginning. *)
  assert (C3 : elem M3' = M3) by reflexivity.

  (* Let's change the last case construct to one that always give out False. *)
  pose (Snew := 
       {| case_ind := nat
        ; case_val := case_val S3
        ; case_type := Type
        ; case_return := {| elem := fun (n : nat) => Type |}
        ; case_branches := {| elem := fun (n : nat) => (False:Type) |} :: tail (case_branches S3)
       |}
       ).
  run (Mmakecase Snew) as Snew'.
  (* See if we did the right thing. *)
  assert (C4 : elem Snew' = match n with 0 => False | _ => False end) by reflexivity.
  (* Yay *)
Abort.

Import Mtac2Notations.
Import ListNotations.

Definition LMap {A B} (f : A -> M B) :=
  mfix1 rec (l : list A) : M (list B) := 
  match l with
  | [] => ret []
  | (x :: xs) => l <- rec xs;
                b <- f x;
                ret (b :: l)
  end.
  
Definition CantCoerce : Exception. exact exception. Qed.

Definition coerce {A B : Type} (x : A) : M B :=
  mmatch A return M B with
  | B => [H] ret (eq_rect_r _ (fun x0 : B => x0) H x)
  | _ => raise CantCoerce
  end.

Program Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
  mmatch d with
  | [C (D : C -> Type) (E : forall y:C, D y)] {| elem := fun x : C=>E x |} => 
    nu y : C,
      r <- rec (Dyn _ (E y));
      Mpabs y r
  | [c : A] {| elem := c |} => 
    ret (B c) 
  end.

Definition destruct {A : Type} (n : A) {P : A -> Prop} : M (P n) :=
  l <- Mconstrs A;
  l <- LMap (fun d : dyn=> 
             t' <- copy_ctx P d;
             e <- Mevar t';
             ret {| elem := e |}) l;
  let c := {| case_ind := A;
              case_val := n;
              case_type := P n;
              case_return := {| elem := fun n : A => P n |};
              case_branches := l
           |} in
  d <- Mmakecase c;
  d <- coerce (elem d);
  ret d.


Goal forall n : nat, True.
  intro n.
  Set Printing Implicit.
  apply (eval (destruct n)).
  Unshelve.
  simpl.
  apply I.
  intro n'.
  simpl.
Abort.

Goal forall b1 b2, andb b1 b2 = andb b2 b1.
intros.
apply (eval (destruct b1 (P:=fun b=>andb b b2 = andb b2 b))).
Unshelve.
simpl.
apply (eval (destruct b2 (P:=fun b=>b = andb b true))).
Unshelve.
simpl.
apply (eval (destruct b2 (P:=fun b=>false = andb b false))).
Unshelve.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Definition NotAProductException : Exception. exact exception. Qed.
Definition destruct0 {P : Prop} : M P :=
  mmatch P with
  | [A (Q : A->Prop)] forall x:A, Q x =>
    nu x:A,
      r <- destruct x (P:=Q);
      a <- Mabs x r (P:=Q);
      coerce a
  | _ => raise NotAProductException
  end.

Goal forall l : list nat, l ++ [] = l.
Drop.
  apply (eval destruct0).
  Unshelve.
  - reflexivity.
  - simpl.
    (* hehe, now we need the fixpoint ;-) *)
Abort.