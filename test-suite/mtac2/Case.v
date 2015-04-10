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

Definition destruct {A : Type} (n : A) {P : Prop} : M P :=
  l <- Mconstrs A;
  l <- LMap (fun d : dyn=> 
             let (t, c) := d in
             e <- Mevar t;
             ret {| elem := e |}) l;
  let c := {| case_ind := A;
              case_val := n;
              case_type := P;
              case_return := {| elem := fun _ : A => P |};
              case_branches := l
           |} in
  d <- Mmakecase c;
  d <- coerce (elem d);
  ret d.


Goal forall n : nat, True.
  intro n.
  run (destruct n (P:=True)) as H.

