Require Import Mtac2.
Require Import List.
Import Mtac2Notations.

Definition foldLL {A B : Type} (f : A -> B -> M B) :=
  mfix2 y (lst : LazyList A) (acc : B) : M B :=
    step <- Mnext lst ;
    mmatch step with
    | None => ret acc
    | [ x xs ] Some (x, xs) =>
      f x acc >>
      y xs
    end.

Definition Absurd : Exception.
  exact exception.
Qed.

Definition get {A} (l : list A) : M A :=
  match l with
  | cons x nil => ret x
  | _ => raise Absurd
  end.

Definition assert (g : goal) A :=
  gmatch g with
  | [ T ] {} T =>
    f <- evar (A -> T) ;
    x <- evar A ;
    Mrefine g (f x)
  end.

Definition intro (g : goal) :=
  gmatch g with
  | [ X Y ] {} X -> Y =>
    f <- nu (x:X), res <- evar Y ; abs x res ;
    l <- Mrefine g f ;
    get l
  end.

Definition assert_by {A} (g : goal) t :=
  gmatch g with
  | [ T ] {} T =>
    f <- evar (A -> T) ;
    sub_goals <- Mrefine g (f t) ;
    match sub_goals with
    | nil => raise Absurd
    | cons g gs =>
      g' <- intro g ;
      ret (cons g' gs)
    end
  end.

Definition simplify (g : goal) :=
  gmatch g with
  | [ l (Res: Type) ] { < local_telescope Type (fun A:Type => local_telescope Type (fun B:Type => { H : (A * B) & unit })) >* as l } Res =>
    foldLL (fun sigma g =>
      mmatch sigma with
      | [ A B H ] lTele Type (fun A => local_telescope Type (fun B => { H : (A * B) & unit })) A
                (lTele Type (fun B => { H : (A * B) & unit }) B 
                  (existT _ H tt)) =>
        g' <- assert_by g (fst H) >> get ;
        assert_by g' (snd H) >> get
      end
    ) l g
  | _ => ret g (* nothing to do *)
  end.

Definition NoSuchAssumption : Exception.
  exact exception.
Qed.

Definition assumption g :=
  gmatch g with
  | [ X H ] { H ::: X } X => Mrefine g H
  | _ => raise NoSuchAssumption
  end.

Example mtactics_usage : nat * bool -> option nat * option bool -> option bool.
Proof.
  intros.
  run_eff (Mgoals >> get >> simplify >> assumption).
Qed.
