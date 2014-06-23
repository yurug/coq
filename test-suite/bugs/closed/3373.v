(* File reduced by coq-bug-finder from original input, then from 5968 lines to
11933 lines, then from 11239 lines to 11231 lines, then from 10365 lines to 446
lines, then from 456 lines to 379 lines, then from 391 lines to 373 lines, then
from 369 lines to 351 lines, then from 350 lines to 340 lines, then from 348
lines to 320 lines, then from 328 lines to 302 lines, then from 332 lines to 21
lines *)
Set Universe Polymorphism.
Axiom admit : forall {T}, T.
Definition UU := Set.
Definition UU' := Type.
Definition hSet:= sigT (fun X : UU' => admit) .
Definition pr1hSet:= @projT1 UU (fun X : UU' => admit) : hSet -> Type.
Coercion pr1hSet: hSet >-> Sortclass.
Axiom binop : UU -> Type.
Axiom setwithbinop : Type.
Definition pr1setwithbinop : setwithbinop -> hSet.
Goal True.
pose (( @projT1 _ ( fun X : hSet@{Set j k} => binop X ) ) : _ -> hSet).
Admitted.