(*
Exercies from http://adam.chlipala.net/cpdt/html/Subset.html
*)

Require Import MoreSpecif.
Require Import CpdtTactics.
Set Implicit Arguments.

Local Open Scope specif_scope.

(*
Write a function of type [forall n m : nat, {][n <= m} + {][n > m}].  That is, this function decides whether one natural is less than another, and its dependent type guarantees that its results are accurate.
*)
Definition leq_nat_dec : forall n m : nat, {n <= m} + {n > m}.
  refine (fix f (n m : nat) : {n <= m} + {n > m} :=
    match n, m with
      | O, _ => Yes
      | _, O => No
      | S n', S m' => Reduce (f n' m')
    end); crush.
Qed.
