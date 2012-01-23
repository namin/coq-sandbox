(*
Exercies from http://adam.chlipala.net/cpdt/html/Subset.html
*)

Require Import Arith.
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
Defined.

(* Ex 2 *)

(* Define [var], a type of propositional variables, as a synonym for [nat]. *)
Definition var := nat.

(* Define an inductive type [prop] of propositional logic formulas, consisting of variables, negation, and binary conjunction and disjunction. *)
Inductive prop : Set :=
| Var : var -> prop
| Not : prop -> prop
| And : prop -> prop -> prop
| Or  : prop -> prop -> prop.

(* Define a function [propDenote] from variable truth assignments and [prop]s to [Prop], based on the usual meanings of the connectives.  Represent truth assignments as functions from [var] to [bool]. *)
Fixpoint propDenote (truth : var -> bool) (p : prop) : Prop :=
  match p with
    | Var v     =>  is_true (truth v)
    | Not p'    => ~(propDenote truth p')
    | And p1 p2 =>  (propDenote truth p1) /\ (propDenote truth p2)
    | Or  p1 p2 =>  (propDenote truth p1) \/ (propDenote truth p2)
  end.

(* Define a function [bool_true_dec] that checks whether a boolean is true, with a maximally expressive dependent type.  That is, the function should have type [forall b, {b = true} + {b = true -> False}]. *)
Definition bool_true_dec : forall b, {b = true} + {b = true -> False}.
  refine (fun b =>
    match b with
      | true => Yes
      | false => No
    end); crush.
Defined.

(* Define a function [decide] that determines whether a particular [prop] is true under a particular truth assignment.  That is, the function should have type [forall (truth : var -> bool) (p : prop), {propDenote truth p} + {~ propDenote truth p}].  This function is probably easiest to write in the usual tactical style, instead of programming with [refine].  The function [bool_true_dec] may come in handy as a hint. *)
Definition decide : forall (truth : var -> bool) (p : prop), {propDenote truth p} + {~ propDenote truth p}.
  induction p; crush. apply bool_true_dec.
Defined.

(* Define a function [negate] that returns a simplified version of the negation of a [prop].  That is, the function should have type [forall p : prop, {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'}].  To simplify a variable, just negate it.  Simplify a negation by returning its argument.  Simplify conjunctions and disjunctions using De Morgan's laws, negating the arguments recursively and switching the kind of connective.  Your [decide] function may be useful in some of the proof obligations, even if you do not use it in the computational part of [negate]'s definition.  Lemmas like [decide] allow us to compensate for the lack of a general Law of the Excluded Middle in CIC. *)
Fixpoint negateProp (p : prop) : prop :=
  match p with
    | Var v     => Not p
    | Not p'    => p'
    | And p1 p2 => Or (negateProp p1) (negateProp p2)
    | Or  p1 p2 => And (negateProp p1) (negateProp p2)
  end.
Definition negate : forall p : prop, {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'}.
  refine (fun p => [ negateProp p ]).
    intro truth. destruct (decide truth p); induction p; crush.
Defined.
