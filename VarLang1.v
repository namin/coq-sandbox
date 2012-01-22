(*
Exercise from http://adam.chlipala.net/cpdt/html/InductiveTypes.html

$\star$ Modify the first example language of Chapter 2 to include variables, where variables are represented with [nat].  Extend the syntax and semantics of expressions to accommodate the change.  Your new [expDenote] function should take as a new extra first argument a value of type [var -> nat], where [var] is a synonym for naturals-as-variables, and the function assigns a value to each variable.  Define a constant folding function which does a bottom-up pass over an expression, at each stage replacing every binary operation on constants with an equivalent constant.  Prove that constant folding preserves the meanings of expressions.
*)

(* begin hide *)
Require Import Arith.

Require Import CpdtTactics.

Set Implicit Arguments.
(* end hide *)

Inductive binop : Set := Plus | Times.

Definition var := nat.
Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.
Definition vs0 := fun v: var => 0.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Fixpoint expDenote (vs : vars) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => vs v
    | Binop b e1 e2 => (binopDenote b) (expDenote vs e1) (expDenote vs e2)
  end.

Example test_const:
  expDenote vs0 (Const 42) = 42.
Proof. simpl. reflexivity. Qed.

Example test_plus:
  expDenote vs0 (Binop Plus (Const 2) (Const 2)) = 4.
Proof. simpl. reflexivity. Qed.

Example test_times:
  expDenote vs0 (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)) = 28.
Proof. simpl. reflexivity. Qed.

Example test_var:
  expDenote (set vs0 0 1) (Binop Plus (Var 0) (Var 0)) = 2.
Proof. auto. Qed.

Fixpoint foldConstants (e : exp) : exp :=
  match e with
    | Binop b e1 e2 =>
      match (foldConstants e1), (foldConstants e2) with
        | (Const n1), (Const n2) => Const ((binopDenote b) n1 n2)
        | e1', e2' => Binop b e1' e2'
      end
    | _ => e
  end.

Example test_fold_constants:
  foldConstants (Binop Plus (Const 1) (Const 2)) = Const 3.
Proof. simpl. reflexivity. Qed.

Example test_fold_constants_nested:
  foldConstants (Binop Plus (Binop Plus (Const 1) (Const 2)) (Const 3)) = Const 6.
Proof. simpl. reflexivity. Qed.

Theorem foldConstants_correct : forall vs e, expDenote vs (foldConstants e) = expDenote vs e.
  induction e; crush;
    repeat (match goal with
              | [ |- context[match ?E with Const _ => _ | Var _ => _
                               | Binop _ _ _ => _ end] ] => destruct E
            end; crush).
Qed.