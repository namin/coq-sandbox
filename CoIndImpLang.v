(* begin hide *)
Require Import CpdtTactics.
Set Implicit Arguments.
(* end hide *)

(** * Simple Modeling of Non-Terminating Programs *)

(** We close the chapter with a quick motivating example for more complex uses of co-inductive types.  We will define a co-inductive semantics for a simple imperative programming language and use that semantics to prove the correctness of a trivial optimization that removes spurious additions by 0.  We follow the technique of %\index{co-inductive big-step operational semantics}\emph{%#<i>#co-inductive big-step operational semantics#</i>#%}~\cite{BigStep}%.

   We define a suggestive synonym for [nat], as we will consider programs with infinitely many variables, represented as [nat]s. *)

Definition var := nat.

(** We define a type [vars] of maps from variables to values.  To define a function [set] for setting a variable's value in a map, we import the [Arith] module from Coq's standard library, and we use its function [beq_nat] for comparing natural numbers. *)

Definition vars := var -> nat.
Require Import Arith.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

(** We define a simple arithmetic expression language with variables, and we give it a semantics via an interpreter. *)

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => vs v
    | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.

(** Finally, we define a language of commands.  It includes variable assignment, sequencing, and a %\texttt{%#<tt>#while#</tt>#%}% form that repeats as long as its test expression evaluates to a nonzero value. *)

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

(** We could define an inductive relation to characterize the results of command evaluation.  However, such a relation would not capture %\emph{%#<i>#nonterminating#</i>#%}% executions.  With a co-inductive relation, we can capture both cases.  The parameters of the relation are an initial state, a command, and a final state.  A program that does not terminate in a particular initial state is related to %\emph{%#<i>#any#</i>#%}% final state. *)

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  -> evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  -> evalCmd vs1 c vs2
  -> evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3.

(** Having learned our lesson in the last section, before proceeding, we build a co-induction principle for [evalCmd]. *)

Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

  (** The proof is routine.  We make use of a form of %\index{tactics!destruct}%[destruct] that takes an %\index{intro pattern}\emph{%#<i>#intro pattern#</i>#%}% in an [as] clause.  These patterns control how deeply we break apart the components of an inductive value, and we refer the reader to the Coq manual for more details. *)

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix; intros; destruct c.
    rewrite (AssignCase H); constructor.
    destruct (SeqCase H) as [? [? ?]]; econstructor; eauto.
    destruct (WhileCase H) as [[? ?] | [? [? [? ?]]]]; subst;
      [ econstructor | econstructor 4 ]; eauto.
  Qed.
End evalCmd_coind.

(** Now that we have a co-induction principle, we should use it to prove something!  Our example is a trivial program optimizer that finds places to replace [0 + e] with [e]. *)

Fixpoint optExp (e : exp) : exp :=
  match e with
    | Plus (Const 0) e => optExp e
    | Plus e1 e2 => Plus (optExp e1) (optExp e2)
    | _ => e
  end.

Fixpoint optCmd (c : cmd) : cmd :=
  match c with
    | Assign v e => Assign v (optExp e)
    | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
    | While e c => While (optExp e) (optCmd c)
  end.

(** Before proving correctness of [optCmd], we prove a lemma about [optExp].  This is where we have to do the most work, choosing pattern match opportunities automatically. *)

(* begin thide *)
Lemma optExp_correct : forall vs e, evalExp vs (optExp e) = evalExp vs e.
  induction e; crush;
    repeat (match goal with
              | [ |- context[match ?E with Const _ => _ | Var _ => _
                               | Plus _ _ => _ end] ] => destruct E
              | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
            end; crush).
Qed.

Hint Rewrite optExp_correct : cpdt.

(** The final theorem is easy to establish, using our co-induction principle and a bit of Ltac smarts that we leave unexplained for now.  Curious readers can consult the Coq manual, or wait for the later chapters of this book about proof automation. *)

Theorem optCmd_correct : forall vs1 c vs2, evalCmd vs1 c vs2
  -> evalCmd vs1 (optCmd c) vs2.
  intros; apply (evalCmd_coind (fun vs1 c' vs2 => exists c, evalCmd vs1 c vs2
    /\ c' = optCmd c)); eauto; crush;
    match goal with
      | [ H : _ = optCmd ?E |- _ ] => destruct E; simpl in *; discriminate
        || injection H; intros; subst
    end; match goal with
           | [ H : evalCmd _ _ _ |- _ ] => ((inversion H; [])
             || (inversion H; [|])); subst
         end; crush; eauto 10.
Qed.
(* end thide *)

(** In this form, the theorem tells us that the optimizer preserves observable behavior of both terminating and nonterminating programs, but we did not have to do more work than for the case of terminating programs alone.  We merely took the natural inductive definition for terminating executions, made it co-inductive, and applied the appropriate co-induction principle.  Curious readers might experiment with adding command constructs like %\texttt{%#<tt>#if#</tt>#%}%; the same proof should continue working, after the co-induction principle is extended to the new evaluation rules. *)
