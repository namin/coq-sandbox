(**

Last exercise from http://adam.chlipala.net/cpdt/html/Subset.html
Also see older more detailed version of similar homework at http://adam.chlipala.net/itp/hw/HW6.html

Implement the DPLL satisfiability decision procedure for boolean formulas in conjunctive normal form, with a dependent type that guarantees its correctness.  An example of a reasonable type for this function would be [forall f : formula, {truth : tvals | formulaTrue truth f} + {][forall truth, ~ formulaTrue truth f}].  Implement at least %``%#"#the basic backtracking algorithm#"#%''% as defined here:
  %\begin{center}\url{http://en.wikipedia.org/wiki/DPLL_algorithm}\end{center}%
  #<blockquote><a href="http://en.wikipedia.org/wiki/DPLL_algorithm">http://en.wikipedia.org/wiki/DPLL_algorithm</a></blockquote>#
It might also be instructive to implement the unit propagation and pure literal elimination optimizations described there or some other optimizations that have been used in modern SAT solvers.

*)

Require Import Arith Bool List.
Require Import MoreSpecif.
Require Import CpdtTactics.
Set Implicit Arguments.

Local Open Scope specif_scope.

Definition var := nat.

Definition lit := (bool * var)%type.

Definition clause := list lit. (** distjunction *)

Definition formula := list clause. (** conjuction *)

Definition asgn := var -> bool.

Definition satLit (l : lit) (a : asgn) :=
  a (snd l) = fst l.

Fixpoint satClause (cl : clause) (a : asgn) : Prop :=
  match cl with
    | nil => False
    | l :: cl' => satLit l a \/ satClause cl' a
  end.

Fixpoint satFormula (fm : formula) (a : asgn) : Prop :=
  match fm with
    | nil => True
    | cl :: fm' => satClause cl a /\ satFormula fm' a
  end.

Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

Lemma contradictory_assignment : forall s l cl a,
  s <> fst l
  -> satLit l a
  -> satLit (s, snd l) a
  -> satClause cl a.
  intros.
  red in H0, H1.
  crush.
Qed.

Hint Resolve contradictory_assignment.

Definition upd (a : asgn) (l : lit) : asgn :=
  fun v : var =>
    if eq_nat_dec v (snd l)
      then fst l
      else a v.

Lemma satLit_upd_eq : forall l a,
  satLit l (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_eq.

Lemma satLit_upd_neq : forall v l s a,
  v <> snd l
  -> satLit (s, v) (upd a l)
  -> satLit (s, v) a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_neq.

Lemma satLit_upd_neq2 : forall v l s a,
  v <> snd l
  -> satLit (s, v) a
  -> satLit (s, v) (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_neq2.

Lemma satLit_contra : forall s l a cl,
  s <> fst l
  -> satLit (s, snd l) (upd a l)
  -> satClause cl a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); crush.
Qed.

Hint Resolve satLit_contra.

Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
  match goal with
    | [ H1 : satLit ?l ?a, H2 : satClause ?cl ?a |- _ ] =>
      assert (satClause cl (upd a l)); firstorder
  end.

Definition setClause : forall (cl : clause) (l : lit),
  {cl' : clause |
    forall a, satClause cl (upd a l) <-> satClause cl' a }
  + { forall a, satLit l a -> satClause cl a }.
  refine (fix setClause (cl : clause) (l : lit)
    : {cl' : clause |
      forall a, satClause cl (upd a l) <-> satClause cl' a}
    + {forall a, satLit l a -> satClause cl a} :=
    match cl with
      | nil => [|| nil ||]
      | (s, v) :: cl' =>
	if eq_nat_dec v (snd l)
	  then if bool_eq_dec s (fst l)
	    then !!
	    else cl'' <-- setClause cl' l; [|| cl'' ||]
	  else   cl'' <-- setClause cl' l; [|| ((s, v) :: cl'') ||]
    end); clear setClause; magic_solver.
Defined.

Definition setClauseSimple (cl : clause) (l : lit) :=
  match setClause cl l with
    | inleft (exist cl' _) => Some cl'
    | inright _ => None
  end.

Eval compute in setClauseSimple nil (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (false, 1).

Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {True}.
  destruct ls; eauto.
Defined.
Implicit Arguments isNil [A].

Lemma satLit_idem_lit : forall l a l',
  satLit l a
  -> satLit l' a
  -> satLit l' (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l') (snd l)); congruence.
Qed.

Hint Resolve satLit_idem_lit.

Lemma satLit_idem_clause : forall l a cl,
  satLit l a
  -> satClause cl a
  -> satClause cl (upd a l).
  induction cl; simpl; intuition.
Qed.

Hint Resolve satLit_idem_clause.

Lemma satLit_idem_formula : forall l a fm,
  satLit l a
  -> satFormula fm a
  -> satFormula fm (upd a l).
  induction fm; simpl; intuition.
Qed.

Hint Resolve satLit_idem_formula.

Definition setFormula : forall (fm : formula) (l : lit),
  {fm' : formula |
    forall a, satFormula fm (upd a l) <-> satFormula fm' a}
  + {forall a, satLit l a -> ~satFormula fm a}.
  refine (fix setFormula (fm : formula) (l : lit)
    : {fm' : formula |
      forall a, satFormula fm (upd a l) <-> satFormula fm' a}
    + {forall a, satLit l a -> ~satFormula fm a} :=
    match fm with
      | nil => [|| nil ||]
      | cl :: fm' =>
	match setClause cl l with
          | !!          => fm'' <-- setFormula fm' l; [|| fm'' ||]
          | [|| cl' ||] => fm'' <-- setFormula fm' l; [|| cl'::fm'' ||]
        end
    end); clear setFormula; magic_solver.
Defined.

