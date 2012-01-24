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

(** * Problem Definition *)

Definition var := nat.
(** We identify propositional variables with natural numbers. *)

Definition lit := (bool * var)%type.
(** A literal is a combination of a truth value and a variable. *)

Definition clause := list lit. (** distjunction *)
(** A clause is a list (disjunction) of literals. *)

Definition formula := list clause. (** conjuction *)
(** A formula is a list (conjunction) of clauses. *)

Definition asgn := var -> bool.
(** An assignment is a function from variables to their truth values. *)

Definition satLit (l : lit) (a : asgn) :=
  a (snd l) = fst l.
(** An assignment satisfies a literal if it maps it to true. *)

Fixpoint satClause (cl : clause) (a : asgn) : Prop :=
  match cl with
    | nil => False
    | l :: cl' => satLit l a \/ satClause cl' a
  end.
(** An assignment satisfies a clause if it satisfies at least one of its
  literals.
  *)

Fixpoint satFormula (fm : formula) (a : asgn) : Prop :=
  match fm with
    | nil => True
    | cl :: fm' => satClause cl a /\ satFormula fm' a
  end.
(** An assignment satisfies a formula if it satisfies all of its clauses. *)

(** * Subroutines *)

(** You'll probably want to compare booleans for equality at some point. *)
Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

(** A literal and its negation can't be true simultaneously. *)
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

(** Augment an assignment with a new mapping. *)
Definition upd (a : asgn) (l : lit) : asgn :=
  fun v : var =>
    if eq_nat_dec v (snd l)
      then fst l
      else a v.

(** Some lemmas about [upd] *)

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

(** Here's the tactic that I used to discharge #<i>#all#</i># proof obligations
  in my implementations of the four functions you will define.
  It comes with no warranty, as different implementations may lead to
  obligations that it can't solve, or obligations that it takes 42 years to
  solve.
  However, if you think enough like me, each of the four definitions you fill in
  should read like: [[
refine some_expression_with_holes; clear function_name; magic_solver.
]] leaving out the [clear] invocation for non-recursive function definitions.
  *)
Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
  match goal with
    | [ H1 : satLit ?l ?a, H2 : satClause ?cl ?a |- _ ] =>
      assert (satClause cl (upd a l)); firstorder
  end.

(** OK, here's your first challenge.  Write this strongly-specified function to
  update a clause to reflect the effect of making a particular literal true.
  *)
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

(** It's useful to have this strongly-specified nilness check. *)
Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {True}.
refine (fun A ls =>
  match ls with
    | nil => left _ _
    | _ => right _ _
  end); reflexivity.
Defined.
Implicit Arguments isNil [A].

(** Some more lemmas that I found helpful.... *)

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

(** Challenge 2: Write this function that updates an entire formula to reflect
  setting a literal to true.
  *)
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
          | [|| cl' ||] =>
            if isNil cl'
              then !!
              else fm'' <-- setFormula fm' l; [|| cl'::fm'' ||]
        end
    end); clear setFormula; magic_solver.
Defined.

Definition setFormulaSimple (fm : formula) (l : lit) :=
  match setFormula fm l with
    | inleft (exist fm' _) => Some fm'
    | inright _ => None
  end.

Eval compute in setFormulaSimple nil (true, 0).
Eval compute in setFormulaSimple (((true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (false, 0) :: nil) :: nil) (true, 0).

Hint Extern 1 False => discriminate.

Hint Extern 1 False =>
  match goal with
    | [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end.

(** A simple SAT Solver *)

Definition negate (l : lit) := (negb (fst l), snd l).

Hint Unfold satFormula.

Lemma satLit_dec : forall l a,
  {satLit l a} + {satLit (negate l) a}.
  destruct l.
  unfold satLit; simpl; intro.
  destruct b; destruct (a v); simpl; auto.
Qed.

(** We'll represent assignments as lists of literals instead of functions. *)
Definition alist := list lit.

Fixpoint interp_alist (al : alist) : asgn :=
  match al with
    | nil => fun _ => true
    | l :: al' => upd (interp_alist al') l
  end.

(** An arbitrary heuristic to choose the next variable to split on *)

Definition chooseSplit (fm : formula) :=
  match fm with
    | ((l :: _) :: _) => l
    | _ => (true, 0)
  end.

Definition simpleSat: forall (bound : nat) (fm : formula),
  option ({al : alist | satFormula fm (interp_alist al)}
    + {forall a, ~satFormula fm a}).
  refine (fix simpleSat (bound : nat) (fm : formula)
    : option ({al : alist | satFormula fm (interp_alist al)}
      + {forall a, ~satFormula fm a}) :=
    if isNil fm then Some [|| nil ||] else
    match bound with
      | O => None
      | S bound' =>
        let l := chooseSplit fm in
          match setFormula fm l with
            | [|| fm' ||] =>
              match simpleSat bound' fm' with
                | None => None
                | Some [|| al ||] => Some [|| l :: al ||]
                | Some !! =>
                  match setFormula fm (negate l) with
                    | [|| fm' ||] =>
                      match simpleSat bound' fm' with
                        | None => None
                        | Some [|| al ||] => Some [|| (negate l) :: al ||]
                        | Some !! => Some !!
                      end
                    | !! => Some !!
                  end
              end
            | !! =>
              match setFormula fm (negate l) with
                | [|| fm' ||] =>
                  match simpleSat bound' fm' with
                    | None => None
                    | Some [|| al ||] => Some [|| (negate l) :: al ||]
                    | Some !! => Some !!
                  end
                | !! => Some !!
              end
          end
    end); simpl; intros; subst; intuition; try generalize dependent (interp_alist al).
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
Defined.

Definition simpleSatSimple (bound : nat) (fm : formula) :=
  match simpleSat bound fm with
    | None => None
    | Some (inleft (exist a _)) => Some (Some a)
    | Some (inright _) => Some None
  end.

Eval compute in simpleSatSimple 100 nil.
Eval compute in simpleSatSimple 100 (((true, 0) :: nil) :: nil).
Eval compute in simpleSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in simpleSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).

(** Challenge 3: Write this code that either finds a unit clause in a formula
  or declares that there are none.
  *)
Definition findUnitClause : forall (fm : formula),
  {l : lit | In (l :: nil) fm}
  + {forall l, ~In (l :: nil) fm}.
  refine (fix findUnitClause (fm : formula)
  : {l : lit | In (l :: nil) fm}
  + {forall l, ~In (l :: nil) fm} :=
  match fm with
    | nil => !!
    | (l::nil) :: fm' => [|| l ||]
    | _ :: fm' => fm'' <-- findUnitClause fm'; [|| fm'' ||]
  end); clear findUnitClause; magic_solver.
Defined.

(** The literal in a unit clause must always be true in a satisfying
  assignment.
  *)
Lemma unitClauseTrue : forall l a fm,
  In (l :: nil) fm
  -> satFormula fm a
  -> satLit l a.
  induction fm; intuition.
  inversion H; subst; simpl in H0; intuition.
Qed.

Hint Resolve unitClauseTrue.

(** Final challenge: Implement unit propagation.  The return type of
  [unitPropagate] signifies that three results are possible:
  - [None]: There are no unit clauses.
  - [Some (inleft _)]: There is a unit clause, and here is a formula reflecting
    setting its literal to true.
  - [Some (inright _)]: There is a unit clause, and propagating it reveals that
    the formula is unsatisfiable.
  *)
Definition unitPropagate : forall (fm : formula), option (sigS (fun fm' : formula =>
  {l : lit |
    (forall a, satFormula fm a -> satLit l a)
    /\ forall a, satFormula fm (upd a l) <-> satFormula fm' a})
+ {forall a, ~satFormula fm a}).
refine (fun (fm : formula) =>
  match findUnitClause fm with
    | [|| l ||] =>
      match setFormula fm l with
        | [|| fm' ||] =>
          Some (inleft _ (existS (fun fm' : formula =>
            {l : lit |
              (forall a, satFormula fm a -> satLit l a)
              /\ forall a, satFormula fm (upd a l) <-> satFormula fm' a})
          fm' (exist _ l _)))
        | !! => Some !!
      end
    | !! => None
  end); magic_solver.
Defined.

Definition unitPropagateSimple (fm : formula) :=
  match unitPropagate fm with
    | None => None
    | Some (inleft (existS fm' (exist l _))) => Some (Some (fm', l))
    | Some (inright _) => Some None
  end.

Eval compute in unitPropagateSimple nil.
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: (false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((false, 0) :: (false, 1) :: nil) :: ((true, 0) :: nil) :: nil).


(** * The SAT Solver *)

(** This section defines a DPLL SAT solver in terms of the subroutines you've
  written.
  *)

(** Here's the final definition!  This is not the way you should write proof
  scripts. ;-)

  This implementation isn't #<i>#quite#</i># what you would expect, since it
  takes an extra parameter expressing a search tree depth.  Writing the function
  without that parameter would be trickier when it came to proving termination.
  In practice, you can just seed the bound with one plus the number of variables
  in the input, but the function's return type still indicates a possibility for
  a "time-out" by returning [None].
  *)
Definition boundedSat: forall (bound : nat) (fm : formula),
  option ({al : alist | satFormula fm (interp_alist al)}
    + {forall a, ~satFormula fm a}).
  refine (fix boundedSat (bound : nat) (fm : formula) {struct bound}
    : option ({al : alist | satFormula fm (interp_alist al)}
      + {forall a, ~satFormula fm a}) :=
    match bound with
      | O => None
      | S bound' =>
	if isNil fm
	  then Some (inleft _ (exist _ nil _))
	  else match unitPropagate fm with
		 | Some (inleft (existS fm' (exist l _))) =>
		   match boundedSat bound' fm' with
		     | None => None
		     | Some (inleft (exist al _)) => Some (inleft _ (exist _ (l :: al) _))
		     | Some (inright _) => Some (inright _ _)
		   end
		 | Some (inright _) => Some (inright _ _)
		 | None =>
		   let l := chooseSplit fm in
		     match setFormula fm l with
		       | inleft (exist fm' _) =>
			 match boundedSat bound' fm' with
			   | None => None
			   | Some (inleft (exist al _)) => Some (inleft _ (exist _ (l :: al) _))
			   | Some (inright _) =>
			     match setFormula fm (negate l) with
			       | inleft (exist fm' _) =>
				 match boundedSat bound' fm' with
				   | None => None
				   | Some (inleft (exist al _)) => Some (inleft _ (exist _ (negate l :: al) _))
				   | Some (inright _) => Some (inright _ _)
				 end
			       | inright _ => Some (inright _ _)
			     end
			 end
		       | inright _ =>
			 match setFormula fm (negate l) with
			   | inleft (exist fm' _) =>
			     match boundedSat bound' fm' with
			       | None => None
			       | Some (inleft (exist al _)) => Some (inleft _ (exist _ (negate l :: al) _))
			       | Some (inright _) => Some (inright _ _)
			     end
			   | inright _ => Some (inright _ _)
			 end
		     end
	       end
    end); simpl; intros; subst; intuition; try generalize dependent (interp_alist al).
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
Defined.

Definition boundedSatSimple (bound : nat) (fm : formula) :=
  match boundedSat bound fm with
    | None => None
    | Some (inleft (exist a _)) => Some (Some a)
    | Some (inright _) => Some None
  end.

Eval compute in boundedSatSimple 100 nil.
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).

Eval compute in boundedSatSimple 100 nil = simpleSatSimple 100 nil.
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: nil) = simpleSatSimple 100 (((true, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil) = simpleSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil) = simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil) = simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil) = simpleSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil) = simpleSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).

(** We can extract an OCaml version of [boundedSat]: *)
Recursive Extraction boundedSat.

(** You can test the OCaml version by saving the output of the
  [Recursive Extraction] to a file [Sol6.ml] and grabbing the support code in
  #<a href="Solver6.ml">#Solver6.ml#</a>#.  In the directory where you've put
  these files, start #<tt>#ocaml#</tt># and run: [[
#use "Sol6.ml";;
#use "Solver6.ml";;
]]
  After that, you can solve SAT problems in the SATLIB format.  You can find lots
  of examples in #<a href="http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html">#the
  SATLIB benchmark problem archive#</a>#.  My implementation is quite speedy on
  the first few classes of formulas listed, so you should be able to test yours
  on these real problems without much hassle.  To solve a problem in file
  #<tt>#testXX.cnf#</tt>#, run: [[
solve "testXX.cnf";;
]] *)