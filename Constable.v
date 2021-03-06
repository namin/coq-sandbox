Theorem ex_falso_quodlibet : forall P,
  False -> P.
Proof.
  intros P contra. inversion contra.
Qed.

Theorem constable_3 : forall P Q,
  ~(P /\ Q) /\ (P \/ ~P) /\ (Q \/ ~Q) ->
  ~P \/ ~Q.
Proof.
  intros P Q H.
  inversion H as [H' [[HP | HP'] [HQ | HQ']]]; solve [
    left; assumption |
    right; assumption |
    apply ex_falso_quodlibet; apply H'; split; assumption
  ].
Qed.

Theorem constable_3' : forall P Q,
  ~(P /\ Q) /\ (P \/ ~P) /\ (Q \/ ~Q) ->
  ~P \/ ~Q.
Proof.
  intros P Q H.
  inversion H as [H' [[HP | HP'] DQ]].
  assert (HQ': ~Q). intros HQ. apply H'. split; assumption. right; assumption.
  left; assumption.
Qed.

Definition constable_3'' : forall P Q,
  ~(P /\ Q) /\ (P \/ ~P) /\ (Q \/ ~Q) ->
  ~P \/ ~Q := fun p q h =>
    match h with
      | conj na (conj (or_intror np) _) =>
        or_introl _ np
      | conj na (conj (or_introl yp) _) =>
        or_intror _ (fun yq => na (conj yp yq))
    end.

Theorem constable_4 : forall (X:Type) (P: X -> Prop) (C: Prop),
  (exists x, (P x -> C)) -> (forall x, (P x)) -> C.
Proof.
  intros X P C Hex Hal. inversion Hex as [x' Hex'].
  apply Hex'. apply Hal.
Qed.

Definition constable_4' : forall (X:Type) (P: X -> Prop) (C: Prop),
  (exists x, (P x -> C)) -> (forall x, (P x)) -> C :=
  fun X P C Hex Hal =>
    match Hex with
      | ex_intro x' Hex' => Hex' (Hal x')
    end.
