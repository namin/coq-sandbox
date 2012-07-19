Check refl_equal.
(* ===>
eq_refl
     : forall (A : Type) (x : A), x = x
*)

Check eq_ind.
(* ===>
eq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
*)

Definition eq_sym' (A:Type)(x y:A)(h : x=y) : y=x :=
  eq_ind x (fun z => z=x) (refl_equal x) y h.

Definition eq_trans' (A:Type)(x y z:A)(h : x=y)(g : y=z) : x=z :=
  eq_ind y (fun z => x=z) h z g.

Definition eq_subst' (A:Type)(B: A -> Prop)(x y:A)(h : x=y)(g : B x) : B y :=
  eq_ind x (fun z => B z) g y h.

Definition eq_resp' (A:Type)(B: Prop)(x y:A)(h : x=y)(g: A -> B) : g x = g y :=
  eq_ind x (fun z => g x = g z) (refl_equal (g x)) y h.
