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

Inductive id' (A:Type) : A -> A -> Prop :=
  refl': forall x, id' A x x.

Check id'_ind.
(* ===>
id'_ind
     : forall (A : Type) (P : A -> A -> Prop),
       (forall x : A, P x x) -> forall y y0 : A, id' A y y0 -> P y y0
*)

Definition id'_sym (A:Type)(x y:A)(h : id' A x y) : id' A y x :=
  id'_ind A (fun u v => id' A v u) (fun z => refl' A z) x y h.

Definition id'_trans (A:Type)(x y z:A)(h : id' A x y)(g : id' A y z) : id' A x z :=
  id'_ind A (fun u v => id' A v z -> id' A u z) (fun z i => i) x y h g.

Definition id'_subst (A:Type)(B: A -> Prop)(x y:A)(h : id' A x y)(g : B x) : B y :=
  id'_ind A (fun u v => B u -> B v) (fun z i => i) x y h g.

Definition id'_resp' (A:Type)(B: Prop)(x y:A)(h : id' A x y)(g: A -> B) : id' B (g x) (g y) :=
  id'_ind A (fun u v => forall q, id' B (q u) (q v)) (fun z q => refl' B (q z)) x y h g.
