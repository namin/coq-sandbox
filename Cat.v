Require Import ConCaT.CATEGORY_THEORY.CATEGORY.Category.
Require Import ConCaT.CATEGORY_THEORY.CATEGORY.Dual.
Require Import ConCaT.CATEGORY_THEORY.CATEGORY.SET.
Require Import ConCaT.CATEGORY_THEORY.CATEGORY.PROD.
Require Import ConCaT.CATEGORY_THEORY.FUNCTOR.Functor.
Require Import ConCaT.CATEGORY_THEORY.FUNCTOR.Dual_Functor.
Require Import ConCaT.SETOID.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

(**

Homework 1, problem 2.

Verify that, for a fixed set A, the operations X -> X^A and X -> A^X
are, respectively, co- and contravariant functors on the category of
sets.

**)

Section hw1ex2_a2x.
  Variables (A : SET).

  Definition a2x_ob(X : SET) := A --> X.

  Section a2x_map_def.
    Variable X Y : SET.

    Section a2x_mor_def.
      Variable f : X --> Y.
      Definition a2x_mor1(g : A --> X) := g o f.
      Lemma a2x_map_law1 : Map_law a2x_mor1.
      Proof.
        unfold Map_law, a2x_mor1 in |- *.
        intros g h H.
        apply Comp_r; assumption.
      Qed.
      Canonical Structure a2x_mor : Map (a2x_ob X) (a2x_ob Y) :=
        a2x_map_law1.
    End a2x_mor_def.

    Lemma a2x_map_law : Map_law a2x_mor.
    Proof.
      unfold Map_law in |- *; simpl in |- *.
      intros f g H.
      unfold Ext. simpl.
      unfold a2x_mor1, a2x_ob in |- *.
      intros h.
      apply Pres1.
      assumption.
    Qed.
    Canonical Structure a2x_map := Build_Map a2x_map_law.
  End a2x_map_def.

  Lemma a2x_comp_law : Fcomp_law a2x_map.
  Proof.
    unfold Fcomp_law.
    intros X Y Z f g.
    unfold a2x_map. simpl.
    unfold a2x_mor, a2x_ob.
    unfold Ext. intros h.
    apply Ass.
  Qed.
  Lemma a2x_id_law : Fid_law a2x_map.
  Proof.
    unfold Fid_law. simpl.
    unfold Ext. simpl.
    unfold Id_fun. simpl.
    unfold a2x_mor1, a2x_ob.
    intros b f. unfold Ext. intros x.
    simpl. unfold Id_fun. apply Refl.
  Qed.
  Canonical Structure a2x_Fun := Build_Functor a2x_comp_law a2x_id_law.
End hw1ex2_a2x.

Definition SETop := Dual SET.

Section hw1ex2_x2a.
  Variables (A : SETop).

  Definition x2a_ob(X : SETop): SET := DHom X A.

  Section x2a_map_def.
    Variable X Y : SETop.

    Section x2a_mor_def.
      Variable f : X --> Y.

      Definition x2a_mor1(g : A --> X) := g o f.
      Lemma x2a_map_law1 : Map_law x2a_mor1.
      Proof.
        unfold Map_law, x2a_mor1 in |- *.
        intros g h H.
        apply Comp_r; assumption.
      Qed.
      Canonical Structure x2a_mor : Map (x2a_ob X) (x2a_ob Y) :=
        x2a_map_law1.
    End x2a_mor_def.

    Lemma x2a_map_law : Map_law x2a_mor.
    Proof.
      unfold Map_law in |- *; simpl in |- *.
      intros f g H.
      unfold Ext. simpl.
      unfold x2a_mor1, x2a_ob in |- *.
      intros h.
      unfold Ext. simpl. intros x.
      apply Pres1. apply H.
    Qed.
    Canonical Structure x2a_map := Build_Map x2a_map_law.
  End x2a_map_def.

  Lemma x2a_comp_law : Fcomp_law x2a_map.
  Proof.
    unfold Fcomp_law.
    intros X Y Z f g.
    unfold x2a_map. simpl.
    unfold x2a_mor, x2a_ob.
    unfold Ext. intros h.
    apply Ass.
  Qed.
  Lemma x2a_id_law : Fid_law x2a_map.
  Proof.
    unfold Fid_law. simpl.
    unfold Ext. simpl.
    unfold Id_fun. simpl.
    unfold x2a_mor1, x2a_ob.
    intros b f. unfold Ext. intros x.
    simpl. unfold Id_fun. apply Refl.
  Qed.
  Canonical Structure x2a_Fun := Build_Functor x2a_comp_law x2a_id_law.
End hw1ex2_x2a.

Check a2x_Fun.
(* ===>
a2x_Fun
     : SET -> Functor SET SET
*)
Check x2a_Fun.
(* ===>
x2a_Fun
     : SETop -> Functor SETop SET
*)

(**
Homework 1, problem 3

(a) Show that Hom is a functor Hom : Cop x C -> Set.

(b) Show that the slice category construction determines a functor
    C/(-) : C -> Cat by composition

**)

Section hw1ex3a.

Variables (Cat : Category).

Let CatOp := Dual Cat.

Let IN := PROD CatOp Cat.

Section fundef.

  Definition homfun_ob(p: IN): SET := @Hom Cat ((Ob_l p): Cat) ((Ob_r p): Cat).

  Section mapdef.
    Variables (p q : IN).

    Section mordef.
      Variable f : p --> q.
      Let A: Cat := Ob_l p.
      Let B: Cat := Ob_r p.
      Let C: Cat := Ob_l q.
      Let D: Cat := Ob_r q.
      Let f1: @Hom Cat C A := Hom_l f.
      Let f2: @Hom Cat B D := Hom_r f.
      Definition homfun_mor1(g: @Hom Cat A B) :=
        f1 o g o f2.

      Lemma homfun_map_law1 : Map_law homfun_mor1.
      Proof.
        unfold Map_law, homfun_mor1 in |- *.
        intros g h H.
        apply Comp_l. apply Comp_r.
        assumption.
      Qed.
      Canonical Structure homfun_mor : Map (homfun_ob p) (homfun_ob q) :=
        homfun_map_law1.
    End mordef.

    Lemma homfun_map_law : Map_law homfun_mor.
    Proof.
      unfold Map_law in |- *; simpl in |- *.
      unfold homfun_mor. unfold Ext. unfold homfun_ob. simpl.
      unfold homfun_mor1.
      intros f g H h.
      inversion H.
      apply Comp_lr; try assumption.
      apply Comp_l; assumption.
    Qed.
    Canonical Structure homfun_map := Build_Map homfun_map_law.
  End mapdef.

  Lemma homfun_comp_law : @Fcomp_law IN SET homfun_ob homfun_map.
  Proof.
    unfold Fcomp_law. simpl.
    intros X Y Z f g.
    unfold homfun_map. simpl.
    unfold homfun_mor, homfun_ob.
    unfold Ext. simpl. intros h. simpl.
    unfold homfun_mor1. simpl.

    apply Trans with (y:=(((Hom_l g: @Hom Cat _ _) o (Hom_l f: @Hom Cat _ _)) o h o Hom_r f o Hom_r g)).
    apply Comp_l. apply Refl.

    remember ((Hom_l g: @Hom Cat _ _) o (Hom_l f: @Hom Cat _ _)) as init.
    remember ((Hom_r f) o (Hom_r g)) as fin.

    apply Trans with (y:=((Hom_l g: @Hom Cat _ _) o (Hom_l f: @Hom Cat _ _)) o (h o Hom_r f) o Hom_r g).
    rewrite Heqinit. apply Comp_l. rewrite Heqfin. apply Ass.
    remember (h o Hom_r f) as hthen.

    apply Trans with (y:=((((Hom_l g: @Hom Cat _ _) o (Hom_l f: @Hom Cat _ _)) o hthen) o Hom_r g)).
    rewrite <- Heqinit. apply Ass.
    apply Trans with (y:=(((((Hom_l g: @Hom Cat _ _) o (Hom_l f: @Hom Cat _ _) o hthen) o Hom_r g)))).
    apply Comp_r. apply Ass1.
    remember ((Hom_l f: @Hom Cat _ _) o hthen) as hround.
    apply Ass1.
  Qed.
  Lemma homfun_id_law : Fid_law homfun_map.
  Proof.
    unfold Fid_law. simpl.
    unfold Ext. simpl.
    unfold homfun_mor1, homfun_ob.
    intros b f. unfold Id_PROD. simpl. unfold Id_fun.
    apply Trans with (y:=f o Id (c:=Cat) (Ob_r b)).
    apply Idl.
    apply Idr1.
  Qed.

  Canonical Structure hom_Fun := Build_Functor homfun_comp_law homfun_id_law.

End fundef.
End hw1ex3a.

Check hom_Fun.
(* ===>
hom_Fun
     : forall Cat : Category, Functor (PROD (Dual Cat) Cat) SET
*)
