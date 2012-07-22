Require Import ConCaT.CATEGORY_THEORY.CATEGORY.Category.
Require Import ConCaT.CATEGORY_THEORY.CATEGORY.Dual.
Require Import ConCaT.CATEGORY_THEORY.CATEGORY.SET.
Require Import ConCaT.CATEGORY_THEORY.FUNCTOR.Functor.
Require Import ConCaT.CATEGORY_THEORY.FUNCTOR.Dual_Functor.

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
