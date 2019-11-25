Set Implicit Arguments.
Require Import OrderedType.
Require Import Classes.RelationClasses.

Section Node.
  Variables Name Tag : Type.
  Inductive Node : Type :=
  | file : Name -> Tag -> Node
  | dir : Name -> list Node -> Node.
End Node.

Module Node_as_OT (N T:OrderedType) <: OrderedType.
  Module MN := OrderedTypeFacts N.
  Module MT := OrderedTypeFacts T.

  Definition t := Node N.t T.t.

  Definition eq (x1 x2 : t) : Prop :=
    match x1, x2 with
    | @dir _ _ n1 _, @dir _ _ n2 _ => N.eq n1 n2
    | @file _ _ n1 s1, @file _ _ n2 s2 => N.eq n1 n2 /\ T.eq s1 s2
    | _, _ => False
    end.

  Definition lt (x1 x2 : t) : Prop :=
    match x1, x2 with
    | @dir _ _ n1 _, @dir _ _ n2 _ => N.lt n1 n2
    | @dir _ _ n1 _, @file _ _ n2 _ => N.lt n1 n2
    | @file _ _ n1 _, @dir _ _ n2 _ => N.lt n1 n2 \/ N.eq n1 n2
    | @file _ _ n1 s1, @file _ _ n2 s2 => (N.lt n1 n2) \/ (N.eq n1 n2 /\ T.lt s1 s2)
    end.

  Lemma eq_refl : Reflexive eq.
  Proof.
    hnf. destruct x; simpl.
    - split; [apply N.eq_refl | apply T.eq_refl].
    - apply N.eq_refl.
  Qed.

  Lemma eq_sym : Symmetric eq.
  Proof.
    hnf. intros. destruct x, y; simpl in *; try contradiction.
    - destruct H. apply N.eq_sym in H. apply T.eq_sym in H0.
      split; assumption.
    - apply N.eq_sym in H. assumption.
  Qed.

  Lemma eq_trans : Transitive eq.
  Proof.
    hnf. intros. destruct x, y, z; simpl in *; try contradiction.
    - destruct H, H0. split; [apply (N.eq_trans H H0) | apply (T.eq_trans H1 H2)].
    - apply (N.eq_trans H H0).
  Qed.

  Ltac simpl_lt_cases :=
    intros; simpl in *;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end;
    match goal with
    | H : N.lt ?n ?n0, H0: N.lt ?n0 ?n1 |- _ =>
      assert (N.lt n n1); [apply (N.lt_trans H H0) | clear H H0]
    | H : N.eq ?n ?n0, H0: N.lt ?n0 ?n1 |- _ =>
      assert (N.lt n n1); [apply (MN.eq_lt H H0) | clear H H0]
    | H : N.lt ?n ?n0, H0: N.eq ?n0 ?n1 |- _ =>
      assert (N.lt n n1); [apply (MN.lt_eq H H0) | clear H H0]
    | H : N.eq ?n ?n0, H0 : N.eq ?n0 ?n1 |- _ =>
      assert (N.eq n n1); [apply (N.eq_trans H H0) | clear H H0]
    | _ => idtac
    end.

  Lemma lt_trans : forall (x y z : t), lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x, y, z; simpl_lt_cases.
    all: try assumption || (left; assumption) ||
             (right; split; [reflexivity | assumption]).
    - assert (T.lt t1 t5); [revert H2 H1; apply T.lt_trans|].
      right. split; assumption.
    - right. assumption.
  Qed.

  Lemma lt_not_eq : forall (x y : t), lt x y -> ~ eq x y.
  Proof.
    intros. unfold not; intro. destruct x, y; simpl in *; try contradiction.
    - destruct H, H0.
      + contradiction (N.lt_not_eq H).
      + destruct H. contradiction (T.lt_not_eq H2).
    - contradiction (N.lt_not_eq H).
  Qed.

  Definition compare : forall (x y : t), Compare lt eq x y.
  Proof.
    intros; destruct x, y;
      [case_eq (N.compare t0 t2) | case_eq (N.compare t0 t2) |
       case_eq (N.compare t0 t1) | case_eq (N.compare t0 t1)]; intros.
    all: match goal with
         | H : N.compare _ _ = LT _ |- _ =>
           apply LT; simpl; try assumption || (left; assumption)
         | H : N.compare _ _ = GT _ |- _ =>
           apply GT; simpl; try assumption || (left; assumption)
         | _ => idtac
         end.
    - destruct (T.compare t1 t3).
      + apply LT. simpl. right. split; assumption.
      + apply EQ. simpl. split; assumption.
      + apply GT. simpl. right. split; [apply (N.eq_sym e) | assumption].
    - apply LT. simpl. right. assumption.
    - apply GT. simpl. right. apply (N.eq_sym e).
    - apply EQ. simpl. assumption.
  Qed.

  Definition eq_dec : forall (x y : t), {eq x y} + {~ eq x y}.
  Proof.
    intros. destruct x, y; simpl; try auto.
    - case_eq (N.eq_dec t0 t2); case_eq (T.eq_dec t1 t3); intros;
        try (left; split; assumption) ||
            (right; unfold not; intro; destruct H1; contradiction).
    - apply N.eq_dec.
  Qed.
End Node_as_OT.
