Require Import OrderedType.
Require Import Classes.RelationClasses.

Module Node_as_OT (N S:OrderedType) <: OrderedType.
  Module MN := OrderedTypeFacts N.

  Inductive Node : Type :=
  | file : N.t -> S.t -> Node
  | dir : N.t -> list Node -> Node.

  Definition t := Node.

  Definition eq (x1 x2:Node) : Prop :=
    match x1, x2 with
    | dir n1 _, dir n2 _ => N.eq n1 n2
    | file n1 s1, file n2 s2 => N.eq n1 n2 /\ S.eq s1 s2
    | _, _ => False
    end.

  Definition lt (x1 x2:Node) : Prop :=
    match x1, x2 with
    | dir n1 _, dir n2 _ => N.lt n1 n2
    | dir n1 _, file n2 _ => N.lt n1 n2
    | file n1 _, dir n2 _ => N.lt n1 n2 \/ N.eq n1 n2
    | file n1 s1, file n2 s2 => (N.lt n1 n2) \/ (N.eq n1 n2 /\ S.lt s1 s2)
    end.

  Lemma eq_refl : Reflexive eq.
  Proof.
    hnf. destruct x; simpl.
    - split; [apply N.eq_refl | apply S.eq_refl].
    - apply N.eq_refl.
  Qed.

  Lemma eq_sym : Symmetric eq.
  Proof.
    hnf. intros. destruct x, y; simpl in *; try contradiction.
    - destruct H. apply N.eq_sym in H. apply S.eq_sym in H0.
      split; assumption.
    - apply N.eq_sym in H. assumption.
  Qed.

  Lemma eq_trans : Transitive eq.
  Proof.
    hnf. intros. destruct x, y, z; simpl in *; try contradiction.
    - destruct H, H0. split; [apply (N.eq_trans H H0) | apply (S.eq_trans H1 H2)].
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

  Lemma lt_trans : forall (x y z:Node), lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x, y, z; simpl_lt_cases.
    all: try assumption || (left; assumption) ||
             (right; split; [reflexivity | assumption]).
    - assert (S.lt t1 t5); [revert H2 H1; apply S.lt_trans|].
      right. split; assumption.
    - right. assumption.
  Qed.

  Lemma lt_not_eq : forall (x y:Node), lt x y -> ~ eq x y.
  Proof.
    intros. unfold not; intro. destruct x, y; simpl in *; try contradiction.
    - destruct H, H0.
      + contradiction (N.lt_not_eq H).
      + destruct H. contradiction (S.lt_not_eq H2).
    - contradiction (N.lt_not_eq H).
  Qed.

  Definition compare : forall (x y:Node), Compare lt eq x y.
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
    - destruct (S.compare t1 t3).
      + apply LT. simpl. right. split; assumption.
      + apply EQ. simpl. split; assumption.
      + apply GT. simpl. right. split; [apply (N.eq_sym e) | assumption].
    - apply LT. simpl. right. assumption.
    - apply GT. simpl. right. apply (N.eq_sym e).
    - apply EQ. simpl. assumption.
  Qed.

  Definition eq_dec : forall (x y:Node), {eq x y} + {~ eq x y}.
  Proof.
    intros. destruct x, y; simpl; try auto.
    - case_eq (N.eq_dec t0 t2); case_eq (S.eq_dec t1 t3); intros;
        try (left; split; assumption) ||
            (right; unfold not; intro; destruct H1; contradiction).
    - apply N.eq_dec.
  Qed.
End Node_as_OT.
