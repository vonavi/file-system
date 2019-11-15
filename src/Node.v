Require Import OrderedType.
Require Import Classes.RelationClasses.
Require Import Arith.PeanoNat.

Definition Name := nat.
Definition Storage := nat.

Inductive Node : Set :=
| file : Name -> Storage -> Node
| dir : Name -> list Node -> Node.

Module Node_as_OT <: OrderedType.
  Definition t := Node.

  Definition eq (x1 x2:Node) : Prop :=
    match x1, x2 with
    | dir n1 _, dir n2 _ => n1 = n2
    | file n1 s1, file n2 s2 => n1 = n2 /\ s1 = s2
    | _, _ => False
    end.

  Definition lt (x1 x2:Node) : Prop :=
    match x1, x2 with
    | dir n1 _, dir n2 _ => n1 < n2
    | dir n1 _, file n2 _ => n1 < n2
    | file n1 _, dir n2 _ => n1 <= n2
    | file n1 s1, file n2 s2 => (n1 < n2) \/ (n1 = n2 /\ s1 < s2)
    end.

  Lemma eq_refl : Reflexive eq.
  Proof.
    hnf. destruct x; split; reflexivity.
  Qed.

  Lemma eq_sym : Symmetric eq.
  Proof.
    hnf. intros. destruct x, y; inversion H.
    - rewrite H0, H1. split; reflexivity.
    - reflexivity.
  Qed.

  Lemma eq_trans : Transitive eq.
  Proof.
    hnf. intros. destruct x, y, z; inversion H; inversion H0.
    - rewrite H1, H2, <- H3, <- H4. apply eq_refl.
    - reflexivity.
  Qed.

  Ltac destruct_eq :=
    let Heq := fresh
    in match goal with
       | H : ?n = ?n0 /\ _ |- _ =>
         destruct H as [Heq *]; rewrite Heq || rewrite <- Heq; clear Heq
       end.

  Ltac simpl_cases :=
    intros; simpl in *;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           end;
    repeat destruct_eq;
    match goal with
    | H : ?n < ?n0, H0 : ?n0 < ?n1 |- _ =>
      assert (n < n1); [revert H H0; apply Nat.lt_trans|]; clear H H0
    | H : ?n < ?n0, H0 : ?n0 <= ?n1 |- _ =>
      assert (n < n1); [revert H H0; apply Nat.lt_le_trans|]; clear H H0
    | H : ?n <= ?n0, H0 : ?n0 < ?n1 |- _ =>
      assert (n < n1); [revert H H0; apply Nat.le_lt_trans|]; clear H H0
    | _ => idtac
    end.

  Lemma lt_trans : forall (x y z:Node), lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x, y, z; simpl; case_eq (Nat.lt_ge_cases n n1); simpl_cases.
    all: try assumption || (left; assumption) ||
             (right; split; [reflexivity | assumption]).
    all: apply Nat.lt_le_incl; assumption.
  Qed.

  Lemma lt_not_eq : forall (x y:Node), lt x y -> ~ eq x y.
  Proof.
    intros. unfold not. destruct x, y; simpl in *; try trivial.
    - intro. destruct H; destruct H0.
      + rewrite H0 in H. contradiction (Nat.lt_irrefl n0).
      + destruct H. rewrite H1 in H2. contradiction (Nat.lt_irrefl s0).
    - intro. rewrite H0 in H. contradiction (Nat.lt_irrefl n0).
  Qed.

  Ltac simpl_compare :=
    match goal with
    | H : (_ ?= _) = Eq |- _ =>
      rewrite Nat.compare_eq_iff in H; rewrite H; clear H
    | H : (_ ?= _) = Lt |- _ => rewrite Nat.compare_lt_iff in H; apply LT; simpl
    | H : (_ ?= _) = Gt |- _ => rewrite Nat.compare_gt_iff in H; apply GT; simpl
    end;
    try assumption || (left; assumption) || (apply Nat.lt_le_incl; assumption).

  Definition compare : forall (x y:Node), Compare lt eq x y.
  Proof.
    intros; destruct x, y; case_eq (n ?= n0); intro; simpl_compare.
    - case_eq (s ?= s0); intro.
      + apply Nat.compare_eq_iff in H. rewrite H. apply EQ. split; reflexivity.
      + apply Nat.compare_lt_iff in H. apply LT.
        right. split; [reflexivity | assumption].
      + apply Nat.compare_gt_iff in H. apply GT.
        right. split; [reflexivity | assumption].
    - apply LT. simpl. reflexivity.
    - apply GT. simpl. reflexivity.
    - apply EQ. simpl. reflexivity.
  Qed.

  Definition eq_dec : forall (x y:Node), {eq x y} + {~ eq x y}.
  Proof.
    intros. destruct x, y; simpl; try auto.
    - case_eq (Nat.eq_dec n n0); case_eq (Nat.eq_dec s s0); intros;
        try (left; split; assumption) ||
            (right; unfold not; intro; destruct H1; contradiction).
    - apply Nat.eq_dec.
  Qed.
End Node_as_OT.
