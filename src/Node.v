Require Import Arith.PeanoNat.
Require Import Classes.RelationClasses.

Definition Name := nat.
Definition Storage := nat.

Inductive Node : Set :=
| file : Name -> Storage -> Node
| dir : Name -> list Node -> Node.

(*****************)
(* Node equality *)
(*****************)

Definition eq_node (x1 x2:Node) : Prop :=
  match x1, x2 with
  | dir n1 _, dir n2 _ => n1 = n2
  | file n1 s1, file n2 s2 => n1 = n2 /\ s1 = s2
  | _, _ => False
  end.

Lemma eq_node_refl : Reflexive eq_node.
Proof.
  hnf. destruct x; split; reflexivity.
Qed.

Lemma eq_node_sym : Symmetric eq_node.
Proof.
  hnf. intros. destruct x, y; inversion H.
  - rewrite H0, H1. split; reflexivity.
  - reflexivity.
Qed.

Lemma eq_node_trans : Transitive eq_node.
Proof.
  hnf. intros. destruct x, y, z; inversion H; inversion H0.
  - rewrite H1, H2, <- H3, <- H4. apply eq_node_refl.
  - reflexivity.
Qed.

Instance eq_node_equiv : Equivalence eq_node.
Proof.
  constructor; [apply eq_node_refl | apply eq_node_sym | apply eq_node_trans].
Qed.

(*******************)
(* Node comparison *)
(*******************)

Definition compare_node (x1 x2:Node) : comparison :=
  match x1, x2 with
  | dir n1 _, dir n2 _ => n1 ?= n2
  | dir n1 _, file n2 _ => let cmp := n1 ?= n2
                           in match cmp with
                              | Eq => Gt
                              | _ => cmp
                              end
  | file n1 _, dir n2 _ => let cmp := n1 ?= n2
                           in match cmp with
                              | Eq => Lt
                              | _ => cmp
                              end
  | file n1 s1, file n2 s2 => let cmp := n1 ?= n2
                              in match cmp with
                                 | Eq => s1 ?= s2
                                 | _ => cmp
                                 end
  end.

Lemma compare_node_sym :
  forall (x y:Node), compare_node y x = CompOpp (compare_node x y).
Proof.
  intros. destruct x, y; simpl; case_eq (n ?= n0); intro;
            rewrite Nat.compare_antisym; rewrite H; simpl;
              reflexivity || apply Nat.compare_antisym.
Qed.

Lemma compare_node_Eq :
  forall (x y:Node), compare_node x y = Eq <-> eq_node x y.
Proof.
  destruct x, y; simpl; case_eq (n ?= n0); intro.
  all: match goal with
       | |- _ <-> False =>
         split; intro; inversion H0
       | H : _ = Eq |- _ =>
         rewrite Nat.compare_eq_iff in H
       | _ =>
         split; intro; inversion H0; rewrite <- Nat.compare_eq_iff in H1;
           rewrite H1 in H; inversion H
       end.
  - rewrite Nat.compare_eq_iff. split; intro; [split | inversion H0]; assumption.
  - split; intro; [assumption | reflexivity].
Qed.

Lemma compare_node_Eq_trans : forall (x y z:Node),
    compare_node x y = Eq -> compare_node y z = Eq -> compare_node x z = Eq.
Proof.
  intros. apply compare_node_Eq. apply compare_node_Eq in H.
  apply compare_node_Eq in H0. transitivity y; assumption.
Qed.

Ltac destruct_compare_node :=
  let Hc := fresh
  in match goal with
     | H : context [match (?n ?= ?n0) with _ => _ end] |- _ =>
       case_eq (n ?= n0); intro Hc; rewrite Hc in H; inversion H; clear H
     end.

Ltac contradict_compare_node :=
  let Hn := fresh
  in simpl in *; repeat destruct_compare_node;
     repeat match goal with
            | H : (_ ?= _) = Eq |- _ =>
              rewrite Nat.compare_eq_iff in H; try rewrite H in *; clear H
            | H : (_ ?= _) = Lt |- _ =>
              try rewrite H in *; rewrite Nat.compare_lt_iff in H
            | H : (_ ?= _) = Gt |- _ =>
              try rewrite H in *; rewrite Nat.compare_gt_iff in H
            end;
     try discriminate;
     match goal with
     | H : ?n < ?n0, H0: ?n0 < ?n1 |- _ =>
       assert (Hn: n < n1); [ revert H H0; apply Nat.lt_trans |]
     | _ => idtac
     end;
     match goal with
     | H : ?n < ?n |- _ => contradiction (Nat.lt_irrefl n)
     | H : ?n < ?n0, H0 : ?n0 < ?n |- _ => contradiction (Nat.lt_asymm n n0)
     | _ => idtac
     end.

Lemma compare_node_Lt_trans : forall (x y z:Node),
    compare_node x y = Lt -> compare_node y z = Lt -> compare_node x z = Lt.
Proof.
  intros. destruct x, y, z; simpl; case_eq (n ?= n1); intro; try reflexivity;
            contradict_compare_node. rewrite Nat.compare_lt_iff. assumption.
Qed.

Lemma compare_node_Gt_trans : forall (x y z:Node),
    compare_node x y = Gt -> compare_node y z = Gt -> compare_node x z = Gt.
Proof.
  intros. apply (f_equal CompOpp) in H. apply (f_equal CompOpp) in H0.
  rewrite <- compare_node_sym in H, H0. simpl in H, H0.
  pose proof (compare_node_Lt_trans z y x H0 H). apply (f_equal CompOpp) in H1.
  rewrite <- compare_node_sym in H1. assumption.
Qed.

Lemma compare_node_trans : forall (c:comparison) (x y z:Node),
    compare_node x y = c -> compare_node y z = c -> compare_node x z = c.
Proof.
  destruct c.
  - apply compare_node_Eq_trans.
  - apply compare_node_Lt_trans.
  - apply compare_node_Gt_trans.
Qed.
