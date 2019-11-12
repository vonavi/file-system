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
  intros. case_eq (compare_node x y); destruct x; destruct y; simpl;
            case_eq (n ?= n0); intros; rewrite Nat.compare_antisym; rewrite H;
              simpl; reflexivity || inversion H0; rewrite Nat.compare_antisym;
                rewrite H0; reflexivity.
Qed.

Lemma compare_node_Eq :
  forall (x y:Node), compare_node x y = Eq <-> eq_node x y.
Proof.
  split; intros; destruct x, y; simpl in *.
  - case_eq (n ?= n0); intro H0; rewrite H0 in H; inversion H.
    rewrite Nat.compare_eq_iff in H, H0. rewrite H, H0. split; reflexivity.
  - case_eq (n ?= n0); intro H0; rewrite H0 in H; inversion H.
  - case_eq (n ?= n0); intro H0; rewrite H0 in H; inversion H.
  - rewrite Nat.compare_eq_iff in H. assumption.
  - destruct H. rewrite <- Nat.compare_eq_iff in H, H0.
    rewrite H, H0. reflexivity.
  - inversion H.
  - inversion H.
  - apply Nat.compare_eq_iff. assumption.
Qed.

Lemma compare_node_Eq_trans : forall (x y z:Node),
    compare_node x y = Eq -> compare_node y z = Eq -> compare_node x z = Eq.
Proof.
  intros. apply compare_node_Eq. apply compare_node_Eq in H.
  apply compare_node_Eq in H0. transitivity y; assumption.
Qed.

Lemma compare_node_Lt_trans : forall (x y z:Node),
    compare_node x y = Lt -> compare_node y z = Lt -> compare_node x z = Lt.
Proof.
  intros. destruct x, z; simpl; case_eq (n ?= n0); intro; try reflexivity.
  - case_eq (s ?= s0); intro.
    + rewrite Nat.compare_eq_iff in H1, H2. rewrite <- H1, <- H2 in H0.
      rewrite compare_node_sym in H. rewrite H0 in H. discriminate H.
    + reflexivity.
    + apply Nat.compare_eq_iff in H1. rewrite <- H1 in H0.
      destruct y; simpl in H, H0; case_eq (n ?= n1); intro; rewrite H3 in H;
        apply (f_equal CompOpp) in H3; rewrite <- Nat.compare_antisym in H3;
          rewrite H3 in H0; simpl in H0; inversion H; inversion H0.
      rewrite Nat.compare_lt_iff in H, H0. pose proof (Nat.lt_trans s s1 s0 H H0).
      apply Nat.lt_asymm in H4. apply Nat.compare_ngt_iff in H4.
      contradiction.
  - destruct y; simpl in H, H0; case_eq (n ?= n1); case_eq (n1 ?= n0); intros;
      rewrite H3 in H; rewrite H2 in H0; inversion H; inversion H0.
    + rewrite Nat.compare_eq_iff in H2, H3. rewrite <- H2, H3 in H1.
      rewrite Nat.compare_refl in H1. inversion H1.
    + apply Nat.compare_eq_iff in H3. rewrite <- H3 in H2. rewrite H2 in H1.
      inversion H1.
    + apply Nat.compare_eq_iff in H2. rewrite H2 in H3. rewrite H3 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
    + apply Nat.compare_eq_iff in H3. rewrite <- H3 in H2. rewrite H2 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
  - destruct y; simpl in H, H0; case_eq (n ?= n1); case_eq (n1 ?= n0); intros;
      rewrite H3 in H; rewrite H2 in H0; inversion H; inversion H0.
    + rewrite Nat.compare_eq_iff in H2, H3. rewrite <- H2, H3 in H1.
      rewrite Nat.compare_refl in H1. inversion H1.
    + apply Nat.compare_eq_iff in H3. rewrite <- H3 in H2. rewrite H2 in H1.
      inversion H1.
    + apply Nat.compare_eq_iff in H2. rewrite H2 in H3. rewrite H3 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
    + apply Nat.compare_eq_iff in H3. rewrite <- H3 in H2. rewrite H2 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
  - apply Nat.compare_eq_iff in H1. rewrite <- H1 in H0.
    destruct y; simpl in H, H0; case_eq (n ?= n1); intro; rewrite H2 in H;
      apply (f_equal CompOpp) in H2; rewrite <- Nat.compare_antisym in H2;
        rewrite H2 in H0; simpl in H0; inversion H; inversion H0.
  - destruct y; simpl in H, H0; case_eq (n ?= n1); case_eq (n1 ?= n0); intros;
      rewrite H3 in H; rewrite H2 in H0; inversion H; inversion H0.
    + rewrite Nat.compare_eq_iff in H2. rewrite H2 in H3. rewrite H3 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
  - apply Nat.compare_eq_iff in H1. rewrite <- H1 in H0.
    destruct y; simpl in H, H0; case_eq (n ?= n1); intro; rewrite H2 in H;
      apply (f_equal CompOpp) in H2; rewrite <- Nat.compare_antisym in H2;
        rewrite H2 in H0; simpl in H0; inversion H; inversion H0.
  - destruct y; simpl in H, H0; case_eq (n ?= n1); case_eq (n1 ?= n0); intros;
      rewrite H3 in H; rewrite H2 in H0; inversion H; inversion H0.
    + rewrite Nat.compare_eq_iff in H2. rewrite H2 in H3. rewrite H3 in H1.
      inversion H1.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
    + rewrite Nat.compare_lt_iff in H2, H3.
      pose proof (Nat.lt_trans n n1 n0 H3 H2). apply Nat.lt_asymm in H4.
      apply Nat.compare_ngt_iff in H4. contradiction.
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
