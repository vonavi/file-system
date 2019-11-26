Set Implicit Arguments.
Require Import Arith.PeanoNat.
Require Import ArithRing.
Require Import FunInd.
Require Import Init.Datatypes.
Require Import Lists.List.
Require Import Recdef.

Add LoadPath ".".
Require Import Node.

Section Defs.
  Variables Name Tag : Type.
  Definition FileSystem := list (Node Name Tag).
End Defs.

Section FSLevel.
  Variables Name Tag : Type.

  Fixpoint node_level (x:Node Name Tag) : nat :=
    match x with
    | file _ _ => 1
    | dir _ fs => S (fold_right (fun x => Nat.max (node_level x)) O fs)
    end.

  Definition fs_level (fs:FileSystem Name Tag) : nat :=
    fold_right (fun x => Nat.max (node_level x)) O fs.

  Lemma level_eq : forall (x:Node Name Tag),
      node_level x = fs_level (x :: nil).
  Proof.
    intro. simpl. symmetry. apply Nat.max_0_r.
  Qed.

  Lemma node_level_gt_1 : forall (x:Node Name Tag), 1 <= node_level x.
  Proof.
    intro x. destruct x. 1:auto. simpl. rewrite <- Nat.succ_le_mono.
    induction l; simpl. 1:auto. apply Nat.max_le_iff. right. assumption.
  Qed.

  Lemma fs_level_gt_1 : forall (fs:FileSystem Name Tag),
      nil <> fs -> 1 <= fs_level fs.
  Proof.
    intros. destruct fs. 1:contradiction. simpl.
    apply Nat.max_le_iff. left. apply node_level_gt_1.
  Qed.

  Lemma level_cons : forall (x:Node Name Tag) (fs:FileSystem Name Tag),
      fs_level (x :: fs) = Nat.max (node_level x) (fs_level fs).
  Proof.
    intros. simpl. f_equal.
  Qed.

  Lemma level_concat : forall (fs fs':FileSystem Name Tag),
      fs_level (fs ++ fs') = Nat.max (fs_level fs) (fs_level fs').
  Proof.
    intros. induction fs; simpl. 1:reflexivity. rewrite IHfs.
    rewrite Nat.max_assoc. reflexivity.
  Qed.

  Definition node_split (x:Node Name Tag) :
    (Node Name Tag * FileSystem Name Tag)%type :=
    match x with
    | file _ _ => (x, nil)
    | dir n fs => (dir n nil, fs)
    end.

  Definition fs_split (fs:FileSystem Name Tag) :
    (FileSystem Name Tag * FileSystem Name Tag)%type :=
    let node_acc pair acc := (fst pair :: fst acc, snd pair ++ snd acc)
    in fold_right node_acc (nil, nil) (map node_split fs).

  Lemma split_eq : forall (x h:Node Name Tag) (t:FileSystem Name Tag),
      (h, t) = node_split x -> (h :: nil, t) = fs_split (x :: nil).
  Proof.
    intros. unfold fs_split. simpl. rewrite app_nil_r.
    rewrite surjective_pairing in H. inversion H. reflexivity.
  Qed.
  Arguments split_eq {_ _ _}.

  Lemma split_cons : forall (x h:Node Name Tag) (fs t l r:FileSystem Name Tag),
      (h, t) = node_split x -> (l, r) = fs_split fs ->
      (h :: l, t ++ r) = fs_split (x :: fs).
  Proof.
    intros. rewrite surjective_pairing in H, H0.
    inversion H. inversion H0. apply injective_projections; f_equal.
  Qed.
  Arguments split_cons {_ _ _ _ _ _}.

  Lemma split_concat : forall (fs fs' l l' r r':FileSystem Name Tag),
      (l, r) = fs_split fs -> (l', r') = fs_split fs' ->
      (l ++ l', r ++ r') = fs_split (fs ++ fs').
  Proof.
    intros. revert fs l r H. induction fs; intros.
    - inversion H. do 3 rewrite app_nil_l. assumption.
    - remember (fs_split fs) as p. rewrite Heqp in IHfs.
      pattern p in Heqp. rewrite surjective_pairing in Heqp.
      specialize (IHfs (fst p) (snd p) Heqp).
      remember (node_split a) as q. pattern q in Heqq.
      rewrite surjective_pairing in Heqq. rewrite <- app_comm_cons.
      rewrite <- (split_cons Heqq IHfs). pose proof (split_cons Heqq Heqp).
      rewrite <- H1 in H. inversion H. rewrite <- app_assoc.
      apply injective_projections; reflexivity.
  Qed.

  Lemma split_l_split : forall (fs l r:FileSystem Name Tag),
      (l, r) = fs_split fs -> (l, nil) = fs_split l.
  Proof.
    intro fs. induction fs; intros l r H.
    - inversion H. unfold fs_split. reflexivity.
    - remember (fs_split fs) as p. rewrite Heqp in IHfs.
      pattern p in Heqp. rewrite surjective_pairing in Heqp.
      specialize (IHfs (fst p) (snd p) Heqp).
      remember (node_split a) as q. pattern q in Heqq.
      rewrite surjective_pairing in Heqq.
      rewrite <- (split_cons Heqq Heqp) in H. inversion H.
      assert ((fst q, nil) = node_split (fst q)).
      + destruct a; simpl in Heqq; inversion Heqq; rewrite H3;
          apply injective_projections; simpl; assumption || reflexivity.
      + rewrite <- (split_cons H0 IHfs). apply injective_projections; auto.
  Qed.
  Arguments split_l_split {_ _ _}.

  Lemma node_split_l_level : forall (x h:Node Name Tag) (t:FileSystem Name Tag),
      (h, t) = node_split x -> node_level h = 1.
  Proof.
    intros. destruct x; simpl in H; inversion H; reflexivity.
  Qed.
  Arguments node_split_l_level {_ _ _}.

  Lemma node_split_r_level : forall (x h:Node Name Tag) (t:FileSystem Name Tag),
      (h, t) = node_split x -> S (fs_level t) = node_level x.
  Proof.
    intros. destruct x; simpl in *; inversion H; reflexivity.
  Qed.
  Arguments node_split_r_level {_ _ _}.

  Lemma fs_split_level : forall (fs l r:FileSystem Name Tag),
      nil <> fs -> (l, r) = fs_split fs ->
      fs_level fs = Nat.max (fs_level l) (S (fs_level r)).
  Proof.
    intro fs. destruct fs. 1:contradiction.
    revert n. induction fs; intros.
    - simpl. remember (node_split n) as p. pattern p in Heqp.
      rewrite surjective_pairing in Heqp. rewrite <- (split_eq Heqp) in H0.
      inversion H0. simpl. do 2 rewrite Nat.max_0_r.
      rewrite (node_split_l_level Heqp). rewrite <- (node_split_r_level Heqp).
      simpl. reflexivity.
    - remember (fs_split (a :: fs)) as p. pattern p in Heqp.
      rewrite surjective_pairing in Heqp. specialize (IHfs a (fst p) (snd p)).
      assert (nil <> a :: fs). 1:discriminate. specialize (IHfs H1 Heqp).
      remember (node_split n) as q. pattern q in Heqq.
      rewrite surjective_pairing in Heqq. pose proof (split_cons Heqq Heqp).
      rewrite <- H2 in H0. inversion H0. rewrite level_cons. rewrite IHfs.
      rewrite level_concat. rewrite Nat.succ_max_distr.
      do 2 rewrite Nat.max_assoc. f_equal.
      rewrite <- (node_split_r_level Heqq). rewrite Nat.max_comm. f_equal.
      rewrite level_cons. rewrite (node_split_l_level Heqq).
      symmetry. apply Nat.max_r_iff. destruct (fst p).
      + unfold fs_split in Heqp. simpl in Heqp. inversion Heqp.
      + assert (nil <> n0 :: f). 1:discriminate. apply (fs_level_gt_1 H3).
  Qed.
  Arguments fs_split_level {_ _ _}.

  Function fold_level
           (A:Type) (f:Node Name Tag->A->A) (a0:A) (fs:FileSystem Name Tag)
           {measure fs_level fs} : A :=
    match fs with
    | nil => a0
    | _ => match fs_split fs with
             (l, r) => fold_right f (fold_level f a0 r) l
           end
    end.
  Proof.
    intros. assert (nil <> n :: l). 1:apply nil_cons. symmetry in teq0.
    rewrite (fs_split_level H teq0). apply Nat.max_lt_iff. right. auto.
  Qed.

  Lemma fold_level_nil : forall (A:Type) (f:Node Name Tag->A->A) (a0:A),
      fold_level f a0 nil = a0.
  Proof.
    intros. remember nil as fs. functional induction (fold_level f a0 fs).
    1:reflexivity. inversion e0. symmetry in H1. specialize (IHa H1).
    rewrite H1 in IHa. rewrite IHa. reflexivity.
  Qed.

  Lemma split_fold_level :
    forall (A:Type) (f:Node Name Tag->A->A) (a0:A) (fs l r:FileSystem Name Tag),
      (l, r) = fs_split fs ->
      fold_level f a0 fs = fold_right f (fold_level f a0 r) l.
  Proof.
    intros A f a0 fs. functional induction (fold_level f a0 fs); intros.
    - inversion H. rewrite fold_level_nil. reflexivity.
    - rewrite e0 in H. inversion H. reflexivity.
  Qed.
  Arguments split_fold_level {_} _ _ {_ _ _}.

  Lemma split_l_fold_level :
    forall (A:Type) (f:Node Name Tag->A->A) (a0:A) (fs l r:FileSystem Name Tag),
      (l, r) = fs_split fs -> fold_level f a0 l = fold_right f a0 l.
  Proof.
    intros A f a0 fs. functional induction (fold_level f a0 fs); intros l' r' H.
    - inversion H. rewrite fold_level_nil. reflexivity.
    - rewrite e0 in H. inversion H. symmetry in e0. pose proof (split_l_split e0).
      rewrite (split_fold_level f a0 H0). rewrite fold_level_nil. reflexivity.
  Qed.
  Arguments split_l_fold_level {_} _ _ {_ _ _}.
End FSLevel.

Section FSTree.
  Variables Name Tag : Type.

  Definition size (fs:FileSystem Name Tag) : nat := fold_level (fun _ => S) O fs.

  Lemma split_size : forall (fs l r:FileSystem Name Tag),
      (l, r) = fs_split fs -> size fs = length l + size r.
  Proof.
    intros fs. unfold size.
    functional induction (fold_level (fun _ => S) O fs); intros l' r' H.
    - unfold fs_split in H. simpl in H. inversion H. rewrite fold_level_nil.
      reflexivity.
    - rewrite e0 in H. inversion H.
      remember (fold_level (fun _ => S) 0 r) as n.
      clear IHs H H1 H2 Heqn e0 fs l' r r' y. induction l. 1:reflexivity.
      simpl. rewrite IHl. reflexivity.
  Qed.
  Arguments split_size {_ _ _}.

  Lemma size_ge_0 : forall (fs:FileSystem Name Tag), 0 <= size fs.
  Proof.
    intro fs. functional induction (fold_level (fun _ => S) O fs).
    - unfold size. rewrite fold_level_nil. trivial.
    - symmetry in e0. rewrite (split_size e0). pattern 0. rewrite <- Nat.add_0_r.
      apply Nat.add_le_mono.
      + clear e0 IHs fs r y. induction l. 1:reflexivity. simpl. revert IHl.
        apply Nat.le_le_succ_r.
      + assumption.
  Qed.

  Lemma size_concat : forall (fs fs':FileSystem Name Tag),
      size (fs ++ fs') = size fs + size fs'.
  Proof.
    intro fs. functional induction (fold_level (fun _ => S) O fs); intro fs'.
    - rewrite app_nil_l. unfold size. rewrite fold_level_nil. trivial.
    - remember (fs_split fs') as p. pattern p in Heqp.
      rewrite surjective_pairing in Heqp. symmetry in e0.
      pose proof (split_concat fs fs' e0 Heqp). rewrite (split_size H).
      rewrite (IHs (snd p)). rewrite (split_size Heqp).
      do 2 rewrite Nat.add_assoc. apply Nat.add_cancel_r. rewrite (split_size e0).
      cut (length (l ++ fst p) = length l + length (fst p)).
      + intro. rewrite H0. ring.
      + apply app_length.
  Qed.
End FSTree.
