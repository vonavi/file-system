Set Implicit Arguments.
Require Import Arith.PeanoNat.
Require Import FunInd.
Require Import Init.Datatypes.
Require Import Lists.List.
Require Import Recdef.

Add LoadPath ".".
Require Import Node.

Section FSLevel.
  Variables Name Storage : Type.
  Definition Node := @Node Name Storage.
  Definition FileSystem := list Node.

  Fixpoint node_level (x:Node) : nat :=
    match x with
    | file _ _ => 1
    | dir _ fs => S (fold_right (fun x => Nat.max (node_level x)) O fs)
    end.

  Definition fs_level (fs:FileSystem) : nat :=
    fold_right (fun x => Nat.max (node_level x)) O fs.

  Lemma level_eq : forall (x:Node), node_level x = fs_level (x :: nil).
  Proof.
    intro. simpl. symmetry. apply Nat.max_0_r.
  Qed.

  Lemma node_level_gt_1 : forall (x:Node), 1 <= node_level x.
  Proof.
    intro x. destruct x. 1:auto. simpl. rewrite <- Nat.succ_le_mono.
    induction l; simpl. 1:auto. apply Nat.max_le_iff. right. assumption.
  Qed.

  Lemma fs_level_gt_1 : forall (fs:FileSystem), nil <> fs -> 1 <= fs_level fs.
  Proof.
    intros. destruct fs. 1:contradiction. simpl.
    apply Nat.max_le_iff. left. apply node_level_gt_1.
  Qed.

  Lemma level_cons : forall (x:Node) (fs:FileSystem),
      fs_level (x :: fs) = Nat.max (node_level x) (fs_level fs).
  Proof.
    intros. simpl. f_equal.
  Qed.

  Lemma level_concat : forall (fs fs':FileSystem),
      fs_level (fs ++ fs') = Nat.max (fs_level fs) (fs_level fs').
  Proof.
    intros. induction fs; simpl. 1:reflexivity. rewrite IHfs.
    rewrite Nat.max_assoc. reflexivity.
  Qed.

  Definition node_split (x:Node) : (Node * FileSystem)%type :=
    match x with
    | file _ _ => (x, nil)
    | dir n fs => (dir n nil, fs)
    end.

  Definition fs_split (fs:FileSystem) : (FileSystem * FileSystem)%type :=
    let node_acc pair acc := (fst pair :: fst acc, snd pair ++ snd acc)
    in fold_right node_acc (nil, nil) (map node_split fs).

  Lemma split_eq : forall (x h:Node) (t:FileSystem),
      (h, t) = node_split x -> (h :: nil, t) = fs_split (x :: nil).
  Proof.
    intros. unfold fs_split. simpl. rewrite app_nil_r.
    rewrite surjective_pairing in H. inversion H. reflexivity.
  Qed.
  Arguments split_eq {_ _ _}.

  Lemma split_cons : forall (x h:Node) (fs t l r:FileSystem),
      (h, t) = node_split x -> (l, r) = fs_split fs ->
      (h :: l, t ++ r) = fs_split (x :: fs).
  Proof.
    intros. rewrite surjective_pairing in H, H0.
    inversion H. inversion H0. apply injective_projections; f_equal.
  Qed.
  Arguments split_cons {_ _ _ _ _ _}.

  Lemma split_concat : forall (fs fs' l l' r r':FileSystem),
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

  Lemma node_split_level_l : forall (x h:Node) (t:FileSystem),
      (h, t) = node_split x -> node_level h = 1.
  Proof.
    intros. destruct x; simpl in H; inversion H; reflexivity.
  Qed.
  Arguments node_split_level_l {_ _ _}.

  Lemma node_split_level_r : forall (x h:Node) (t:FileSystem),
      (h, t) = node_split x -> S (fs_level t) = node_level x.
  Proof.
    intros. destruct x; simpl in *; inversion H; reflexivity.
  Qed.
  Arguments node_split_level_r {_ _ _}.

  Lemma fs_split_level : forall (fs l r:FileSystem),
      nil <> fs -> (l, r) = fs_split fs ->
      Nat.max (fs_level l) (S (fs_level r)) = fs_level fs.
  Proof.
    intro fs. destruct fs. 1:contradiction.
    revert n. induction fs; intros; simpl.
    - remember (node_split n) as p. pattern p in Heqp.
      rewrite surjective_pairing in Heqp. rewrite <- (split_eq Heqp) in H0.
      inversion H0. simpl. do 2 rewrite Nat.max_0_r.
      rewrite (node_split_level_l Heqp). rewrite <- (node_split_level_r Heqp).
      simpl. reflexivity.
    - remember (fs_split (a :: fs)) as p. pattern p in Heqp.
      rewrite surjective_pairing in Heqp. specialize (IHfs a (fst p) (snd p)).
      assert (nil <> a :: fs). 1:discriminate. specialize (IHfs H1 Heqp).
      remember (node_split n) as q. pattern q in Heqq.
      rewrite surjective_pairing in Heqq. rewrite <- (node_split_level_r Heqq).
      pose proof (split_cons Heqq Heqp). rewrite <- H2 in H0. inversion H0.
      rewrite Nat.max_comm. rewrite level_concat.
      rewrite level_cons. rewrite Nat.succ_max_distr. rewrite <- Nat.max_assoc.
      f_equal. rewrite (node_split_level_l Heqq).
      rewrite level_cons in IHfs. rewrite <- IHfs. rewrite Nat.max_comm. f_equal.
      apply Nat.max_r_iff. destruct (fst p).
      + unfold fs_split in Heqp. simpl in Heqp. inversion Heqp.
      + assert (nil <> n0 :: f). 1:discriminate. apply (fs_level_gt_1 H3).
  Qed.
  Arguments fs_split_level {_ _ _}.

  Function fold_level (A:Type) (f:Node->A->A) (a0:A) (fs:FileSystem)
           {measure fs_level fs} : A :=
    match fs with
    | nil => a0
    | _ => match fs_split fs with
             (l, r) => fold_right f (fold_level f a0 r) l
           end
    end.
  Proof.
    intros. assert (nil <> n :: l). 1:apply nil_cons. symmetry in teq0.
    rewrite <- (fs_split_level H teq0). apply Nat.max_lt_iff. right. auto.
  Qed.
End FSLevel.
