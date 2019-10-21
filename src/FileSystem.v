Set Implicit Arguments.
Require Import FunInd.
Require Import Lists.List.
Require Import Arith.PeanoNat.
Require Import Recdef.

Definition Name := nat.
Inductive Storage := L | R.     (* Local / Remote *)

Inductive Inode : Set :=
| file : Name -> Storage -> Inode
| dir : Name -> list Inode -> Inode.
Definition FileSystem : Set := list Inode.

Lemma max_pair_lt : forall (n1 n2 m1 m2:nat),
    n1 < n2 -> m1 < m2 -> Nat.max n1 m1 < Nat.max n2 m2.
Proof.
  intros n1 n2 m1 m2 Hn Hm. apply Nat.max_lub_lt_iff. split.
  - cut (n2 <= Nat.max n2 m2). 2:apply Nat.le_max_l.
    revert Hn. apply Nat.lt_le_trans.
  - cut (m2 <= Nat.max n2 m2). 2:apply Nat.le_max_r.
    revert Hm. apply Nat.lt_le_trans.
Qed.

Lemma pair_split : forall (A B:Type) (p:(A * B)%type),
    exists (x:A) (y:B), p = (x, y).
Proof.
  intros A B p. remember (fst p) as x. remember (snd p) as y.
  exists x. exists y. rewrite -> Heqx. rewrite -> Heqy.
  assert (Hfst: fst p = fst (fst p, snd p)).
  2:assert (Hsnd: snd p = snd (fst p, snd p)).
  - reflexivity.
  - reflexivity.
  - revert Hfst Hsnd. apply injective_projections.
Qed.

Fixpoint inode_level (x:Inode) : nat :=
  match x with
  | file _ _ => S O
  | dir _ fs' => S (fold_right (fun x => Nat.max (inode_level x)) O fs')
  end.

Definition fs_level (fs:FileSystem) : nat :=
  fold_right (fun x => Nat.max (inode_level x)) O fs.

Definition inode_level_split (x:Inode) : (Inode * FileSystem)%type :=
  match x with
  | file _ _ => (x, nil)
  | dir n fs => (dir n nil, fs)
  end.

Lemma fs_inode_level : forall (x:Inode), inode_level x = fs_level (x::nil).
Proof.
  intro x. unfold fs_level. simpl. symmetry. apply Nat.max_0_r.
Qed.

Lemma inode_level_dec : forall (x x':Inode) (r:FileSystem),
    inode_level_split x = (x', r) -> fs_level r < fs_level (x::nil).
Proof.
  intros x x' r.
  destruct x; unfold inode_level_split; intro H; inversion H; auto.
Qed.

Definition fs_level_split (fs:FileSystem) :
  (FileSystem * FileSystem)%type :=
  let
    inode_split (x:Inode) : (Inode * FileSystem)%type :=
    match x with
    | file _ _ => (x, nil)
    | dir n fs' => (dir n nil, fs')
    end in
  let
    inode_acc pair acc := (fst pair :: fst acc, snd pair ++ snd acc)
  in fold_right inode_acc (nil, nil) (map inode_split fs).

Lemma fs_level_cons : forall (x:Inode) (fs:FileSystem),
    fs_level (x :: fs) = Nat.max (inode_level x) (fs_level fs).
Proof.
  intros x fs. unfold fs_level. unfold fold_right. reflexivity.
Qed.

Lemma fs_level_concat : forall (fs fs':FileSystem),
    fs_level (fs ++ fs') = Nat.max (fs_level fs) (fs_level fs').
Proof.
  intros fs fs'. induction fs.
  - simpl. reflexivity.
  - rewrite <- app_comm_cons. do 2 rewrite -> fs_level_cons.
    rewrite <- Nat.max_assoc. f_equal. apply IHfs.
Qed.

Lemma fs_level_split_cons : forall (x x':Inode) (fs l r r':FileSystem),
    inode_level_split x = (x', r) -> fs_level_split fs = (l, r') ->
    fs_level_split (x :: fs) = (x' :: l, r ++ r').
Proof.
  intros.
  assert (Hfst: fst (fs_level_split (x :: fs)) = x' :: l).
  2:assert (Hsnd: snd (fs_level_split (x :: fs)) = r ++ r').
  - unfold fs_level_split. rewrite -> map_cons. unfold fold_right. simpl.
    apply hd_error_tl_repr. simpl. split.
    + apply (f_equal fst) in H. simpl in H. rewrite <- H. reflexivity.
    + apply (f_equal fst) in H0. simpl in H0. rewrite <- H0. reflexivity.
  - unfold fs_level_split. rewrite -> map_cons. unfold fold_right. simpl.
    apply (f_equal snd) in H. simpl in H. rewrite <- H.
    apply (f_equal snd) in H0. simpl in H0. rewrite <- H0. reflexivity.
  - remember (x' :: l, r ++ r') as pair.
    apply (f_equal fst) in Heqpair as H1. simpl in H1. rewrite <- H1 in Hfst.
    apply (f_equal snd) in Heqpair as H2. simpl in H2. rewrite <- H2 in Hsnd.
    revert Hfst Hsnd. apply injective_projections.
Qed.

Lemma fs_inode_split_dec : forall (x x':Inode) (fs l r r':FileSystem),
    inode_level_split x = (x', r) -> fs_level_split fs = (l, r') ->
    Nat.max (fs_level r) (fs_level r') < Nat.max (inode_level x) (fs_level fs).
Proof.
  intros x x' fs. revert x x'. induction fs; intros x x' l r r' H H0.
  - unfold fs_level_split in H0. inversion H0. simpl.
    pose proof (inode_level_dec x) as Hi. specialize (Hi x' r H).
    rewrite <- fs_inode_level in Hi. do 2 rewrite Nat.max_0_r. auto.
  - remember (inode_level_split a) as pair1.
    assert (H1: exists x' r, pair1 = (x', r)). 1:apply pair_split.
    rewrite -> Heqpair1 in H1. destruct H1 as [a' H1]. destruct H1 as [ar H1].
    remember (fs_level_split fs) as pair2.
    assert (H2: exists l r', pair2 = (l, r')). 1:apply pair_split.
    destruct H2 as [al H2]. destruct H2 as [ar' H2].
    specialize (IHfs a a' al ar ar' H1 H2). rewrite -> Heqpair2 in H2.
    rewrite -> (fs_level_split_cons a fs H1 H2) in H0. inversion H0.
    rewrite -> fs_level_concat. rewrite -> fs_level_cons.
    assert (fs_level r < inode_level x).
    + rewrite -> fs_inode_level. revert H. apply inode_level_dec.
    + revert H3 IHfs. apply max_pair_lt.
Qed.

Lemma fs_level_split_dec : forall (fs l r:FileSystem),
    fs <> nil -> fs_level_split fs = (l, r) -> fs_level r < fs_level fs.
Proof.
  intros fs l'' r'' H. pose proof destruct_list as H0. specialize (H0 Inode fs).
  destruct H0. 2:contradiction. destruct s as [x H0]. destruct H0 as [fs' H0].
  remember (inode_level_split x) as pair1.
  assert (H1: exists x' r, pair1 = (x', r)). 1:apply pair_split.
  rewrite -> Heqpair1 in H1. destruct H1 as [x' H1]. destruct H1 as [r H1].
  remember (fs_level_split fs') as pair2.
  assert (H2: exists l r', pair2 = (l, r')). 1:apply pair_split.
  rewrite -> Heqpair2 in H2. destruct H2 as [l H2]. destruct H2 as [r' H2].
  pose proof (fs_level_split_cons x fs' H1 H2) as Hpair.
  intro H3. rewrite -> H0 in H3. rewrite -> Hpair in H3. inversion H3.
  pose proof (fs_level_cons x fs') as Hm. rewrite <- H0 in Hm. rewrite -> Hm.
  rewrite fs_level_concat. apply (fs_inode_split_dec x fs' H1 H2).
Qed.

Function fs_fold_level (A:Type) (f:Inode->A->A) (a0:A) (fs:FileSystem)
         {measure fs_level fs} : A :=
  match fs with
  | nil => a0
  | _ => match fs_level_split fs with
           (l, r) => fold_right f (fs_fold_level f a0 r) l
         end
  end.
Proof.
  intros A f a0 fs x fs' H.
  remember (inode_level_split x) as pair0.
  assert (H0: exists x' r, pair0 = (x', r)). 1:apply pair_split.
  rewrite -> Heqpair0 in H0.
  destruct H0 as [x' H0]. destruct H0 as [r H0].
  remember (fs_level_split fs') as pair1.
  assert (H1: exists l r', pair1 = (l, r')). 1:apply pair_split.
  rewrite -> Heqpair1 in H1.
  destruct H1 as [l H1]. destruct H1 as [r' H1].
  pose proof (fs_level_split_cons x fs' H0 H1) as H2.
  intros l'' r'' Hpair. rewrite -> H2 in Hpair. inversion Hpair.
  revert H2. cut (x :: fs' <> nil).
  - apply fs_level_split_dec.
  - unfold not. intro Hnil. discriminate Hnil.
Qed.

Lemma fs_fold_level_nil : forall (A:Type) (f:Inode->A->A) (a0:A),
    fs_fold_level f a0 nil = a0.
Proof.
  intros A f a0. remember nil as fs.
  functional induction (fs_fold_level f a0 fs). 1:reflexivity.
  unfold fs_level_split in e0. inversion e0. symmetry in H1.
  specialize (IHa H1). rewrite -> H1 in IHa. rewrite -> IHa. reflexivity.
Qed.

Lemma fs_fold_level_cons :
  forall (A:Type) (f:Inode->A->A) (a0:A) (fs l r:FileSystem),
    fs_level_split fs = (l, r) ->
    fs_fold_level f a0 fs = fold_right f (fs_fold_level f a0 r) l.
Proof.
  intros A f a0 fs.
  functional induction (fs_fold_level f a0 fs); intros l' r' H.
  - unfold fs_level_split in H. simpl in H. inversion H.
    rewrite -> fs_fold_level_nil. reflexivity.
  - rewrite -> e0 in H. inversion H. reflexivity.
Qed.

Lemma fs_level_split_left :
  forall (A:Type) (f:Inode->A->A) (a0:A) (fs l r:FileSystem),
    fs_level_split fs = (l, r) -> fs_level_split l = (l, nil).
Proof.
  intros A f a0 fs. induction fs; intros l r H.
  assert (fs_level_split nil = (nil, nil)).
  - unfold fs_level_split. reflexivity.
  - rewrite -> H0 in H. inversion H. assumption.
  - remember (fs_level_split fs) as pair. rewrite -> Heqpair in IHfs.
    assert (H0: exists l' r', pair = (l', r')). 1:apply pair_split.
    rewrite -> Heqpair in H0. clear pair Heqpair.
    destruct H0 as [l' H0]. destruct H0 as [r' H0]. specialize (IHfs l' r' H0).
    remember (inode_level_split a) as pair.
    assert (H1: exists x' r'', pair = (x', r'')). 1:apply pair_split.
    rewrite -> Heqpair in H1. clear pair Heqpair.
    destruct H1 as [x' H1]. destruct H1 as [r'' H1].
    rewrite -> (fs_level_split_cons a fs H1 H0) in H. inversion H.
    apply (f_equal fst) in IHfs as Hfst. simpl in Hfst.
    apply (f_equal snd) in IHfs as Hsnd. simpl in Hsnd. clear IHfs.
    apply (f_equal fst) in H1. unfold inode_level_split in H1.
    assert (fst (fs_level_split (x' :: l')) = x' :: l').
    2:assert (snd (fs_level_split (x' :: l')) = nil).
    + pattern l' at 2. rewrite <- Hfst. unfold fs_level_split.
      rewrite -> map_cons. destruct a; simpl in H1; rewrite <- H1; reflexivity.
    + rewrite <- Hsnd. unfold fs_level_split. rewrite -> map_cons.
      destruct a; simpl in H1; rewrite <- H1; reflexivity.
    + clear Hfst Hsnd. remember nil as r0. remember (x' :: l', r0).
      apply (f_equal fst) in Heqp as Hfst. simpl in Hfst. rewrite <- H2 in Hfst.
      apply (f_equal snd) in Heqp as Hsnd. simpl in Hsnd. rewrite <- H5 in Hsnd.
      rewrite -> Heqp in Hfst. symmetry in Hfst.
      rewrite -> Heqp in Hsnd. symmetry in Hsnd.
      revert Hfst Hsnd. apply injective_projections.
Qed.

Lemma fs_fold_level_left :
  forall (A:Type) (f:Inode->A->A) (a0:A) (fs l r:FileSystem),
    fs_level_split fs = (l, r) -> fs_fold_level f a0 l = fold_right f a0 l.
Proof.
  intros A f a0 fs.
  functional induction (fs_fold_level f a0 fs); intros l' r' H.
  - unfold fs_level_split in H. simpl in H. inversion H.
    rewrite fs_fold_level_nil. reflexivity.
  - rewrite -> e0 in H. inversion H. rewrite <- H1. clear H H1 H2 l' r'.
    pose proof (fs_level_split_left f a0 fs) as H0. specialize (H0 l r e0).
    pose proof (fs_fold_level_cons f a0 l) as H1. specialize (H1 l nil H0).
    rewrite fs_fold_level_nil in H1. assumption.
Qed.

Definition fs_inode_total (fs:FileSystem) : nat :=
  fs_fold_level (fun _ => S) O fs.
