Set Implicit Arguments.
Require Import FunInd.
Require Import Lists.List.
Require Import Arith.PeanoNat.
Require Import Recdef.
Require Import ArithRing.
Require Import Program.Wf.

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
  exists x. exists y. rewrite Heqx. rewrite Heqy.
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
  - rewrite <- app_comm_cons. do 2 rewrite fs_level_cons.
    rewrite <- Nat.max_assoc. f_equal. apply IHfs.
Qed.

Lemma fs_level_split_cons : forall (x x':Inode) (fs l r r':FileSystem),
    inode_level_split x = (x', r) -> fs_level_split fs = (l, r') ->
    fs_level_split (x :: fs) = (x' :: l, r ++ r').
Proof.
  intros.
  assert (Hfst: fst (fs_level_split (x :: fs)) = x' :: l).
  2:assert (Hsnd: snd (fs_level_split (x :: fs)) = r ++ r').
  - unfold fs_level_split. rewrite map_cons. unfold fold_right. simpl.
    apply hd_error_tl_repr. simpl. split.
    + apply (f_equal fst) in H. simpl in H. rewrite <- H. reflexivity.
    + apply (f_equal fst) in H0. simpl in H0. rewrite <- H0. reflexivity.
  - unfold fs_level_split. rewrite map_cons. unfold fold_right. simpl.
    apply (f_equal snd) in H. simpl in H. rewrite <- H.
    apply (f_equal snd) in H0. simpl in H0. rewrite <- H0. reflexivity.
  - remember (x' :: l, r ++ r') as pair.
    apply (f_equal fst) in Heqpair as H1. simpl in H1. rewrite <- H1 in Hfst.
    apply (f_equal snd) in Heqpair as H2. simpl in H2. rewrite <- H2 in Hsnd.
    revert Hfst Hsnd. apply injective_projections.
Qed.

Lemma fs_level_split_concat : forall (fs l r fs' l' r':FileSystem),
    fs_level_split fs = (l, r) -> fs_level_split fs' = (l', r') ->
    fs_level_split (fs ++ fs') = (l ++ l', r ++ r').
Proof.
  intros fs l r fs' l' r'. revert l r l' r'. induction fs; intros.
  - unfold fs_level_split in H. simpl in H. inversion H.
    do 3 rewrite app_nil_l. assumption.
  - rename l into al'. rename r into ar'.
    remember (inode_level_split a) as p.
    assert (H1: exists a' ar, p = (a', ar)). 1:apply pair_split.
    rewrite Heqp in H1. clear Heqp p.
    destruct H1 as [a' H1]. destruct H1 as [ar H1].
    remember (fs_level_split fs) as p. rewrite Heqp in IHfs.
    assert (H2: exists l r, p = (l, r)). 1:apply pair_split.
    rewrite Heqp in H2. clear Heqp p.
    destruct H2 as [l H2]. destruct H2 as [r H2].
    specialize (IHfs l r l' r' H2 H0).
    pose proof (fs_level_split_cons a (fs ++ fs') H1 IHfs).
    rewrite <- app_comm_cons. rewrite H3.
    rewrite (fs_level_split_cons a fs H1 H2) in H. inversion H.
    rewrite app_comm_cons. rewrite app_assoc. split.
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
    rewrite Heqpair1 in H1. destruct H1 as [a' H1]. destruct H1 as [ar H1].
    remember (fs_level_split fs) as pair2.
    assert (H2: exists l r', pair2 = (l, r')). 1:apply pair_split.
    destruct H2 as [al H2]. destruct H2 as [ar' H2].
    specialize (IHfs a a' al ar ar' H1 H2). rewrite Heqpair2 in H2.
    rewrite (fs_level_split_cons a fs H1 H2) in H0. inversion H0.
    rewrite fs_level_concat. rewrite fs_level_cons.
    assert (fs_level r < inode_level x).
    + rewrite fs_inode_level. revert H. apply inode_level_dec.
    + revert H3 IHfs. apply max_pair_lt.
Qed.

Lemma fs_level_split_dec : forall (fs l r:FileSystem),
    fs <> nil -> fs_level_split fs = (l, r) -> fs_level r < fs_level fs.
Proof.
  intros fs l'' r'' H. pose proof destruct_list as H0. specialize (H0 Inode fs).
  destruct H0. 2:contradiction. destruct s as [x H0]. destruct H0 as [fs' H0].
  remember (inode_level_split x) as pair1.
  assert (H1: exists x' r, pair1 = (x', r)). 1:apply pair_split.
  rewrite Heqpair1 in H1. destruct H1 as [x' H1]. destruct H1 as [r H1].
  remember (fs_level_split fs') as pair2.
  assert (H2: exists l r', pair2 = (l, r')). 1:apply pair_split.
  rewrite Heqpair2 in H2. destruct H2 as [l H2]. destruct H2 as [r' H2].
  pose proof (fs_level_split_cons x fs' H1 H2) as Hpair.
  intro H3. rewrite H0 in H3. rewrite Hpair in H3. inversion H3.
  pose proof (fs_level_cons x fs') as Hm. rewrite <- H0 in Hm. rewrite Hm.
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
  rewrite Heqpair0 in H0. destruct H0 as [x' H0]. destruct H0 as [r H0].
  remember (fs_level_split fs') as pair1.
  assert (H1: exists l r', pair1 = (l, r')). 1:apply pair_split.
  rewrite Heqpair1 in H1. destruct H1 as [l H1]. destruct H1 as [r' H1].
  pose proof (fs_level_split_cons x fs' H0 H1) as H2.
  intros l'' r'' Hpair. rewrite H2 in Hpair. inversion Hpair.
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
  specialize (IHa H1). rewrite H1 in IHa. rewrite IHa. reflexivity.
Qed.

Lemma fs_fold_level_cons :
  forall (A:Type) (f:Inode->A->A) (a0:A) (fs l r:FileSystem),
    fs_level_split fs = (l, r) ->
    fs_fold_level f a0 fs = fold_right f (fs_fold_level f a0 r) l.
Proof.
  intros A f a0 fs.
  functional induction (fs_fold_level f a0 fs); intros l' r' H.
  - unfold fs_level_split in H. simpl in H. inversion H.
    rewrite fs_fold_level_nil. reflexivity.
  - rewrite e0 in H. inversion H. reflexivity.
Qed.

Lemma fs_level_split_left :
  forall (A:Type) (f:Inode->A->A) (a0:A) (fs l r:FileSystem),
    fs_level_split fs = (l, r) -> fs_level_split l = (l, nil).
Proof.
  intros A f a0 fs. induction fs; intros l r H.
  assert (fs_level_split nil = (nil, nil)).
  - unfold fs_level_split. reflexivity.
  - rewrite H0 in H. inversion H. assumption.
  - remember (fs_level_split fs) as pair. rewrite Heqpair in IHfs.
    assert (H0: exists l' r', pair = (l', r')). 1:apply pair_split.
    rewrite Heqpair in H0. clear pair Heqpair.
    destruct H0 as [l' H0]. destruct H0 as [r' H0]. specialize (IHfs l' r' H0).
    remember (inode_level_split a) as pair.
    assert (H1: exists x' r'', pair = (x', r'')). 1:apply pair_split.
    rewrite Heqpair in H1. clear pair Heqpair.
    destruct H1 as [x' H1]. destruct H1 as [r'' H1].
    rewrite (fs_level_split_cons a fs H1 H0) in H. inversion H.
    apply (f_equal fst) in IHfs as Hfst. simpl in Hfst.
    apply (f_equal snd) in IHfs as Hsnd. simpl in Hsnd. clear IHfs.
    apply (f_equal fst) in H1. unfold inode_level_split in H1.
    assert (fst (fs_level_split (x' :: l')) = x' :: l').
    2:assert (snd (fs_level_split (x' :: l')) = nil).
    + pattern l' at 2. rewrite <- Hfst. unfold fs_level_split.
      rewrite map_cons. destruct a; simpl in H1; rewrite <- H1; reflexivity.
    + rewrite <- Hsnd. unfold fs_level_split. rewrite map_cons.
      destruct a; simpl in H1; rewrite <- H1; reflexivity.
    + clear Hfst Hsnd. remember nil as r0. remember (x' :: l', r0).
      apply (f_equal fst) in Heqp as Hfst. simpl in Hfst. rewrite <- H2 in Hfst.
      apply (f_equal snd) in Heqp as Hsnd. simpl in Hsnd. rewrite <- H5 in Hsnd.
      rewrite Heqp in Hfst. symmetry in Hfst.
      rewrite Heqp in Hsnd. symmetry in Hsnd.
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
  - rewrite e0 in H. inversion H. rewrite <- H1. clear H H1 H2 l' r'.
    pose proof (fs_level_split_left f a0 fs) as H0. specialize (H0 l r e0).
    pose proof (fs_fold_level_cons f a0 l) as H1. specialize (H1 l nil H0).
    rewrite fs_fold_level_nil in H1. assumption.
Qed.

Definition fs_inode_total (fs:FileSystem) : nat :=
  fs_fold_level (fun _ => S) O fs.

Lemma fs_inode_total_sum : forall (fs l r:FileSystem),
    fs_level_split fs = (l, r) ->
    fs_inode_total fs = fs_inode_total l + fs_inode_total r.
Proof.
  intros fs. unfold fs_inode_total.
  functional induction (fs_fold_level (fun _ => S) O fs); intros l' r' H.
  - unfold fs_level_split in H. simpl in H. inversion H.
    rewrite fs_fold_level_nil. reflexivity.
  - rewrite e0 in H. inversion H. rewrite <- H1. rewrite <- H2.
    clear H H1 H2 l' r'. remember (fs_fold_level (fun _ => S) O r) as c.
    pose proof (fs_fold_level_left (fun _ => S) O fs) as H.
    specialize (H l r e0). rewrite H. clear e0 Heqc IHs H fs y r.
    induction l. 1:reflexivity.
    assert (fold_right (fun _ => S) c (a :: l) = S (fold_right (fun _ => S) c l)).
    1:reflexivity. rewrite H. rewrite IHl. reflexivity.
Qed.

Lemma fs_inode_total_left : forall (fs l r:FileSystem),
    fs_level_split fs = (l, r) -> fs_inode_total l = length l.
Proof.
  intros fs. induction fs; intros.
  - unfold fs_level_split in H. simpl in H. inversion H.
    unfold fs_inode_total. rewrite fs_fold_level_nil. reflexivity.
  - remember (inode_level_split a) as p.
    assert (H0: exists a' ar, p = (a', ar)). 1:apply pair_split.
    rewrite Heqp in H0. clear p Heqp.
    destruct H0 as [a' H0]. destruct H0 as [ar H0].
    remember (fs_level_split fs) as p. rewrite Heqp in IHfs.
    assert (H1: exists l' r', p = (l', r')). 1:apply pair_split.
    rewrite Heqp in H1. clear p Heqp.
    destruct H1 as [l' H1]. destruct H1 as [r' H1].
    pose proof (fs_level_split_cons a fs H0 H1). rewrite H in H2. inversion H2.
    specialize (IHfs l' r' H1). rewrite H2 in H. unfold fs_inode_total.
    pose proof (fs_fold_level_left (fun _ => S) O) as Hl.
    rewrite (Hl (a :: fs) (a' :: l') (ar ++ r') H). specialize (Hl fs l' r' H1).
    unfold fs_inode_total in IHfs. rewrite Hl in IHfs.
    unfold fold_right. unfold fold_right in IHfs. rewrite IHfs. auto.
Qed.

Lemma fs_inode_total_cons : forall (fs l r:FileSystem),
    fs_level_split fs = (l, r) ->
    fs_inode_total fs = length l + fs_inode_total r.
Proof.
  intros. unfold fs_inode_total. rewrite (fs_fold_level_cons (fun _ => S) O fs H).
  remember (fs_fold_level (fun _ => S) O r) as k. clear H fs Heqk r. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma fs_inode_total_concat : forall (fs fs':FileSystem),
     fs_inode_total (fs ++ fs') = fs_inode_total fs + fs_inode_total fs'.
Proof.
  intro fs. unfold fs_inode_total.
  functional induction (fs_fold_level (fun _ => S) O fs); intro fs'.
  - rewrite app_nil_l. reflexivity.
  - functional induction (fs_fold_level (fun _ => S) O fs').
    + rewrite app_nil_r. rewrite (fs_fold_level_cons (fun _ => S) O fs e0). auto.
    + pose proof (fs_level_split_concat fs fs0 e0 e1).
      pose proof (fs_inode_total_sum (fs ++ fs0) H).
      unfold fs_inode_total in H0. rewrite H0. clear H0.
      specialize (IHs r0). rewrite IHs. clear IHs IHs0.
      remember (fs_inode_total fs) as p. assert (Htmp := Heqp).
      unfold fs_inode_total in Htmp.
      rewrite (fs_fold_level_cons (fun _ => S) O fs e0) in Htmp.
      rewrite <- Htmp. rewrite Heqp. clear Heqp Htmp p.
      remember (fs_inode_total fs0) as p. assert (Htmp := Heqp).
      unfold fs_inode_total in Htmp.
      rewrite (fs_fold_level_cons (fun _ => S) O fs0 e1) in Htmp.
      rewrite <- Htmp. rewrite Heqp. clear Heqp Htmp p.
      rewrite (fs_inode_total_cons fs e0). rewrite (fs_inode_total_cons fs0 e1).
      pose proof (fs_inode_total_left (fs ++ fs0) H).
      unfold fs_inode_total in H0. rewrite H0.
      unfold fs_inode_total. rewrite app_length. ring.
Qed.

Lemma fs_inode_total_ge_0 : forall (fs:FileSystem), fs_inode_total fs >= 0.
Proof.
  intro fs. functional induction (fs_fold_level (fun _ => S) O fs).
  - unfold fs_inode_total. rewrite fs_fold_level_nil. auto.
  - rewrite (fs_inode_total_cons fs e0). clear e0.
    cut (fs_inode_total r <= length l + fs_inode_total r).
    + revert IHs. unfold ge. apply Nat.le_trans.
    + clear IHs. induction l. 1:auto. simpl. revert IHl. apply Nat.le_le_succ_r.
Qed.

Lemma fs_inode_total_cons_gt : forall (x:Inode) (fs:FileSystem),
    fs_inode_total fs < fs_inode_total (x :: fs).
Proof.
  intros. assert (x :: fs = (x :: nil) ++ fs). 1:auto. rewrite H.
  clear H. rewrite fs_inode_total_concat.
  pattern (fs_inode_total fs) at 1. rewrite <- Nat.add_0_l.
  apply Nat.add_lt_mono_r. destruct x.
  - remember (fs_level_split (file n s :: nil)) as p. assert (H := Heqp).
    unfold fs_level_split in H. simpl in H. rewrite Heqp in H. clear Heqp p.
    rewrite (fs_inode_total_cons (file n s :: nil) H).
    unfold fs_inode_total.  rewrite fs_fold_level_nil. auto.
  - remember (fs_level_split (dir n l :: nil)) as p. assert (H := Heqp).
    unfold fs_level_split in H. simpl in H. rewrite Heqp in H. clear Heqp p.
    rewrite app_nil_r in H. rewrite (fs_inode_total_cons (dir n l :: nil) H).
    simpl. apply Nat.lt_succ_r. apply fs_inode_total_ge_0.
Qed.

Function fs_map_inode (f:Inode->Inode) (fs:FileSystem)
         {measure fs_inode_total fs} : FileSystem :=
  match fs with
  | nil => nil
  | x::fs' =>
    let x' := match x with
              | file _ _ => f x
              | dir n fs'' => dir n (fs_map_inode f fs'')
              end
    in x' :: fs_map_inode f fs'
  end.
Proof.
  - intros. clear f teq fs. rewrite <- teq0. apply fs_inode_total_cons_gt.
  - intros. clear f teq fs. rewrite <- teq0. apply fs_inode_total_cons_gt.
  - intros. clear f teq fs.
    assert (dir n fs'' :: fs' = (dir n fs'' :: nil) ++ fs'). 1:auto.
    rewrite H. clear H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs'') at 1. rewrite <- Nat.add_0_r.
    cut (0 <= fs_inode_total fs'). apply Nat.add_lt_le_mono.
    + remember (fs_level_split (dir n fs'' :: nil)) as p.
      assert (H := Heqp). unfold fs_level_split in H. simpl in H.
      rewrite app_nil_r in H. rewrite Heqp in H. clear Heqp p.
      rewrite (fs_inode_total_cons (dir n fs'' :: nil) H). simpl. auto.
    + apply fs_inode_total_ge_0.
Qed.

Definition fs_set_storage (s:Storage) (fs:FileSystem) :=
  let f x := match x with
             | file n _ => file n s
             | dir _ _ => x
             end
  in fs_map_inode f fs.

Definition get_name (x:Inode) : Name :=
  match x with
  | file n _ => n
  | dir n _ => n
  end.

Fixpoint fs_sort_insert (x:Inode) (fs:FileSystem) : FileSystem :=
  match fs with
  | nil => x :: nil
  | x'::fs' => if get_name x <=? get_name x'
               then x :: fs
               else x' :: fs_sort_insert x fs'
  end.

Lemma fs_inode_total_insert : forall (x:Inode) (fs:FileSystem),
    fs_inode_total (fs_sort_insert x fs) = fs_inode_total (x :: fs).
Proof.
  intros x fs. induction fs; unfold fs_sort_insert. 1:reflexivity.
  fold fs_sort_insert. destruct (get_name x <=? get_name a). 1:reflexivity.
  assert (a :: fs_sort_insert x fs = (a :: nil) ++ fs_sort_insert x fs).
  1:reflexivity. rewrite H. rewrite fs_inode_total_concat. rewrite IHfs.
  assert (x :: a :: fs = (x :: a :: nil) ++ fs).
  1:reflexivity. rewrite H0. rewrite fs_inode_total_concat.
  assert (x :: fs = (x :: nil) ++ fs).
  1:reflexivity. rewrite H1. rewrite fs_inode_total_concat.
  assert (x :: a :: nil = (x :: nil) ++ (a :: nil)).
  1:reflexivity. rewrite H2. rewrite fs_inode_total_concat.
  ring.
Qed.

Fixpoint fs_sort_level (fs:FileSystem) : FileSystem :=
  match fs with
  | nil => nil
  | x::fs' => fs_sort_insert x (fs_sort_level fs')
  end.

Lemma fs_inode_total_sorted : forall (fs:FileSystem),
    fs_inode_total (fs_sort_level fs) = fs_inode_total fs.
Proof.
  intro fs. induction fs; unfold fs_sort_level. 1:reflexivity.
  fold fs_sort_level. rewrite fs_inode_total_insert.
  assert (a :: fs_sort_level fs = (a :: nil) ++ fs_sort_level fs).
  1:reflexivity. rewrite H. rewrite fs_inode_total_concat.
  assert (a :: fs = (a :: nil) ++ fs). 1:reflexivity.
  rewrite H0. rewrite fs_inode_total_concat. rewrite IHfs. reflexivity.
Qed.

Function fs_sort_other (fs:FileSystem)
         {measure fs_inode_total fs} : FileSystem :=
  match fs with
  | nil => nil
  | x::fs' =>
    let x' := match x with
              | file _ _ => x
              | dir n fs' => dir n (fs_sort_other (fs_sort_level fs'))
              end
    in x' :: fs_sort_other fs'
  end.
Proof.
  - intros. assert (file n s :: fs' = (file n s :: nil) ++ fs').
    1:reflexivity. rewrite H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs') at 1. rewrite <- Nat.add_0_l.
    apply Nat.add_lt_mono_r. assert (fs_inode_total nil = 0).
    + unfold fs_inode_total. apply fs_fold_level_nil.
    + rewrite <- H0. apply fs_inode_total_cons_gt.
  - intros. assert (dir n fs'0 :: fs' = (dir n fs'0 :: nil) ++ fs').
    1:reflexivity. rewrite H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs') at 1. rewrite <- Nat.add_0_l.
    apply Nat.add_lt_mono_r. assert (fs_inode_total nil = 0).
    + unfold fs_inode_total. apply fs_fold_level_nil.
    + rewrite <- H0. apply fs_inode_total_cons_gt.
  - intros. rewrite fs_inode_total_sorted.
    assert (dir n fs'0 :: fs' = (dir n fs'0 :: nil) ++ fs').
    1:reflexivity. rewrite H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs'0) at 1. rewrite <- Nat.add_0_r.
    apply Nat.add_lt_le_mono.
    + remember (fs_level_split (dir n fs'0 :: nil)) as p. assert (H0 := Heqp).
      unfold fs_level_split in H0. simpl in H0.
      rewrite Heqp in H0. clear Heqp p. rewrite app_nil_r in H0.
      rewrite (fs_inode_total_cons (dir n fs'0 :: nil) H0). auto.
    + apply fs_inode_total_ge_0.
Qed.

Definition fs_sort (fs:FileSystem) : FileSystem :=
  fs_sort_other (fs_sort_level fs).

Definition resolve_names (x1 x2:Inode) : (Name * Name)%type :=
  match x1, x2 with
  | dir n1 _,  dir n2 _  => (n1, n2)
  | dir n1 _,  file n2 _ => (n1, n2)
  | file n1 _, dir n2 _  => (n1, n2)
  | file n1 _, file n2 _ => (n1, n2)
  end.

Program Fixpoint fs_merge (fs1 fs2:FileSystem)
        {measure (fs_inode_total fs1 + fs_inode_total fs2)} : FileSystem :=
  match fs1, fs2 with
  | _, nil => fs1
  | nil, _ => fs2
  | x1::fs1', x2::fs2' =>
    match Nat.compare (get_name x1) (get_name x2) with
    | Lt => x1 :: fs_merge fs1' fs2
    | Gt => x2 :: fs_merge fs1 fs2'
    | Eq =>
      let
        (n1, n2) := resolve_names x1 x2 in
      let
        xs := match x1, x2 with
              | dir _ fs1'', dir _ fs2'' => dir n1 (fs_merge fs1'' fs2'') :: nil
              | dir _ fs1'', file _ s2   => dir n1 fs1'' :: file n2 s2 :: nil
              | file _ s1,   dir _ fs2'' => file n1 s1 :: dir n2 fs2'' :: nil
              | file _ s1,   file _ s2   => file n1 s1 :: file n2 s2 :: nil
              end
      in xs ++ fs_merge fs1' fs2'
    end
  end.
Next Obligation.
  apply Nat.add_lt_mono_r. apply fs_inode_total_cons_gt.
Qed.
Next Obligation.
  apply Nat.add_lt_mono_l. apply fs_inode_total_cons_gt.
Qed.
Next Obligation.
  rename wildcard'0 into n1'. rename wildcard' into n2'.
  cut (fs_inode_total fs2'' < fs_inode_total (dir n1' fs2'' :: fs2')).
  cut (fs_inode_total fs1'' < fs_inode_total (dir n2' fs1'' :: fs1')).
  - apply Nat.add_lt_mono.
  - assert (dir n2' fs1'' :: fs1' = (dir n2' fs1'' :: nil) ++ fs1').
    1:auto. rewrite H. clear H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs1'') at 1. rewrite <- Nat.add_0_r.
    apply Nat.add_lt_le_mono.
    + remember (fs_level_split (dir n2' fs1'' :: nil)) as p. assert (H := Heqp).
      unfold fs_level_split in H. simpl in H.
      rewrite Heqp in H. clear Heqp p. rewrite app_nil_r in H.
      rewrite (fs_inode_total_cons (dir n2' fs1'' :: nil) H). simpl. auto.
    + apply fs_inode_total_ge_0.
  - assert (dir n1' fs2'' :: fs2' = (dir n1' fs2'' :: nil) ++ fs2').
    1:auto. rewrite H. clear H. rewrite fs_inode_total_concat.
    pattern (fs_inode_total fs2'') at 1. rewrite <- Nat.add_0_r.
    apply Nat.add_lt_le_mono.
    + remember (fs_level_split (dir n1' fs2'' :: nil)) as p. assert (H := Heqp).
      unfold fs_level_split in H. simpl in H.
      rewrite Heqp in H. clear Heqp p. rewrite app_nil_r in H.
      rewrite (fs_inode_total_cons (dir n1' fs2'' :: nil) H). simpl. auto.
    + apply fs_inode_total_ge_0.
Qed.
Next Obligation.
  apply Nat.add_lt_mono; apply fs_inode_total_cons_gt.
Qed.
