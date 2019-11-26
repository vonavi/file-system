Set Implicit Arguments.
Require Import FunInd.
Require Import Lists.List.
Require Import Arith.PeanoNat.
Require Import Recdef.
Require Import ArithRing.
Require Import Program.Wf.
Require Import OrderedType OrderedTypeEx.

Add LoadPath ".".
Require Import Node.
Require Import FileSystem.

Module Inode := Node_as_OT Nat_as_OT Nat_as_OT.
Module IM := OrderedTypeFacts Inode.
Definition FileSystem := @FileSystem nat nat.

Lemma size_cons_gt : forall (x:Inode.t) (fs:FileSystem),
    size fs < size (x :: fs).
Proof.
  intros. assert (x :: fs = (x :: nil) ++ fs). 1:auto. rewrite H.
  clear H. rewrite size_concat. pattern (size fs) at 1. rewrite <- Nat.add_0_l.
  apply Nat.add_lt_mono_r. remember (x :: nil) as fs'. destruct x.
  - assert ((fs', nil) = fs_split fs').
    + rewrite Heqfs'. unfold fs_split. reflexivity.
    + rewrite (split_size fs' H). rewrite Heqfs'. unfold size.
      rewrite fold_level_nil. auto.
  - assert ((dir n nil :: nil, l) = fs_split fs').
    + rewrite Heqfs'. unfold fs_split. simpl. rewrite app_nil_r. reflexivity.
    + rewrite (split_size fs' H). simpl. apply Nat.lt_succ_r. apply size_ge_0.
Qed.

Function fs_map_inode (f:Inode.t->Inode.t) (fs:FileSystem)
         {measure size fs} : FileSystem :=
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
  - intros. clear f teq fs. rewrite <- teq0. apply size_cons_gt.
  - intros. clear f teq fs. rewrite <- teq0. apply size_cons_gt.
  - intros. clear f. rewrite <- teq. assert (fs = (dir n fs'' :: nil) ++ fs').
    1:auto. rewrite H. clear H. rewrite size_concat.
    pattern (size fs'') at 1. rewrite <- Nat.add_0_r. apply Nat.add_lt_le_mono.
    + assert ((dir n nil :: nil, fs'') = fs_split (dir n fs'' :: nil)).
      * unfold fs_split. simpl. rewrite app_nil_r. reflexivity.
      * rewrite (split_size (dir n fs'' :: nil) H). auto.
    + apply size_ge_0.
Qed.

Definition fs_set_storage (s:nat) (fs:FileSystem) :=
  let f x := match x with
             | file n _ => file n s
             | dir _ _ => x
             end
  in fs_map_inode f fs.

Fixpoint fs_sort_insert (x:Inode.t) (fs:FileSystem) : FileSystem :=
  match fs with
  | nil => x :: nil
  | x'::fs' => match Inode.compare x x' with
               | LT _ => x :: fs
               | EQ _ => x :: fs
               | GT _ => x' :: fs_sort_insert x fs'
               end
  end.

Lemma fs_sort_insert_comm : forall (x y:Inode.t) (fs:FileSystem),
    Inode.lt x y -> fs_sort_insert x (fs_sort_insert y fs) =
                    fs_sort_insert y (fs_sort_insert x fs).
Proof.
  intros x y fs. revert x y. induction fs; intros; simpl.
  - assert (H0 := H). apply IM.elim_compare_lt in H. destruct H. rewrite H.
    apply IM.elim_compare_gt in H0. destruct H0. rewrite H0. reflexivity.
  - destruct (Inode.compare y a).
    + pose proof (Inode.lt_trans x y a H l). apply IM.elim_compare_lt in H0.
      destruct H0. rewrite H0. simpl. assert (H2 := H).
      apply IM.elim_compare_lt in H. destruct H. rewrite H.
      apply IM.elim_compare_gt in H2. destruct H2. rewrite H1.
      apply IM.elim_compare_lt in l. destruct l. rewrite H2. reflexivity.
    + pose proof (IM.lt_eq H e). apply IM.elim_compare_lt in H0. destruct H0.
      rewrite H0. simpl. assert (H2 := H). apply IM.elim_compare_lt in H.
      destruct H. rewrite H. apply IM.elim_compare_gt in H2. destruct H2.
      rewrite H1. apply IM.elim_compare_eq in e. destruct e. rewrite H2.
      reflexivity.
    + destruct (Inode.compare x a); simpl; apply IM.elim_compare_gt in l;
        destruct l; rewrite H0; apply IM.elim_compare_gt in H; destruct H;
          try rewrite H.
      * apply IM.elim_compare_lt in l0. destruct l0. rewrite H1. reflexivity.
      * apply IM.elim_compare_eq in e. destruct e. rewrite H1. reflexivity.
      * apply IM.elim_compare_gt in l0. destruct l0. rewrite H1.
        specialize (IHfs x y x1). rewrite IHfs. reflexivity.
Qed.

Lemma size_insert : forall (x:Inode.t) (fs:FileSystem),
    size (fs_sort_insert x fs) = size (x :: fs).
Proof.
  intros x fs. induction fs; unfold fs_sort_insert. 1:reflexivity.
  fold fs_sort_insert. destruct (Inode.compare x a); try reflexivity.
  assert (a :: fs_sort_insert x fs = (a :: nil) ++ fs_sort_insert x fs).
  1:reflexivity. rewrite H. rewrite size_concat. rewrite IHfs.
  assert (x :: a :: fs = (x :: a :: nil) ++ fs).
  1:reflexivity. rewrite H0. rewrite size_concat.
  assert (x :: fs = (x :: nil) ++ fs).
  1:reflexivity. rewrite H1. rewrite size_concat.
  assert (x :: a :: nil = (x :: nil) ++ (a :: nil)).
  1:reflexivity. rewrite H2. rewrite size_concat. ring.
Qed.

Fixpoint fs_sort_level (fs:FileSystem) : FileSystem :=
  match fs with
  | nil => nil
  | x::fs' => fs_sort_insert x (fs_sort_level fs')
  end.

Lemma fs_sort_level_insert : forall (x:Inode.t) (fs:FileSystem),
    fs_sort_level (fs_sort_insert x fs) = fs_sort_level (x :: fs).
Proof.
  intros x fs. revert x. induction fs. 1:reflexivity.
  simpl. intro x. destruct (Inode.compare x a); try reflexivity.
  simpl in *. specialize (IHfs x). rewrite IHfs.
  apply (fs_sort_insert_comm a x (fs_sort_level fs) l).
Qed.

Lemma fs_sort_level_dec : forall (x:Inode.t) (fs fs':FileSystem),
    x :: fs = fs_sort_level fs' ->
    exists (fs'':FileSystem), fs = fs_sort_level fs''.
Proof.
  intros x fs fs'. revert x fs. induction fs'; intros. 1:discriminate.
  simpl in H. remember (fs_sort_level fs') as xs. destruct xs.
  - inversion H. eauto.
  - simpl in H. destruct (Inode.compare a n); inversion H; try eauto.
    assert (n :: xs = n :: xs). 1:reflexivity. specialize (IHfs' n xs H0).
    destruct IHfs' as [fs'' IHfs']. rewrite IHfs'.
    assert (fs_sort_insert a (fs_sort_level fs'') = fs_sort_level (a :: fs'')).
    + induction fs''; reflexivity.
    + eauto.
Qed.

Lemma fs_sort_level_double : forall (fs:FileSystem),
    fs_sort_level (fs_sort_level fs) = fs_sort_level fs.
Proof.
  intro fs. induction fs; simpl. 1:reflexivity.
  remember (fs_sort_level fs) as fs'. clear Heqfs' fs.
  pattern fs' at 2. rewrite <- IHfs. clear IHfs.
  revert a. induction fs'; simpl. 1:reflexivity.
  intro a0. destruct (Inode.compare a0 a); try auto. simpl.
  specialize (IHfs' a). rewrite <- IHfs'. clear IHfs'.
  revert a a0 l. induction fs'; intros; simpl.
  - assert (l0 := l). apply IM.elim_compare_lt in l. destruct l. rewrite H.
    apply IM.elim_compare_gt in l0. destruct l0. rewrite H0. reflexivity.
  - destruct (Inode.compare a1 a).
    + pose proof (Inode.lt_trans a0 a1 a l l0). apply IM.elim_compare_lt in H.
      destruct H. rewrite H. simpl.
      apply (fs_sort_insert_comm a0 a1 (fs_sort_insert a (fs_sort_level fs')) l).
    + pose proof (IM.lt_eq l e). apply IM.elim_compare_lt in H. destruct H.
      rewrite H. simpl.
      apply (fs_sort_insert_comm a0 a1 (fs_sort_insert a (fs_sort_level fs')) l).
    + destruct (Inode.compare a0 a); simpl.
      * specialize (IHfs' a a1 l0). rewrite IHfs'.
        rewrite fs_sort_level_insert. simpl.
        apply (fs_sort_insert_comm a0 a1 (fs_sort_insert a (fs_sort_level fs')) l).
      * specialize (IHfs' a a1 l0). rewrite IHfs'.
        rewrite fs_sort_level_insert. simpl.
        apply (fs_sort_insert_comm a0 a1 (fs_sort_insert a (fs_sort_level fs')) l).
      * assert (IHfs'0 := IHfs'). specialize (IHfs' a a1 l0). rewrite IHfs'.
        specialize (IHfs'0 a a0 l1). rewrite IHfs'0.
        apply (fs_sort_insert_comm a0 a1 (fs_sort_level (fs_sort_insert a fs')) l).
Qed.

Lemma size_sorted : forall (fs:FileSystem),
    size (fs_sort_level fs) = size fs.
Proof.
  intro fs. induction fs; unfold fs_sort_level. 1:reflexivity.
  fold fs_sort_level. rewrite size_insert.
  assert (a :: fs = (a :: nil) ++ fs). 1:reflexivity. rewrite H.
  rewrite size_concat. rewrite <- IHfs.
  rewrite <- size_concat. simpl. reflexivity.
Qed.

Function fs_sort_other (fs:FileSystem)
         {measure size fs} : FileSystem :=
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
  - intros. rewrite <- teq. assert (fs = (file n n0 :: nil) ++ fs').
    1:rewrite teq; reflexivity. rewrite H. rewrite size_concat.
    pattern (size fs') at 1. rewrite <- Nat.add_0_l. apply Nat.add_lt_mono_r.
    pose proof (size_cons_gt (file n n0) nil). unfold size in *.
    rewrite fold_level_nil in H0. assumption.
  - intros. rewrite <- teq. assert (fs = (dir n fs'0 :: nil) ++ fs').
    1:rewrite teq; reflexivity. rewrite H. rewrite size_concat.
    pattern (size fs') at 1. rewrite <- Nat.add_0_l. apply Nat.add_lt_mono_r.
    pose proof (size_cons_gt (dir n fs'0) nil). unfold size in *.
    rewrite fold_level_nil in H0. assumption.
  - intros. rewrite size_sorted. rewrite <- teq.
    assert (fs = (dir n fs'0 :: nil) ++ fs'). 1:rewrite teq; reflexivity.
    rewrite H. rewrite size_concat. pattern (size fs'0) at 1.
    rewrite <- Nat.add_0_r. apply Nat.add_lt_le_mono.
    + assert ((dir n nil :: nil, fs'0) = fs_split (dir n fs'0 :: nil)).
      * unfold fs_split. simpl. rewrite app_nil_r. reflexivity.
      * rewrite (split_size (dir n fs'0 :: nil) H0). auto.
    + apply size_ge_0.
Qed.

Definition fs_sort (fs:FileSystem) : FileSystem :=
  fs_sort_other (fs_sort_level fs).

Fixpoint fs_group_level (fs:FileSystem) : list FileSystem :=
  match fs with
  | nil => nil
  | x::fs' =>
    let
      gs := fs_group_level fs'
    in match gs with
       | nil => (x :: nil) :: nil
       | xs::gs' => match hd_error xs with
                    | None => (x :: nil) :: gs
                    | Some x' => if IM.eqb x x'
                                 then (x :: xs) :: gs'
                                 else (x :: nil) :: gs
                    end
       end
  end.

Definition resolve_names (x1 x2:Inode.t) : (nat * nat)%type :=
  match x1, x2 with
  | dir n1 _,  dir n2 _  => (n1, n2)
  | dir n1 _,  file n2 _ => (n1, n2)
  | file n1 _, dir n2 _  => (n1, n2)
  | file n1 _, file n2 _ => (n1, n2)
  end.

Lemma size_insert_gt_0 : forall (x:Inode.t) (fs:FileSystem),
    0 < size (fs_sort_insert x fs).
Proof.
  intros. unfold fs_sort_insert. destruct fs.
  - pose proof (size_cons_gt x nil). unfold size in *.
    rewrite fold_level_nil in H. assumption.
  - destruct (Inode.compare x n).
    + assert (x :: n :: fs = (x :: nil) ++ (n :: fs)). 1:reflexivity.
      rewrite H. rewrite size_concat.
      pattern 0. rewrite <- Nat.add_0_l. apply Nat.add_lt_le_mono.
      * pose proof (size_cons_gt x nil). unfold size in *.
        rewrite fold_level_nil in H0. assumption.
      * apply size_ge_0.
    + assert (x :: n :: fs = (x :: nil) ++ (n :: fs)). 1:reflexivity.
      rewrite H. rewrite size_concat.
      pattern 0. rewrite <- Nat.add_0_l. apply Nat.add_lt_le_mono.
      * pose proof (size_cons_gt x nil). unfold size in *.
        rewrite fold_level_nil in H0. assumption.
      * apply size_ge_0.
    + fold fs_sort_insert. remember (fs_sort_insert x fs) as fs'.
      assert (n :: fs' = (n :: nil) ++ fs'). 1:reflexivity.
      rewrite H. rewrite size_concat.
      pattern 0. rewrite <- Nat.add_0_l. apply Nat.add_lt_le_mono.
      * pose proof (size_cons_gt n nil). unfold size in *.
        rewrite fold_level_nil in H0. assumption.
      * apply size_ge_0.
Qed.

Lemma size_grouped : forall (fs:FileSystem),
    fold_right Nat.add O (map (fun x => size x) (fs_group_level fs)) = size fs.
Proof.
  intro fs. induction fs.
  - simpl. unfold size. symmetry. apply fold_level_nil.
  - unfold fs_group_level. fold fs_group_level. destruct (fs_group_level fs).
    + rewrite map_cons. simpl. simpl in IHfs.
      assert (a :: fs = (a :: nil) ++ fs). 1:reflexivity.
      rewrite H. rewrite size_concat. rewrite <- IHfs. reflexivity.
    + rewrite map_cons in IHfs. simpl in IHfs. destruct (hd_error f).
      * destruct (IM.eqb a n); assert (a :: fs = (a :: nil) ++ fs);
          try reflexivity; rewrite H; rewrite size_concat.
        -- rewrite map_cons. assert (a :: f = (a :: nil) ++ f). 1:reflexivity.
           rewrite H0. rewrite size_concat. rewrite <- IHfs.
           unfold fold_right. ring_simplify. reflexivity.
        -- do 2 rewrite map_cons. rewrite <- IHfs. unfold fold_right.
           ring_simplify. reflexivity.
      * do 2 rewrite map_cons. assert (a :: fs = (a :: nil) ++ fs).
        1:reflexivity. rewrite H. rewrite size_concat.
        rewrite <- IHfs. unfold fold_right. ring_simplify. reflexivity.
Qed.

Lemma size_compacted :
  forall (n n1 n2:nat) (fs fs1 fs2:FileSystem),
    size (dir n (fs1 ++ fs2) :: fs) <
    size (dir n1 fs1 :: dir n2 fs2 :: fs).
Proof.
  intros. assert (dir n (fs1 ++ fs2) :: fs = (dir n (fs1 ++ fs2) :: nil) ++ fs).
  1:reflexivity. rewrite H. rewrite size_concat.
  assert (dir n1 fs1 :: dir n2 fs2 :: fs =
          (dir n1 fs1 :: dir n2 fs2 :: nil) ++ fs).
  1:reflexivity. rewrite H0. rewrite size_concat.
  apply Nat.add_lt_mono_r.
  remember (fs_split (dir n (fs1 ++ fs2) :: nil)) as p.
  assert (H1 := Heqp). unfold fs_split in H1. simpl in H1.
  rewrite app_nil_r in H1. rewrite Heqp in H1. symmetry in H1. clear Heqp p.
  rewrite (split_size (dir n (fs1 ++ fs2) :: nil) H1).
  assert (dir n1 fs1 :: dir n2 fs2 :: nil =
          (dir n1 fs1 :: nil) ++ (dir n2 fs2 :: nil)).
  1:reflexivity. rewrite H2. do 2 rewrite size_concat.
  remember (fs_split (dir n1 fs1 :: nil)) as p.
  assert (H3 := Heqp). unfold fs_split in H3. simpl in H3.
  rewrite app_nil_r in H3. rewrite Heqp in H3. symmetry in H3. clear Heqp p.
  rewrite (split_size (dir n1 fs1 :: nil) H3).
  remember (fs_split (dir n2 fs2 :: nil)) as q.
  assert (H4 := Heqq). unfold fs_split in H4. simpl in H4.
  rewrite app_nil_r in H4. rewrite Heqq in H4. symmetry in H4. clear Heqq q.
  rewrite (split_size (dir n2 fs2 :: nil) H4). simpl.
  rewrite <- Nat.succ_lt_mono. apply Nat.add_lt_mono_l. auto.
Qed.

Lemma size_perm : forall (x1 x2:Inode.t) (fs:FileSystem),
    size (x1 :: x2 :: fs) = size (x2 :: x1 :: fs).
Proof.
  intros. assert (x1 :: x2 :: fs = (x1 :: nil) ++ (x2 :: fs)).
  1:reflexivity. assert (x2 :: x1 :: fs = (x2 :: nil) ++ (x1 :: fs)).
  1:reflexivity. rewrite H. rewrite H0. do 2 rewrite size_concat.
  assert (x1 :: fs = (x1 :: nil) ++ fs). 1:reflexivity.
  assert (x2 :: fs = (x2 :: nil) ++ fs). 1:reflexivity.
  rewrite H1. rewrite H2. do 2 rewrite size_concat. ring.
Qed.

Function fs_compact_group (fs:FileSystem)
         {measure size fs} : option Inode.t :=
  match fs with
  | nil => None
  | x1::nil => Some x1
  | x1::x2::fs' =>
    if IM.eqb x1 x2
    then let
        (n1, n2) := resolve_names x1 x2
      in match x1, x2 with
         | dir _ fs1, dir _ fs2 => fs_compact_group (dir n1 (fs1 ++ fs2) :: fs')
         | file _ _, file _ _ => fs_compact_group (x1 :: fs')
         | _, _ => None
         end
    else None
  end.
Proof.
  - intros. rewrite size_perm. apply size_cons_gt.
  - intros. apply (f_equal (fun x => size x)) in teq. symmetry in teq.
    apply (size_compacted n1 n n0 fs' fs1 fs2).
Qed.

Lemma fs_compacted_group_eq : forall (x y:Inode.t) (fs:FileSystem),
    fs_compact_group (x :: fs) = Some y -> Inode.eq x y.
Proof.
  intros x y fs. remember (x :: fs) as fs'. revert x fs Heqfs'.
  functional induction fs_compact_group fs'; intros; inversion H.
  - inversion Heqfs'. rewrite <- H1. rewrite <- H2. reflexivity.
  - specialize (IHo (dir n1 (fs1 ++ fs2)) fs').
    assert (dir n1 (fs1 ++ fs2) :: fs' = dir n1 (fs1 ++ fs2) :: fs').
    1:reflexivity. specialize (IHo H0 H). inversion Heqfs'. simpl in e1.
    inversion e1. simpl in IHo. destruct y; inversion IHo. simpl. reflexivity.
  - specialize (IHo (file _x _x0) fs').
    assert (file _x _x0 :: fs' = file _x _x0 :: fs'). 1:reflexivity.
    specialize (IHo H0 H). inversion Heqfs'. assumption.
Qed.

Lemma fs_compacted_group_dir_cons : forall (n:nat) (fs fs1 fs2:FileSystem),
    fs_compact_group (dir n fs1 :: dir n fs2 :: fs) =
    fs_compact_group (dir n (fs1 ++ fs2) :: fs).
Proof.
  intros. remember (dir n fs1 :: dir n fs2 :: fs) as fs'.
  functional induction fs_compact_group fs'; inversion Heqfs'.
  - repeat f_equal. simpl in e1. inversion e1. rewrite <- H5. assumption.
  - rewrite H0 in y. rewrite H1 in y. inversion y.
  - rewrite H0 in e0. rewrite H1 in e0. simpl in e0.
    assert (n = n). 1:reflexivity. rewrite IM.eqb_alt in e0.
    destruct (Inode.compare (dir n fs1) (dir n fs2)); try discriminate;
      simpl in l; contradiction (Nat.lt_irrefl n).
Qed.

Lemma fs_compacted_group_file_cons : forall (n:nat) (s:nat) (fs:FileSystem),
    fs_compact_group (file n s :: file n s :: fs) =
    fs_compact_group (file n s :: fs).
Proof.
  intros. remember (file n s :: file n s :: fs) as fs'.
  functional induction fs_compact_group fs'; inversion Heqfs'.
  - reflexivity.
  - rewrite H0 in y. rewrite H1 in y. inversion y.
  - rewrite H0 in e0. rewrite H1 in e0. simpl in e0. rewrite IM.eqb_alt in e0.
    destruct (Inode.compare (file n s) (file n s)); try discriminate;
      simpl in l; destruct l; try contradiction (Nat.lt_irrefl n);
        destruct H; contradiction (Nat.lt_irrefl s).
Qed.

Lemma fs_compacted_group_cons : forall (x y:Inode.t) (fs:FileSystem),
    fs_compact_group fs = Some y -> Inode.eq x y ->
    exists (z:Inode.t), fs_compact_group (x :: fs) = Some z.
Proof.
  intros. remember (x :: fs) as fs'.
  destruct x; destruct y; intros. simpl in H0; inversion H0.
  - rewrite <- H1, <- H2 in H. clear H0 H1 H2 n1 n2.
    functional induction fs_compact_group fs; inversion H.
    + rewrite <- H1 in Heqfs'. rewrite Heqfs'. rewrite <- Heqfs'.
      assert (fs_compact_group fs' = fs_compact_group (x1 :: nil)).
      1:rewrite Heqfs', H1; apply fs_compacted_group_file_cons. rewrite H0.
      clear H0. remember (x1 :: nil) as fs.
      functional induction fs_compact_group fs; inversion Heqfs. eauto.
    + pose proof (fs_compacted_group_eq (dir n1 (fs1 ++ fs2)) fs'0 H).
      simpl in H0. contradiction.
    + rewrite IM.eqb_alt in e0.
      destruct (Inode.compare (file _x _x0) (file _x1 _x2)) in e0;
        try discriminate. simpl in e. inversion e. rewrite <- H0, <- H2 in Heqfs'.
      pose proof (fs_compacted_group_eq (file _x _x0) fs'0 H). simpl in H3.
      inversion H3. rewrite H4, H5 in Heqfs', H. rewrite Heqfs'.
      do 2 rewrite fs_compacted_group_file_cons. eauto.
  - simpl in H0. contradiction.
  - simpl in H0. contradiction.
  - simpl in H0. rewrite <- H0 in H. revert fs' Heqfs'.
    functional induction fs_compact_group fs; inversion H; intros.
    + remember (dir n (l ++ l0) :: nil) as fs.
      assert (fs_compact_group fs' = fs_compact_group fs).
      1:rewrite Heqfs', Heqfs. apply fs_compacted_group_dir_cons. rewrite H1.
      clear H1. functional induction fs_compact_group fs; inversion Heqfs. eauto.
    + specialize (IHo H). rewrite IM.eqb_alt in e0.
      destruct (Inode.compare (dir _x fs1) (dir _x0 fs2)); try discriminate e0.
      simpl in e. rewrite <- e in e1, Heqfs'. simpl in e1. inversion e1.
      rewrite H3 in Heqfs'. remember (dir n l :: dir n1 (fs1 ++ fs2) :: fs') as fs.
      specialize (IHo fs Heqfs).
      pose proof (fs_compacted_group_eq (dir n1 (fs1 ++ fs2)) fs' H).
      simpl in H1. rewrite H1 in H, Heqfs, Heqfs'.
      assert (fs_compact_group fs'0 = fs_compact_group fs).
      * rewrite Heqfs, Heqfs'. do 3 rewrite fs_compacted_group_dir_cons.
        rewrite <- List.app_assoc. reflexivity.
      * rewrite H5. assumption.
    + pose proof (fs_compacted_group_eq (file _x _x0) fs' H). simpl in H1.
      contradiction.
Qed.

Fixpoint fs_compact_groups (gs:list FileSystem) : FileSystem :=
  match gs with
  | nil => nil
  | g::gs' => match fs_compact_group g with
              | None => fs_compact_groups gs'
              | Some x => x :: fs_compact_groups gs'
              end
  end.

Lemma fs_compact_groups_dec : forall (gs:list FileSystem),
    size (fs_compact_groups gs) <=
    fold_right Nat.add O (map (fun x => size x) gs).
Proof.
  intros. induction gs.
  - simpl. unfold size.
    rewrite (fold_level_nil (fun _ => S) O). auto.
  - unfold fs_compact_groups. fold fs_compact_groups.
    functional induction (fs_compact_group a).
    + simpl. pattern (size (fs_compact_groups gs)).
      rewrite <- Nat.add_0_l. revert IHgs. apply Nat.add_le_mono.
      unfold size. rewrite (fold_level_nil (fun _ => S) O). auto.
    + transitivity
        (size (x1 :: nil) + size (fs_compact_groups gs)).
      * rewrite <- size_concat. auto.
      * rewrite map_cons. simpl. apply Nat.add_le_mono_l. assumption.
    + rewrite IHo. simpl. apply Nat.add_le_mono_r. apply Nat.lt_eq_cases.
      left. apply (size_compacted n1 _x _x0 fs' fs1 fs2).
    + rewrite IHo. simpl. apply Nat.add_le_mono_r.
      rewrite size_perm. apply Nat.lt_eq_cases. left.
      apply size_cons_gt.
    + rewrite IHgs. simpl.
      pattern (fold_right Nat.add 0 (map (fun x => size x) gs)) at 1.
      rewrite <- Nat.add_0_l.
      apply Nat.add_le_mono; [apply size_ge_0 | auto].
    + simpl. pattern (size (fs_compact_groups gs)) at 1.
      rewrite <- Nat.add_0_l. apply Nat.add_le_mono;
                                [apply size_ge_0 | assumption].
Qed.

Definition fs_compact_level (fs:FileSystem) : FileSystem :=
  fs_compact_groups (fs_group_level fs).

Lemma fs_compact_level_dec : forall (fs:FileSystem),
    size (fs_compact_level fs) <= size fs.
Proof.
  intro fs. induction fs; unfold fs_compact_level. 1:auto.
  rewrite fs_compact_groups_dec. rewrite size_grouped. auto.
Qed.

Function fs_compact_other (fs:FileSystem)
         {measure size fs} : FileSystem :=
  match fs with
  | nil => nil
  | x::fs' =>
    let x' := match x with
              | file _ _ => x
              | dir n fs' => dir n (fs_compact_other (fs_compact_level fs'))
              end
    in x' :: fs_compact_other fs'
  end.
Proof.
  - intros. rewrite <- teq. assert (fs = (x :: nil) ++ fs').
    1:rewrite teq, teq0; reflexivity. rewrite H. rewrite size_concat.
    pattern (size fs') at 1. rewrite <- Nat.add_0_l.
    apply Nat.add_lt_mono_r. pose proof (size_cons_gt x nil). unfold size in *.
    rewrite fold_level_nil in H0. assumption.
  - intros. rewrite <- teq. assert (fs = (x :: nil) ++ fs').
    1:rewrite teq, teq0; reflexivity. rewrite H. rewrite size_concat.
    pattern (size fs') at 1. rewrite <- Nat.add_0_l. apply Nat.add_lt_mono_r.
    pose proof (size_cons_gt x nil). unfold size in *.
    rewrite fold_level_nil in H0. assumption.
  - intros. rewrite <- teq. assert (fs = (x :: nil) ++ fs').
    1:rewrite teq, teq0; reflexivity. rewrite H. rewrite size_concat.
    pattern (size (fs_compact_level fs'0)) at 1.
    rewrite <- Nat.add_0_r. apply Nat.add_lt_le_mono.
    + remember (fs_split (x :: nil)) as p. assert (H0 := Heqp).
      rewrite teq0 in H0. unfold fs_split in H0. simpl in H0.
      rewrite Heqp in H0. clear Heqp p. rewrite app_nil_r in H0.
      symmetry in H0. rewrite (split_size (x :: nil) H0). simpl.
      apply Nat.lt_succ_r. apply fs_compact_level_dec.
    + apply size_ge_0.
Qed.

Definition fs_compact (fs:FileSystem) : FileSystem :=
  fs_compact_other (fs_compact_level fs).

Definition fs_merge (fs1 fs2:FileSystem) : FileSystem :=
  fs_compact (fs_sort (fs1 ++ fs2)).

Fixpoint fs_inode_lookup (x:Inode.t) (fs:FileSystem) : option Inode.t :=
  match fs with
  | nil => None
  | x'::fs' => if IM.eqb x x'
               then Some x'
               else fs_inode_lookup x fs'
  end.

Fixpoint fs_find (xs:list Inode.t) (fs:FileSystem) : Prop :=
  match xs with
  | nil => True
  | x::xs' => match fs_inode_lookup x fs with
              | None => False
              | Some x' => match x' with
                           | file _ _ => fs_find xs' nil
                           | dir _ fs' => fs_find xs' fs'
                           end
              end
  end.

Fixpoint fs_inode_lookup_group (x:Inode.t) (gs:list FileSystem) : option Inode.t :=
  match gs with
  | nil => None
  | g::gs' => match fs_inode_lookup x g with
              | Some y => Some y
              | None => fs_inode_lookup_group x gs'
              end
  end.

Lemma fs_lookup_eq : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some y -> Inode.eq x y.
Proof.
  intros. induction fs; simpl in H. 1:discriminate H.
  case_eq (IM.eqb x a); intro H0. rewrite H0 in H. inversion H.
  - rewrite H2 in H0. rewrite IM.eqb_alt in H0.
    destruct (Inode.compare x y); try discriminate H0. assumption.
  - rewrite H0 in H. specialize (IHfs H). assumption.
Qed.

Lemma fs_lookup_cons_none : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x (y :: fs) = None -> fs_inode_lookup x fs = None.
Proof.
  intros. unfold fs_inode_lookup in H.
  fold fs_inode_lookup in H. destruct (IM.eqb x y); [discriminate H | assumption].
Qed.

Lemma fs_lookup_cons_some : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some y -> exists (z:Inode.t),
      fs_inode_lookup x (y :: fs) = Some z.
Proof.
  intros. unfold fs_inode_lookup in H. destruct fs. 1:discriminate.
  fold fs_inode_lookup in H. case_eq (IM.eqb x n); intro H0; rewrite H0 in H.
  - inversion H. rewrite H2 in H0. exists y. simpl. rewrite H0. reflexivity.
  - exists y. simpl. destruct (IM.eqb x y). 1:reflexivity.
    rewrite H0. assumption.
Qed.

Lemma fs_lookup_inserted : forall (x x' y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some x' -> exists (z:Inode.t),
      fs_inode_lookup x (fs_sort_insert y fs) = Some z.
Proof.
  intros. induction fs. 1:discriminate H. simpl. destruct (Inode.compare y a).
  - simpl. destruct (IM.eqb x y).
    + exists y. reflexivity.
    + simpl in H. rewrite H. exists x'. reflexivity.
  - simpl. destruct (IM.eqb x y).
    + exists y. reflexivity.
    + simpl in H. rewrite H. exists x'. reflexivity.
  - simpl in *. destruct (IM.eqb x a).
    + exists a. reflexivity.
    + specialize (IHfs H). assumption.
Qed.

Lemma fs_lookup_sorted_level : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some y -> exists (z:Inode.t),
      fs_inode_lookup x (fs_sort_level fs) = Some z.
Proof.
  intros x y fs. revert x y. induction fs; intros. 1:discriminate H.
  simpl. simpl in H. case_eq (IM.eqb x a); intro H0; rewrite H0 in H.
  - inversion H. rewrite H2 in H0. clear H H2 a. clear IHfs.
    remember (fs_sort_level fs) as fs'. clear Heqfs' fs.
    induction fs'; simpl. 1:rewrite H0; eauto.
    destruct (Inode.compare y a); simpl; try (rewrite H0; eauto).
    destruct (IM.eqb x a); [eauto | assumption].
  - specialize (IHfs x y H). remember (fs_sort_level fs) as fs'.
    clear Heqfs' H y fs. destruct IHfs as [y IHfs].
    induction fs'. 1:discriminate. simpl.
    destruct (Inode.compare a a0); simpl; case_eq (IM.eqb x a0); intro;
      try (rewrite H0); eauto; simpl in IHfs; rewrite H in IHfs; eauto.
Qed.

Lemma fs_lookup_sorted : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some y -> exists (z:Inode.t),
      fs_inode_lookup x (fs_sort fs) = Some z.
Proof.
  intros. unfold fs_sort.
  assert (exists (z:Inode.t), fs_inode_lookup x (fs_sort_level fs) = Some z).
  1:apply (fs_lookup_sorted_level x fs H). remember (fs_sort_level fs) as fs'.
  clear H Heqfs' y fs. destruct H0 as [y H0].
  functional induction fs_sort_other fs'; simpl in H0.
  - discriminate.
  - simpl. destruct (IM.eqb x (file _x _x0)). 1:eauto.
    specialize (IHf H0). assumption.
  - remember (fs_sort_other (fs_sort_level fs'0)) as fs.
    case_eq (IM.eqb x (dir n fs'0)); intro H; rewrite H in H0;
      destruct x; simpl in H.
    + rewrite IM.eqb_alt in H. destruct (Inode.compare (file n0 n1) (dir n fs'0));
                                 discriminate H || contradiction.
    + rewrite IM.eqb_alt in H.
      destruct (Inode.compare (dir n0 l) (dir n fs'0)); try discriminate H.
      simpl in *. rewrite e. assert (IM.eqb (dir n l) (dir n fs) = true).
      * rewrite IM.eqb_alt.
        destruct (Inode.compare (dir n l) (dir n fs)); try reflexivity;
          simpl in *; contradiction (Nat.lt_irrefl n).
      * rewrite H1. eauto.
    + specialize (IHf0 H0). simpl.
      destruct (IM.eqb (file n0 n1) (dir n fs)); [eauto | assumption].
    + specialize (IHf0 H0). simpl.
      destruct (IM.eqb (dir n0 l) (dir n fs)); [eauto | assumption].
Qed.

Lemma fs_lookup_grouped_level : forall (x y:Inode.t) (fs:FileSystem),
    fs_inode_lookup x fs = Some y -> exists (z:Inode.t),
      fs_inode_lookup_group x (fs_group_level fs) = Some z.
Proof.
  intros x y fs. revert x y. induction fs; intros. 1:discriminate H.
  simpl in H. case_eq (IM.eqb x a); intro H0; rewrite H0 in H.
  - inversion H. rewrite H2 in H0. simpl. destruct (fs_group_level fs).
    + simpl. rewrite H0. eauto.
    + destruct (hd_error f); try (destruct (IM.eqb y n));
        simpl; rewrite H0; eauto.
  - specialize (IHfs x y H). destruct IHfs as [z IHfs].
    simpl. destruct (fs_group_level fs).
    + unfold fs_inode_lookup_group in IHfs. discriminate.
    + destruct (hd_error f); try (destruct (IM.eqb a n)); simpl; rewrite H0;
        simpl in IHfs; rewrite IHfs; eauto.
Qed.
