theory
  FS_Size
imports
  Main
begin

datatype ('n, 't) node =
  File "'n \<times> 't" |
  Dir "'n \<times> (('n, 't) node) list"

type_synonym ('n, 't) filesystem = "('n, 't) node list"

fun node_level :: "('n, 't) node \<Rightarrow> nat" where
  "node_level (File _) = 1" |
  "node_level (Dir d) =
    Suc (foldr (\<lambda> x. max (node_level x)) (snd d) 0)"

definition fs_level :: "('n, 't) filesystem \<Rightarrow> nat" where
  "fs_level fs = foldr (\<lambda> x. max (node_level x)) fs 0"

lemma level_eq [simp]:
  fixes x :: "('n, 't) node"
  shows "fs_level [x] = node_level x"
  unfolding fs_level_def by auto

lemma level_eq_0 [simp]:
  fixes fs :: "('n, 't) filesystem"
  assumes A: "fs_level fs = 0"
  shows "fs = []"
proof (cases fs)
  case Nil
  thus ?thesis by blast
next
  case (Cons f fs)
  moreover
  have "node_level f \<ge> 1" by (case_tac f; auto)
  ultimately
  show ?thesis using A unfolding fs_level_def by auto
qed

lemma level_cons:
  fixes x :: "('n, 't) node" and xs :: "('n, 't) filesystem"
  shows "fs_level (x # xs) = max (node_level x) (fs_level xs)"
  unfolding fs_level_def by auto

lemma level_concat:
  fixes xs xs' :: "('n, 't) filesystem"
  shows "fs_level (xs @ xs') = max (fs_level xs) (fs_level xs')"
proof (induction xs)
  case Nil
  show ?case unfolding fs_level_def by auto
next
  case (Cons x xs)
  thus ?case using level_cons [of x] by auto
qed

primrec node_split where
  "node_split (File f) = (File f, [])" |
  "node_split (Dir d) = (Dir (fst d, []), snd d)"

definition fs_split where
  "fs_split fs = (
    let node_acc = \<lambda> p acc. (fst p # fst acc, snd p @ snd acc) in
    foldr node_acc (map node_split fs) ([], []) )"

lemma split_eq [simp]:
  fixes x h :: "('n, 't) node" and t :: "('n, 't) filesystem"
  shows "node_split x = (h, t) \<Longrightarrow> fs_split [x] = ([h], t)"
  unfolding fs_split_def by auto

lemma split_cons:
  fixes x :: "('n, 't) node" and xs :: "('n, 't) filesystem"
  shows "let (h, t) = node_split x in
    let (l, r) = fs_split xs in
    fs_split (x # xs) = (h # l, t @ r)"
  unfolding fs_split_def by auto

lemma split_concat:
  fixes xs xs' :: "('n, 't) filesystem"
  shows "let (l, r) = fs_split xs in
    let (l', r') = fs_split xs' in
    fs_split (xs @ xs') = (l @ l', r @ r')"
proof (induction xs)
  case Nil
  show ?case unfolding fs_split_def by auto
next
  case (Cons x xs)
  thus ?case
    using split_cons [of x xs] split_cons [of x "xs @ xs'"]
    by auto
qed

lemma split_split_left:
  fixes fs :: "('n, 't) filesystem"
  shows "let (l, _) = fs_split fs in fs_split l = (l, [])"
proof (induction fs)
  case Nil
  show ?case unfolding fs_split_def by auto
next
  case (Cons f fs)
  thus ?case
    using split_cons [of f fs]
    unfolding fs_split_def
    by (case_tac f; auto)
qed

lemma node_head_level [simp]:
  fixes x :: "('n, 't) node"
  shows "let (h, _) = node_split x in node_level h = 1"
  by (case_tac x; auto)

lemma node_split_level:
  fixes x :: "('n, 't) node"
  shows "let (h, t) = node_split x in
    node_level x = max (node_level h) (Suc (fs_level t))"
  unfolding fs_level_def by (case_tac x; auto)

lemma fs_head_level [simp]:
  fixes xs :: "('n, 't) filesystem"
  shows "let (l, _) = fs_split xs in max 1 (fs_level l) = 1"
proof (induction xs)
  case Nil
  show ?case unfolding fs_level_def fs_split_def by auto
next
  case (Cons x xs)
  let ?h = "fst (node_split x)"
  show ?case
    using Cons.IH level_cons [of ?h]
    using split_cons [of x xs] node_head_level [of x]
    by auto
qed

lemma fs_split_level:
  fixes xs :: "('n, 't) filesystem"
  shows "let (l, r) = fs_split xs in
    max 1 (fs_level xs) = max (fs_level l) (Suc (fs_level r))"
proof (induction xs)
  case Nil
  show ?case unfolding fs_level_def fs_split_def by auto
next
  case (Cons x xs)
  let ?h = "fst (node_split x)"
  let ?t = "snd (node_split x)"
  let ?l = "fst (fs_split xs)"
  let ?r = "snd (fs_split xs)"
  show ?case
    using Cons.IH level_cons [of x xs] level_cons [of ?h ?l]
    using level_concat [of ?t ?r] split_cons [of x xs]
    using node_head_level [of x] node_split_level [of x]
    using fs_head_level [of xs]
    by auto
qed

function (sequential) fold_level ::
  "(('n, 't) node \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('n, 't) filesystem \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "fold_level f xs a0 = (
     case fs_level xs of
       0 \<Rightarrow> foldr f xs a0 |
       Suc _ \<Rightarrow> (
         let (l, r) = fs_split xs
         in foldr f l (fold_level f r a0) ))"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>(_, fs, _). fs_level fs)"; auto)
  fix xs :: "('n, 't) filesystem"
  show "\<And>n _ _ l r.
    fs_level xs = Suc n \<Longrightarrow> (l, r) = fs_split xs \<Longrightarrow>
    fs_level r < Suc n"
    using fs_split_level [of xs] by auto
qed

definition size :: "('n, 't) filesystem \<Rightarrow> nat" where
  "size fs = fold_level (\<lambda> _. Suc) fs 0"

lemma foldr_suc:
  fixes fs :: "('n, 't) filesystem"
    and a0 :: nat
  shows "foldr (\<lambda> _. Suc) fs (Suc a0) =
    Suc (foldr (\<lambda> _. Suc) fs a0)"
  by (induction fs; auto)

lemma fold_level_suc [simp]:
  fixes fs :: "('n, 't) filesystem"
    and a0 :: nat
  shows "fold_level (\<lambda> _. Suc) fs (Suc a0) =
    Suc (fold_level (\<lambda> _. Suc) fs a0)"
proof (induction "fs_level fs" arbitrary: fs)
  case 0
  thus ?case using foldr_suc [of fs] by auto
next
  case (Suc n)
  let ?r = "snd (fs_split fs)"
  have "fs_level ?r = n"
    using fs_head_level [of fs] fs_split_level [of fs]
    using Suc.hyps by auto
  hence "fold_level (\<lambda> _. Suc) ?r (Suc a0) =
    Suc (fold_level (\<lambda> _. Suc) ?r a0)"
    using Suc.hyps by blast
  thus ?case using foldr_suc
    by (case_tac "fs_level fs"; case_tac "fs_split fs"; auto)
qed

lemma fold_level_comm:
  fixes xs :: "('n, 't) filesystem"
    and a0 :: nat
  shows "let (l, r) = fs_split xs in
    foldr (\<lambda> _. Suc) l (fold_level (\<lambda> _. Suc) r a0) =
    fold_level (\<lambda> _. Suc) r (foldr (\<lambda> _. Suc) l a0)"
proof (induction xs)
  case Nil
  show ?case unfolding fs_split_def by auto
next
  case (Cons x xs)
  show ?case
    using Cons.IH split_cons [of x xs] split_split_left [of "x # xs"]
    by auto

lemma size_comm:
  fixes xs ys :: "('n, 't) filesystem"
  shows "size (xs @ ys) = size (ys @ xs)"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  show ?case
    using Cons.IH [of ys]
    unfolding size_def
    by auto
  proof (induction ys arbitrary: xs)
    case Nil
    show ?case by auto
  next
    case (Cons y ys)
    show ?case using Cons.IH [of "y # xs"] by auto

proof (induction x arbitrary: xs rule: node_level.induct)
  case (1 f)
  show ?case
    unfolding size_def
    using split_cons [of "File f" xs] by auto
    by (case_tac xs; auto)

lemma node_size_comm:
  fixes x y :: "('n, 't) node"
  shows "size [x, y] = size [y, x]"
proof (cases x)
  case (File f)
  show ?thesis
    unfolding size_def
    using split_cons [of x "[y]"] split_cons [of "y" "[x]"]
    by auto

lemma size_in_list:
  fixes xs ys :: "('n, 't) filesystem"
  shows "(\<And> x. x \<in> set xs \<Longrightarrow>
      size (x # ys) = size [x] + size ys) \<Longrightarrow>
    size (xs @ ys) = size xs + size ys"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case unfolding size_def by auto
next
  case (Cons x xs)
  print_cases
  show ?case
    using Cons.prems [of x] Cons.IH [of "x # ys"]
    by auto
    (*using Cons.IH [of "xs @ ys"]*)

  thus ?case by auto

(*
lemma size_split:
  fixes xs :: "('n, 't) filesystem"
  shows "let (l, r) = fs_split xs in size xs = length l + size r"
proof (induction xs)
  case Nil
  show ?case unfolding fs_split_def by auto
next
  case (Cons x xs)
  thus ?case by auto
*)
lemma size_cons:
  fixes x :: "('n, 't) node" and xs :: "('n, 't) filesystem"
  shows "size (x # xs) = size [x] + size xs"
proof (induction x arbitrary: xs rule: node_level.induct)
  case (1 f)
  show ?case
    unfolding size_def
    using split_cons [of "File f" xs]
    by (case_tac xs; auto)
next
  case (2 d)
  let ?r = "snd (fs_split xs)"
  show ?case
    unfolding size_def
    using "2.IH" [of _ ?r] split_cons [of "Dir d" xs]
    by auto


  case Nil
  show ?case unfolding size_def by auto
next
  case (Cons x xs)
  show ?case
(*    using Cons.IH [of x'] split_cons [of x "x' # xs"]*)
    unfolding size_def
    by auto

lemma size_cons:
  fixes x :: "('n, 't) node" and xs :: "('n, 't) filesystem"
  shows "size (x # xs) = size [x] + size xs"
proof (induction xs arbitrary: x)
  case Nil
  show ?case unfolding size_def by auto
next
  case (Cons x' xs)
  show ?case
    using Cons.IH [of x'] split_cons [of x "x' # xs"]
    unfolding size_def
    by auto


  have "\<And> l r. fs_split [] = (l, r) \<Longrightarrow> l = [] \<and> r = []"
    unfolding fs_split_def by auto
  thus ?thesis
    unfolding fs_level_def size_def
    using split_cons [of x xs] split_cons [of x Nil] by auto

proof (induction xs arbitrary: x)
  case Nil
  show ?case unfolding size_def by auto
next
  case (Cons x xs)
  thus ?case unfolding size_def by auto

lemma concat_size:
  fixes xs ys :: "('n, 't) filesystem"
  shows "size (xs @ ys) = size xs + size ys"
proof (induction xs)
  case Nil
  show ?case unfolding size_def by auto
next
  case (Cons x xs)
  thus ?case unfolding size_def by auto

(*
lemma split_size_l:
  fixes fs :: "('n, 't) filesystem"
  shows "let (l, _) = fs_split fs in size l = length l"
proof (induction fs)
  case Nil
  show ?case unfolding fs_split_def size_def by auto
next
  case (Cons f fs)
  thus ?case 
    using split_cons [of f fs] by auto
*)

lemma split_size:
  fixes fs :: "('n, 't) filesystem"
  shows "let (l, r) = fs_split fs in
    size fs = size l + size r"
proof (induction fs)
  case Nil
  show ?case unfolding fs_split_def size_def by auto
next
  case (Cons f fs)
  thus ?case using split_cons [of f fs] by auto

  let ?l = "fst (fs_split fs)"
  have "size ?l = length ?l"
    unfolding fs_split_def size_def using split_cons by auto
  thus ?case unfolding size_def using split_cons [of f fs] by auto

  then show ?case sorry
next
  case (2 f v va a0)
  then show ?case sorry
qed
  
  
  
  case (1)
  thus ?case by auto
  case (1 a a0)

end
