theory
  FileSystem
imports
  Main
  Node
begin

type_synonym ('n, 't) filesystem = "('n, 't) node list"

fun node_level :: "('n, 't) node \<Rightarrow> nat" where
  "node_level (File _) = 1" |
  "node_level (Dir d) =
    Suc (foldr (\<lambda> x. max (node_level x)) (snd d) 0)"

definition fs_level :: "('n, 't) filesystem \<Rightarrow> nat" where
  "fs_level fs = foldr (\<lambda> x. max (node_level x)) fs 0"

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
  "node_split (File f) = (File f, Nil)" |
  "node_split (Dir d) = (Dir (fst d, Nil), snd d)"

definition fs_split where
  "fs_split fs = (
    let node_acc = \<lambda> p acc. (fst p # fst acc, snd p @ snd acc) in
    foldr node_acc (map node_split fs) (Nil, Nil) )"

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

end