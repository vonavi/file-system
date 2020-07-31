theory
  Node
imports
  Main
begin

lemma le_imp_not_le_lt:
  fixes x y :: "'a::preorder"
  shows "x \<le> y \<Longrightarrow> \<not> y \<le> x \<longleftrightarrow> x < y"
  using less_le_not_le by blast

instantiation prod :: (preorder, preorder) preorder
begin

definition less_eq_prod:
  "less_eq_prod p\<^sub>x p\<^sub>y \<longleftrightarrow>
     fst p\<^sub>x < fst p\<^sub>y \<or> (fst p\<^sub>x \<le> fst p\<^sub>y \<and> snd p\<^sub>x \<le> snd p\<^sub>y)"

definition less_prod:
  "less_prod p\<^sub>x p\<^sub>y \<longleftrightarrow>
     fst p\<^sub>x < fst p\<^sub>y \<or> (fst p\<^sub>x \<le> fst p\<^sub>y \<and> snd p\<^sub>x < snd p\<^sub>y)"

lemma order_trans_prod:
  fixes p\<^sub>x p\<^sub>y p\<^sub>z :: "'n::preorder \<times> 't::preorder"
  shows "p\<^sub>x \<le> p\<^sub>y \<Longrightarrow> p\<^sub>y \<le> p\<^sub>z \<Longrightarrow> p\<^sub>x \<le> p\<^sub>z" (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
proof -
  have "fst p\<^sub>x < fst p\<^sub>y \<Longrightarrow> fst p\<^sub>y \<le> fst p\<^sub>z \<Longrightarrow> fst p\<^sub>x < fst p\<^sub>z"
    by (rule less_le_trans)
  moreover
  have "fst p\<^sub>x \<le> fst p\<^sub>y \<Longrightarrow> fst p\<^sub>y < fst p\<^sub>z \<Longrightarrow> fst p\<^sub>x < fst p\<^sub>z"
    by (rule le_less_trans)
  moreover
  have "fst p\<^sub>x < fst p\<^sub>z \<Longrightarrow> \<not> fst p\<^sub>x < fst p\<^sub>z \<Longrightarrow> False"
    using less_trans less_irrefl by blast
  moreover
  have "fst p\<^sub>x \<le> fst p\<^sub>y \<Longrightarrow> fst p\<^sub>y \<le> fst p\<^sub>z \<Longrightarrow> fst p\<^sub>x \<le> fst p\<^sub>z"
    by (rule order_trans)
  moreover
  have "snd p\<^sub>x \<le> snd p\<^sub>y \<Longrightarrow> snd p\<^sub>y \<le> snd p\<^sub>z \<Longrightarrow> snd p\<^sub>x \<le> snd p\<^sub>z"
    by (rule order_trans)
  ultimately
  show "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R"
    using less_trans
    unfolding less_eq_prod by blast
qed

instance proof
  fix p\<^sub>x p\<^sub>y p\<^sub>z :: "'n::preorder \<times> 't::preorder"
  show "p\<^sub>x < p\<^sub>y \<longleftrightarrow> p\<^sub>x \<le> p\<^sub>y \<and> \<not> p\<^sub>y \<le> p\<^sub>x"
    unfolding less_eq_prod and less_prod
    by (simp only: less_le_not_le) blast
  show "p\<^sub>x \<le> p\<^sub>x" unfolding less_eq_prod by blast
  show "p\<^sub>x \<le> p\<^sub>y \<Longrightarrow> p\<^sub>y \<le> p\<^sub>z \<Longrightarrow> p\<^sub>x \<le> p\<^sub>z"
    by (rule order_trans_prod)
qed

end

instantiation list :: (preorder) preorder
begin

fun less_eq_list where
  "less_eq_list [] _ \<longleftrightarrow> True" |
  "less_eq_list _ [] \<longleftrightarrow> False" |
  "less_eq_list (x # xs) (y # ys) \<longleftrightarrow>
     x < y \<or> (x \<le> y \<and> less_eq_list xs ys)"

fun less_list where
  "less_list [] [] \<longleftrightarrow> False" |
  "less_list [] _ \<longleftrightarrow> True" |
  "less_list _ [] \<longleftrightarrow> False" |
  "less_list (x # xs) (y # ys) \<longleftrightarrow>
     x < y \<or> (x \<le> y \<and> less_list xs ys)"

lemma lt_le_list:
  fixes xs ys :: "('a::preorder) list"
  shows "xs < ys \<Longrightarrow> xs \<le> ys"
  by (induction xs arbitrary: ys; case_tac ys; auto)

lemma lt_not_le_list:
  fixes xs ys :: "('a::preorder) list"
  shows "xs < ys \<Longrightarrow> ys \<le> xs \<Longrightarrow> False"
proof (induction xs rule: less_eq_list.induct)
  case (1 xs)
  thus ?case by (case_tac xs; auto)
next
  case (2 y ys)
  thus ?case by auto
next
  case (3 x xs y ys)
  moreover
  have "x < y \<Longrightarrow> y < x \<Longrightarrow> False"
    using less_irrefl less_trans by blast
  moreover
  have "\<And> x y :: 'a::preorder. x \<le> y \<Longrightarrow> y < x \<Longrightarrow> False"
    using less_irrefl le_less_trans by blast
  ultimately
  show ?case by auto
qed

lemma le_not_le_lt_list:
  fixes xs ys :: "('a::preorder) list"
  shows "xs \<le> ys \<Longrightarrow> \<not> ys \<le> xs \<Longrightarrow> xs < ys"
  using le_imp_not_le_lt
  by (induction xs arbitrary: ys; case_tac ys; auto)

lemma le_trans_list:
  fixes xs ys zs :: "('a::preorder) list"
  shows "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
proof (induction ys arbitrary: xs rule: less_eq_list.induct)
  case (1 ys)
  thus ?case by (case_tac xs; case_tac ys; auto)
next
  case (2 z zs)
  thus ?case by (case_tac xs; auto)
next
  case (3 z zs y ys)
  moreover
  have "\<And> x. x < y \<Longrightarrow> y < z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
    using less_trans by blast
  moreover
  have "\<And> x. x \<le> y \<Longrightarrow> y < z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
    using le_less_trans by blast
  moreover
  have "\<And> x. x < y \<Longrightarrow> y \<le> z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
    using less_le_trans by blast
  ultimately
  show ?case using order_trans by (case_tac xs; auto)
qed

instance proof
  fix xs ys zs :: "('a::preorder) list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    using lt_le_list lt_not_le_list le_not_le_lt_list by blast
  show "xs \<le> xs" by (induct_tac xs; auto)
  show "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
    using le_trans_list by blast
qed

end

datatype ('n, 't) node =
  File "'n \<times> 't" |
  Dir "'n \<times> (('n, 't) node) list"

instantiation node :: (preorder, preorder) preorder
begin

fun less_eq_node where
  "less_eq_node (File f\<^sub>x) (File f\<^sub>y) \<longleftrightarrow> f\<^sub>x \<le> f\<^sub>y" |
  "less_eq_node (File f\<^sub>x) (Dir d\<^sub>y) \<longleftrightarrow> fst f\<^sub>x \<le> fst d\<^sub>y" |
  "less_eq_node (Dir f\<^sub>x) (File d\<^sub>y) \<longleftrightarrow> fst f\<^sub>x < fst d\<^sub>y" |
  "less_eq_node (Dir d\<^sub>x) (Dir d\<^sub>y) \<longleftrightarrow> fst d\<^sub>x \<le> fst d\<^sub>y"

fun less_node where
  "less_node (File f\<^sub>x) (File f\<^sub>y) \<longleftrightarrow> f\<^sub>x < f\<^sub>y" |
  "less_node (File f\<^sub>x) (Dir d\<^sub>y) \<longleftrightarrow> fst f\<^sub>x \<le> fst d\<^sub>y" |
  "less_node (Dir d\<^sub>x) (File f\<^sub>y) \<longleftrightarrow> fst d\<^sub>x < fst f\<^sub>y" |
  "less_node (Dir d\<^sub>x) (Dir d\<^sub>y) \<longleftrightarrow> fst d\<^sub>x < fst d\<^sub>y"

lemma lt_le_node:
  fixes xs ys :: "('n::preorder, 't::preorder) node"
  shows "xs < ys \<Longrightarrow> xs \<le> ys"
  using less_imp_le
  by (case_tac xs; case_tac ys; auto)

lemma lt_not_le_node:
  fixes xs ys :: "('n::preorder, 't::preorder) node"
  shows "xs < ys \<Longrightarrow> ys \<le> xs \<Longrightarrow> False" (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
proof -
  have "\<And> x y :: 'n::preorder . x < y \<Longrightarrow> y \<le> x \<Longrightarrow> False"
    using less_irrefl le_less_trans by auto
  moreover
  have "\<And> x y :: 'n::preorder \<times> 't::preorder .
         x \<le> y \<Longrightarrow> y < x \<Longrightarrow> False"
    using less_irrefl le_less_trans by auto
  ultimately
  show "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R"
    by (case_tac xs; case_tac ys; auto)
qed

lemma le_not_le_lt_node:
  fixes xs ys :: "('n::preorder, 't::preorder) node"
  shows "xs \<le> ys \<Longrightarrow> \<not> ys \<le> xs \<Longrightarrow> xs < ys"
    (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
proof (cases xs)
  case (File p\<^sub>x)
  thus "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R" using le_imp_not_le_lt
    by (case_tac ys; auto)
next
  case (Dir p\<^sub>x)
  thus "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R"
    using le_imp_not_le_lt le_not_le_lt_list
    by (case_tac ys; auto)
qed

lemma le_trans_node:
  fixes xs ys zs :: "('n::preorder, 't::preorder) node"
  shows "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
    (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
proof -
  have "\<And> p\<^sub>x p\<^sub>y n\<^sub>z . p\<^sub>x \<le> p\<^sub>y \<Longrightarrow> fst p\<^sub>y \<le> n\<^sub>z \<Longrightarrow> fst p\<^sub>x \<le> n\<^sub>z"
    using order_trans less_imp_le
    unfolding less_eq_prod by blast
  moreover
  have "\<And> p\<^sub>x n\<^sub>y p\<^sub>z . fst p\<^sub>x \<le> n\<^sub>y \<Longrightarrow> n\<^sub>y < fst p\<^sub>z \<Longrightarrow> p\<^sub>x \<le> p\<^sub>z"
    using le_less_trans
    unfolding less_eq_prod by blast
  moreover
  have "\<And> n\<^sub>x p\<^sub>y p\<^sub>z . n\<^sub>x < fst p\<^sub>y \<Longrightarrow> p\<^sub>y \<le> p\<^sub>z \<Longrightarrow> n\<^sub>x < fst p\<^sub>z"
    using less_trans less_le_trans
    unfolding less_eq_prod by blast
  moreover
  have "\<And> n\<^sub>x n\<^sub>y n\<^sub>z :: 'n::preorder .
         n\<^sub>x < n\<^sub>y \<Longrightarrow> n\<^sub>y \<le> n\<^sub>z \<Longrightarrow> n\<^sub>x \<le> n\<^sub>z"
    using less_imp_le less_le_trans
    unfolding less_prod by blast
  ultimately
  show "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R"
    using order_trans le_less_trans
    by (case_tac xs; case_tac ys; case_tac zs; auto)
qed

instance proof
  fix xs ys zs :: "('n::preorder, 't::preorder) node"
  show "xs < ys \<longleftrightarrow> (xs \<le> ys \<and> \<not> ys \<le> xs)"
    using lt_le_node lt_not_le_node le_not_le_lt_node by blast
  show "xs \<le> xs" by (case_tac xs; auto)
  show "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
    using le_trans_node by blast
qed

end

end
