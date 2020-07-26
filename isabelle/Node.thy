theory
  Node
imports
  Main
begin

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

lemma lt_le:
  fixes xs ys :: "('a::preorder) list"
  shows "xs < ys \<Longrightarrow> xs \<le> ys"
  by (induction xs arbitrary: ys; case_tac ys; auto)

lemma lt_not_le:
  fixes xs ys :: "('a::preorder) list"
  shows "xs < ys \<Longrightarrow> ys \<le> xs \<Longrightarrow> False" (is "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R")
proof -
  have "\<And> x y :: 'a::preorder . x < y \<Longrightarrow> y < x \<Longrightarrow> False"
    using less_irrefl less_trans by auto
  moreover
  have "\<And> x y :: 'a::preorder . x < y \<Longrightarrow> y \<le> x \<Longrightarrow> False"
    using less_irrefl le_less_trans by auto
  moreover
  have "\<And> x y :: 'a::preorder . x \<le> y \<Longrightarrow> y < x \<Longrightarrow> False"
    using less_irrefl le_less_trans by auto
  ultimately
  show "?P \<Longrightarrow> ?Q \<Longrightarrow> ?R"
    by (induction xs arbitrary: ys; case_tac ys; auto)
qed

lemma le_imp_not_le_lt:
  fixes x y :: "'a::preorder"
  shows "x \<le> y \<Longrightarrow> \<not> y \<le> x \<longleftrightarrow> x < y"
  using less_le_not_le by blast

lemma le_not_le_lt:
  fixes xs ys :: "('a::preorder) list"
  shows "xs \<le> ys \<Longrightarrow> \<not> ys \<le> xs \<Longrightarrow> xs < ys"
  using le_imp_not_le_lt
  by (induction xs arbitrary: ys; case_tac ys; auto)

lemma le_trans:
  fixes xs ys zs :: "('a::preorder) list"
  shows "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
proof (induction ys arbitrary: xs zs)
  case Nil
  thus ?case by (case_tac xs; case_tac zs; auto)
next
  case (Cons y ys)
  note c = Cons
  thus ?case
  proof (cases xs)
    case Nil thus ?thesis by auto
  next
    case (Cons x xs)
    moreover
    have "\<And> z . x < y \<Longrightarrow> y < z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
      using less_trans by blast
    moreover
    have "\<And> z . x \<le> y \<Longrightarrow> y < z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
      using le_less_trans by blast
    moreover
    have "\<And> z . x < y \<Longrightarrow> y \<le> z \<Longrightarrow> \<not> x < z \<Longrightarrow> False"
      using less_le_trans by blast
    moreover
    have "\<And> z . x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using order_trans by blast
    ultimately
    show ?thesis using c by (case_tac zs; auto)
  qed
qed

instance proof
  fix xs ys zs :: "('a::preorder) list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    using lt_le lt_not_le le_not_le_lt by blast
  show "xs \<le> xs" by (induct_tac xs; auto)
  show "xs \<le> ys \<Longrightarrow> ys \<le> zs \<Longrightarrow> xs \<le> zs"
    using le_trans by blast
qed

end

end
