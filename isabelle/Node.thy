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

end
