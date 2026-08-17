section \<open>Strictly sorted lists, and a product of indicators\<close>

(*<*)
theory Sorted_Lists
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>Four facts with no Brownian content, used when a finite-dimensional
  distribution is read off a strictly increasing list of times.\<close>

lemma prod_indicator_conj:
  "finite J \<Longrightarrow> (\<Prod>s\<in>J. (indicator (A s) (g s) :: ennreal))
     = (if \<forall>s\<in>J. g s \<in> A s then 1 else 0)"
  by (induction J rule: finite_induct) (auto simp: indicator_def)

lemma sorted_wrt_less_nth_iff:
  fixes l :: "'a :: linorder list"
  assumes l: "sorted_wrt (<) l" and k: "k < length l" and j: "j < length l"
  shows "l ! j < l ! k \<longleftrightarrow> j < k"
proof
  assume "j < k" then show "l ! j < l ! k"
    using l k by (intro sorted_wrt_nth_less) auto
next
  assume lt: "l ! j < l ! k"
  have "\<not> k \<le> j"
  proof
    assume kj: "k \<le> j"
    have "l ! k \<le> l ! j"
      by (rule sorted_nth_mono[OF strict_sorted_imp_sorted[OF l] kj j])
    with lt show False by (meson leD)
  qed
  then show "j < k" by simp
qed

lemma sorted_wrt_less_set_take:
  fixes l :: "'a :: linorder list"
  assumes l: "sorted_wrt (<) l" and k: "k < length l"
  shows "{v \<in> set l. v < l ! k} = set (take k l)"
proof (intro equalityI subsetI)
  fix v assume "v \<in> {v \<in> set l. v < l ! k}"
  then obtain j where j: "j < length l" "v = l ! j" "l ! j < l ! k"
    by (auto simp: in_set_conv_nth)
  have jk: "j < k"
    using sorted_wrt_less_nth_iff[OF l k j(1)] j(3) by simp
  have "take k l ! j = l ! j"
    using jk by (rule nth_take)
  moreover have "j < length (take k l)"
    using jk k j(1) by simp
  ultimately show "v \<in> set (take k l)"
    using j(2) by (metis nth_mem)
next
  fix v assume "v \<in> set (take k l)"
  then obtain j where j: "j < length (take k l)" "take k l ! j = v"
    by (metis in_set_conv_nth)
  have jk: "j < k" and jl: "j < length l"
    using j(1) k by auto
  have vj: "v = l ! j"
    using j(2) nth_take[OF jk, of l] by simp
  have "v \<in> set l"
    using jl vj by simp
  moreover have "v < l ! k"
    using sorted_wrt_less_nth_iff[OF l k jl] jk vj by simp
  ultimately show "v \<in> {v \<in> set l. v < l ! k}" by blast
qed

lemma sorted_wrt_less_Max_last:
  "sorted_wrt (<) xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Max (set xs) = last xs"
proof (induction xs)
  case (Cons a xs)
  show ?case
  proof (cases "xs = []")
    case True then show ?thesis by simp
  next
    case False
    have hd: "a < hd xs"
      using Cons.prems False by (cases xs) auto
    have "a \<le> Max (set xs)"
      by (meson False Max_ge List.finite_set dual_order.trans hd
          hd_in_set less_imp_le)
    then have "Max (set (a # xs)) = Max (set xs)"
      using False by (simp add: max_absorb2)
    also have "\<dots> = last xs"
      using Cons False by simp
    finally show ?thesis using False by simp
  qed
qed simp


(*<*)
end
(*>*)
