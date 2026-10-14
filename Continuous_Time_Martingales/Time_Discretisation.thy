

(*<*)
theory Time_Discretisation
  imports Sampled_Quadratic_Variation
begin

(*>*)

text \<open>
  Sampling a continuous-time martingale on a time grid.  \<open>time_grid\<close> is
  an increasing grid of nonnegative times and \<open>sampled_martingale\<close> a
  square-integrable continuous-time martingale read along it.  The sampled
  process is a discrete-time square-integrable martingale for the sampled
  filtration (\<open>sq_int_martingale_sampled\<close>), so every result of the
  discrete-time calculus (\<open>Quadratic_Variation\<close>: compensated square,
  optional sampling, stopped Dynkin identity) is available along the grid,
  through the sublocale \<open>D\<close> below.\<close>

section \<open>Time grids\<close>

locale time_grid =
  fixes t :: "nat \<Rightarrow> real"
  assumes t_nonneg: "0 \<le> t 0"
    and t_step: "\<And>n. t n \<le> t (Suc n)"
begin

lemma t_ge_0: "0 \<le> t n"
  using t_nonneg lift_Suc_mono_le[of t, OF t_step, of 0 n] by simp

lemma mono_t: "mono t"
  by (rule mono_iff_le_Suc[THEN iffD2]) (rule allI, rule t_step)

end

section \<open>A continuous-time martingale sampled on a grid\<close>

locale sampled_martingale = martingale M F "0 :: real" Y + time_grid t
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" +
  assumes Y_sq_integrable: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (Y u \<omega>)\<^sup>2)"

sublocale sampled_martingale
  \<subseteq> D: sq_int_martingale M "\<lambda>n. F (t n)" "\<lambda>n. Y (t n)"
  by (intro sq_int_martingale_sampled t_ge_0 mono_t Y_sq_integrable)
    unfold_locales

(*<*)
end
(*>*)
