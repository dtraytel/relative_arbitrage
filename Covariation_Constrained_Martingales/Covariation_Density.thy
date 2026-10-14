section \<open>The covariation constraint: quotients and densities\<close>

(*<*)
theory Covariation_Density
  imports
    "Disintegration.Disintegration"
    "Kolmogorov_Chentsov.Dyadic_Interval" "Kolmogorov_Chentsov.Holder_Continuous"
    "Levy_Prokhorov_Metric.Prokhorov_Theorem" "Martingales.Martingale"
    "Continuous_Path_Spaces.Difference_Quotients"
begin
(*>*)

text \<open>Equation (1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> constrains the
  almost-everywhere derivative of the covariation, while the class below asks
  that every difference quotient of the compensator lie in the constraint set.
  The paper uses both readings.  Its compactness lemma asserts that the
  covariation is Lipschitz, rewrites the difference quotient as the average of
  the derivative over the interval, places that average in the constraint set
  because the set is convex and closed, and returns to the derivative by
  Lebesgue's fundamental theorem of calculus and differentiation theorem.

  The two readings are therefore one and the same, and this theory proves it.
  The integral representation presupposes absolute continuity, which is exactly
  what the derivative notation asserts.  Both analytic steps the paper takes
  are in HOL-Analysis: Lipschitz paths are absolutely continuous
  (@{thm [source] Lipschitz_imp_absolutely_continuous}), and paths of bounded
  variation are differentiable almost everywhere
  (@{thm [source] Lebesgue_differentiation_thm}).\<close>


section \<open>An integral mean lies in a closed convex set\<close>

lemma integral_mean_in_convex:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and S :: "'a set"
  assumes cvx: "convex S" and cl: "closed S"
    and st: "s < t"
    and fi: "(f has_integral I) {s..t}"
    and fS: "\<And>r. r \<in> {s..t} \<Longrightarrow> f r \<in> S"
  shows "(1/(t-s)) *\<^sub>R I \<in> S"
proof (rule ccontr)
  assume nS: "(1/(t-s)) *\<^sub>R I \<notin> S"
  obtain a b where lt: "inner a ((1/(t-s)) *\<^sub>R I) < b"
    and sep: "\<And>x. x \<in> S \<Longrightarrow> b < inner a x"
    using separating_hyperplane_closed_point[OF cvx cl nS] by blast
  have blin: "bounded_linear (\<lambda>x. inner x a)" by (rule bounded_linear_inner_left)
  have hi: "((\<lambda>r. inner (f r) a) has_integral inner I a) {s..t}"
    using has_integral_linear[OF fi blin] by (simp add: o_def)
  have hc: "((\<lambda>_. b) has_integral (t - s) * b) {s..t}"
    using has_integral_const_real[of b s t] st by simp
  have le: "(t - s) * b \<le> inner I a"
    by (rule has_integral_le[OF hc hi]) (use sep fS in \<open>fastforce simp: inner_commute\<close>)
  have "b < inner a ((1/(t-s)) *\<^sub>R I)" 
  proof -
    have "b = (1/(t-s)) * ((t - s) * b)" using st by simp
    also have "\<dots> \<le> (1/(t-s)) * inner I a"
      using le st by (intro mult_left_mono) auto
    also have "\<dots> = inner a ((1/(t-s)) *\<^sub>R I)"
      by (simp add: inner_commute)
    finally show ?thesis using lt by linarith
  qed
  then show False using lt by linarith
qed

lemma integral_mean_in_convex_ae:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and S :: "'a set"
  assumes cvx: "convex S" and cl: "closed S" and z: "z \<in> S"
    and st: "s < t"
    and fi: "(f has_integral I) {s..t}"
    and neg: "negligible N"
    and fS: "\<And>r. r \<in> {s..t} - N \<Longrightarrow> f r \<in> S"
  shows "(1/(t-s)) *\<^sub>R I \<in> S"
proof -
  define f' where "f' = (\<lambda>r. if r \<in> N then z else f r)"
  have "(f' has_integral I) {s..t}"
    by (rule has_integral_spike[OF neg _ fi]) (simp add: f'_def)
  moreover have "f' r \<in> S" if "r \<in> {s..t}" for r
    unfolding f'_def using z fS that by auto
  ultimately show ?thesis
    by (rule integral_mean_in_convex[OF cvx cl st, where f = f' and I = I]) auto
qed

section \<open>A derivative of a path with quotients in \<open>S\<close> lies in \<open>S\<close>\<close>

lemma vector_derivative_in_closed_set:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cl: "closed S" and x0: "0 \<le> x"
    and dq: "\<And>s t. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> (1/(t-s)) *\<^sub>R (g t - g s) \<in> S"
    and der: "(g has_vector_derivative D) (at x)"
  shows "D \<in> S"
proof (rule Lim_in_closed_set[OF cl _ trivial_limit_at_right_real])
  show "((\<lambda>h. (g (x + h) - g x) /\<^sub>R h) \<longlongrightarrow> D) (at_right 0)"
    using tendsto_mono[OF at_le[OF subset_UNIV]
        LIM_offset_zero[OF vector_derivative_works[THEN iffD1, OF differentiableI_vector[OF der],
          unfolded has_vector_derivative_within_1D]]]
    by (simp add: vector_derivative_at[OF der])
  show "\<forall>\<^sub>F h in at_right 0. (g (x + h) - g x) /\<^sub>R h \<in> S"
    by (rule eventually_mono[OF eventually_at_right_less])
      (use dq[of x "x + h" for h] x0 in \<open>auto simp: divide_inverse_commute\<close>)
qed

section \<open>The two readings of the covariation constraint\<close>

definition dq_cond :: "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "dq_cond g S \<longleftrightarrow> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1/(t-s)) *\<^sub>R (g t - g s) \<in> S)"

definition density_cond :: "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "density_cond g S \<longleftrightarrow>
     (\<forall>T. 0 \<le> T \<longrightarrow> absolutely_continuous_on {0..T} g)
   \<and> (\<exists>N. negligible N \<and> (\<forall>t. 0 \<le> t \<longrightarrow> t \<notin> N \<longrightarrow>
          (\<exists>D. (g has_vector_derivative D) (at t) \<and> D \<in> S)))"

lemma dq_imp_density:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cl: "closed S" and bd: "bounded S" and dq: "dq_cond g S"
  shows "density_cond g S"
proof -
  from bd obtain M where M: "\<And>y. y \<in> S \<Longrightarrow> norm y \<le> M"
    unfolding bounded_iff by blast
  have ac: "absolutely_continuous_on {0..T} g" if T: "0 \<le> T" for T
  proof (rule Lipschitz_imp_absolutely_continuous)
    have "(max M 0)-lipschitz_on {0..T} g"
    proof (rule diffquot_lipschitz)
      show "norm a \<le> max M 0" if "a \<in> S" for a using M[OF that] by simp
      show "(1 / (v - u)) *\<^sub>R (g v - g u) \<in> S" if "0 \<le> u" "u < v" "v \<le> T" for u v
        using dq that unfolding dq_cond_def by blast
    qed simp
    then show "norm (g x - g y) \<le> max M 0 * \<bar>x - y\<bar>" if "x \<in> {0..T}" "y \<in> {0..T}" for x y
      using that by (auto dest: lipschitz_onD simp: dist_norm)
  qed
  have bv: "has_bounded_variation_on g {0..T}" if T: "0 \<le> T" for T
    by (rule absolutely_continuous_on_imp_has_bounded_variation_on[OF ac[OF T]]) simp
  have negT: "negligible {x \<in> {0..real n}. \<not> g differentiable (at x)}" for n :: nat
    by (rule Lebesgue_differentiation_thm[OF _ bv]) auto
  define N where "N = (\<Union>n::nat. {x \<in> {0..real n}. \<not> g differentiable (at x)})"
  have negN: "negligible N"
    unfolding N_def by (rule negligible_Union_nat) (use negT in auto)
  have main: "\<exists>D. (g has_vector_derivative D) (at t) \<and> D \<in> S"
    if t0: "0 \<le> t" and tN: "t \<notin> N" for t
  proof -
    obtain n :: nat where tn: "t \<le> real n" using real_arch_simple by blast
    have "t \<in> {0..real n}" using t0 tn by simp
    with tN have diff: "g differentiable (at t)" unfolding N_def by blast
    then have hvd: "(g has_vector_derivative vector_derivative g (at t)) (at t)"
      using vector_derivative_works by blast
    have "vector_derivative g (at t) \<in> S"
      by (rule vector_derivative_in_closed_set[OF cl t0 _ hvd])
        (use dq in \<open>simp add: dq_cond_def\<close>)
    with hvd show ?thesis by blast
  qed
  show ?thesis
    unfolding density_cond_def using ac negN main by blast
qed

lemma density_imp_dq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cvx: "convex S" and cl: "closed S" and dc: "density_cond g S"
  shows "dq_cond g S"
  unfolding dq_cond_def
proof (intro allI impI)
  fix s t :: real assume s0: "0 \<le> s" and st: "s < t"
  from dc obtain N where negN: "negligible N"
    and der: "\<And>u. 0 \<le> u \<Longrightarrow> u \<notin> N \<Longrightarrow>
        \<exists>D. (g has_vector_derivative D) (at u) \<and> D \<in> S"
    and acg: "\<And>T. 0 \<le> T \<Longrightarrow> absolutely_continuous_on {0..T} g"
    unfolding density_cond_def by blast
  define D where "D = (\<lambda>u. SOME d. (g has_vector_derivative d) (at u) \<and> d \<in> S)"
  have Dprop: "(g has_vector_derivative D u) (at u) \<and> D u \<in> S"
    if "0 \<le> u" "u \<notin> N" for u
    unfolding D_def by (rule someI_ex) (use der that in blast)
  have ac: "absolutely_continuous_on {s..t} g"
    by (rule absolutely_continuous_on_subset[OF acg[of t]]) (use s0 st in auto)
  have ftc: "(D has_integral (g t - g s)) {s..t}"
  proof (rule fundamental_theorem_of_calculus_absolutely_continuous[OF negN _ ac])
    show "s \<le> t" using st by simp
    fix u assume uI: "u \<in> {s..t} - N"
    then have u0: "0 \<le> u" and uN: "u \<notin> N" using s0 by auto
    have "(g has_vector_derivative D u) (at u)" using Dprop[OF u0 uN] by blast
    then show "(g has_vector_derivative D u) (at u within {s..t})"
      by (rule has_vector_derivative_at_within)
  qed
  have nonneg: "\<not> negligible {s..t}"
  proof -
    have iff: "negligible (cbox s t) \<longleftrightarrow> box s t = {}"
      by (rule negligible_interval(1))
    have cb: "cbox s t = {s..t}" by simp
    have "box s t \<noteq> {}" using st by simp
    with iff cb show ?thesis by simp
  qed
  then obtain u where uI: "u \<in> {s..t}" and uN: "u \<notin> N"
    using negN by (metis negligible_subset subsetI)
  have zS: "D u \<in> S" using Dprop[of u] uI uN s0 by auto
  show "(1/(t-s)) *\<^sub>R (g t - g s) \<in> S"
    by (rule integral_mean_in_convex_ae[OF cvx cl zS st ftc negN])
      (use Dprop s0 in auto)
qed

theorem dq_iff_density:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "convex S" "closed S" "bounded S"
  shows "dq_cond g S \<longleftrightarrow> density_cond g S"
  using dq_imp_density[OF assms(2,3)] density_imp_dq[OF assms(1,2)] by blast

(*<*)
end
(*>*)
