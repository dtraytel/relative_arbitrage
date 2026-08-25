section \<open>The covariation constraint: quotients and densities\<close>

(*<*)
theory Covariation_Density
  imports Exit_Class
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
  what the derivative notation asserts.  Neither of the two analytic steps the
  paper takes is available in the Isabelle distribution or in the AFP, so both
  are proved here.\<close>


section \<open>Lipschitz paths are absolutely continuous\<close>

lemma lipschitz_imp_absolutely_continuous_on:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes lip: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> norm (f x - f y) \<le> M * \<bar>x - y\<bar>"
  shows "absolutely_continuous_on S f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix e :: real assume e: "0 < e"
  define MM where "MM = max M 0"
  have MM0: "0 \<le> MM" unfolding MM_def by simp
  have lip': "norm (f x - f y) \<le> MM * \<bar>x - y\<bar>" if "x \<in> S" "y \<in> S" for x y
  proof -
    have "M * \<bar>x - y\<bar> \<le> MM * \<bar>x - y\<bar>"
      unfolding MM_def by (intro mult_right_mono) auto
    then show ?thesis using lip[OF that] by linarith
  qed
  define d where "d = e / (MM + 1)"
  have d0: "0 < d" unfolding d_def using e MM0 by simp
  show "\<exists>\<delta>>0. \<forall>d T. d division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>d. content k) < \<delta>
       \<longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < e"
  proof (intro exI[of _ d] conjI d0 allI impI)
    fix dd T assume H: "dd division_of T \<and> T \<subseteq> S \<and> (\<Sum>k\<in>dd. content k) < d"
    then have dv: "dd division_of T" and TS: "T \<subseteq> S"
      and small: "(\<Sum>k\<in>dd. content k) < d" by auto
    have bound: "norm (f (Sup k) - f (Inf k)) \<le> MM * content k" if kd: "k \<in> dd" for k
    proof -
      obtain a b where kb: "k = {a..b}" and kT: "k \<subseteq> T" and ab: "a \<le> b"
        by (metis atLeastatMost_empty_iff box_real(2) cbox_division_memE dv kd)
      have aS: "a \<in> S" and bS: "b \<in> S"
        using kT TS kb ab by auto
      have "norm (f (Sup k) - f (Inf k)) = norm (f b - f a)"
        unfolding kb using ab by simp
      also have "\<dots> \<le> MM * \<bar>b - a\<bar>" by (rule lip'[OF bS aS])
      also have "\<dots> = MM * content k" unfolding kb using ab by simp
      finally show ?thesis .
    qed
    have "(\<Sum>k\<in>dd. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>dd. MM * content k)"
      by (rule sum_mono) (use bound in blast)
    also have "\<dots> = MM * (\<Sum>k\<in>dd. content k)" by (simp add: sum_distrib_left)
    also have "\<dots> \<le> MM * d" using small MM0 by (intro mult_left_mono) auto
    also have "\<dots> < e" unfolding d_def using e MM0 by (simp add: field_simps)
    finally show "(\<Sum>k\<in>dd. norm (f (Sup k) - f (Inf k))) < e" .
  qed
qed

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
proof -
  define h where "h = (\<lambda>n::nat. 1 / (real n + 1))"
  have h0: "0 < h n" for n unfolding h_def by simp
  have hlim: "h \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_inverse_real_of_nat)
    moreover have "(\<lambda>n. inverse (real (Suc n))) = h"
      unfolding h_def by (simp add: inverse_eq_divide add.commute)
    ultimately show ?thesis by simp
  qed
  define q where "q = (\<lambda>n. (1 / h n) *\<^sub>R (g (x + h n) - g x))"
  have qS: "q n \<in> S" for n
  proof -
    have "(1/((x + h n) - x)) *\<^sub>R (g (x + h n) - g x) \<in> S"
      using x0 h0[of n] by (intro dq) auto
    then show ?thesis unfolding q_def by simp
  qed
  have hd: "(g has_derivative (\<lambda>u. u *\<^sub>R D)) (at x)"
    using der unfolding has_vector_derivative_def .
  have "q \<longlonglongrightarrow> D"
  proof (rule tendstoI)
    fix e :: real assume e: "0 < e"
    obtain d where d0: "0 < d"
      and est: "\<And>x'. 0 < norm (x' - x) \<Longrightarrow> norm (x' - x) < d \<Longrightarrow>
          norm (g x' - g x - (x' - x) *\<^sub>R D) / norm (x' - x) < e"
      using hd e unfolding has_derivative_at' by blast
    have ev: "\<forall>\<^sub>F n in sequentially. h n < d"
      by (rule order_tendstoD(2)[OF hlim d0])
    show "\<forall>\<^sub>F n in sequentially. dist (q n) D < e"
      using ev
    proof eventually_elim
      case (elim n)
      have hn: "0 < h n" by (rule h0)
      have nx: "norm ((x + h n) - x) = h n" using hn by simp
      have "norm (g (x + h n) - g x - (h n) *\<^sub>R D) / h n < e"
        using est[of "x + h n"] hn elim nx by simp
      moreover have "q n - D = (1 / h n) *\<^sub>R (g (x + h n) - g x - (h n) *\<^sub>R D)"
        unfolding q_def using hn by (simp add: algebra_simps)
      ultimately have "norm (q n - D) < e"
        using hn by (simp add: divide_inverse mult.commute)
      then show ?case by (simp add: dist_norm)
    qed
  qed
  then show ?thesis using cl qS closed_sequentially by blast
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
  have lip1: "norm (g u - g v) \<le> M * (u - v)" if uv: "0 \<le> v" "v < u" for u v
  proof -
    have q: "(1/(u-v)) *\<^sub>R (g u - g v) \<in> S"
      using dq uv unfolding dq_cond_def by blast
    have le: "norm ((1/(u-v)) *\<^sub>R (g u - g v)) \<le> M" by (rule M[OF q])
    have "norm (g u - g v) = (u - v) * norm ((1/(u-v)) *\<^sub>R (g u - g v))"
      using uv by simp
    also have "\<dots> \<le> (u - v) * M" using le uv by (intro mult_left_mono) auto
    finally show ?thesis by (simp add: mult.commute)
  qed
  have lip: "norm (g u - g v) \<le> M * \<bar>u - v\<bar>" if "0 \<le> u" "0 \<le> v" for u v
  proof (cases "u = v" "v < u" rule: case_split[case_product case_split])
    case True_True then show ?thesis by simp
  next
    case True_False then show ?thesis by simp
  next
    case False_True
    then have "\<bar>u - v\<bar> = u - v" by simp
    then show ?thesis using lip1[OF that(2)] False_True by simp
  next
    case False_False
    then have ulv: "u < v" by simp
    have a: "norm (g v - g u) \<le> M * (v - u)" by (rule lip1[OF that(1) ulv])
    have b: "norm (g u - g v) = norm (g v - g u)" by (rule norm_minus_commute)
    have c: "\<bar>u - v\<bar> = v - u" using ulv by simp
    show ?thesis unfolding b c using a by simp
  qed
  have ac: "absolutely_continuous_on {0..T} g" if T: "0 \<le> T" for T
    by (rule lipschitz_imp_absolutely_continuous_on[where M = M]) (use lip in auto)
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
