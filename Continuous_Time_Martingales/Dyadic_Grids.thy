section \<open>The dyadic ceiling\<close>

(*<*)
theory Dyadic_Grids
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>\<open>dyceil n U x\<close> rounds \<open>x\<close> up to the dyadic grid of mesh \<open>2\<^sup>-\<^sup>n\<close>,
  capped at the horizon \<open>U\<close>.  Applied to a stopping time bounded by \<open>U\<close>
  it gives stopping times with finitely many values that decrease to it,
  the usual route from simple to general stopping times.\<close>

definition dyceil :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "dyceil n U x = min U (real_of_int \<lceil>2^n * x\<rceil> / 2^n)"

lemma dyceil_le_U: "dyceil n U x \<le> U"
  unfolding dyceil_def by simp

lemma dyceil_ge:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "x \<le> dyceil n U x"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have "2^n * x \<le> real_of_int \<lceil>2^n * x\<rceil>" by (rule le_of_int_ceiling)
  then have "x \<le> real_of_int \<lceil>2^n * x\<rceil> / 2^n" using p by (simp add: field_simps)
  then show ?thesis unfolding dyceil_def using xU by simp
qed

lemma dyceil_nonneg:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "0 \<le> dyceil n U x"
  using x dyceil_ge[OF x xU, of n] by simp

text \<open>Finitely many values --- which is what makes sampling at the
  approximating simple stopping times a finite sum.\<close>

lemma dyceil_range:
  assumes U: "0 \<le> U" and x: "0 \<le> x" and xU: "x \<le> U"
  shows "dyceil n U x
      \<in> (\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>}"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have lo: "0 \<le> \<lceil>2^n * x\<rceil>"
  proof -
    have "(0::real) \<le> 2^n * x" using x by simp
    then have "\<lceil>(0::real)\<rceil> \<le> \<lceil>2^n * x\<rceil>" by (rule ceiling_mono)
    then show ?thesis by simp
  qed  have hi: "\<lceil>2^n * x\<rceil> \<le> \<lceil>2^n * U\<rceil>" using xU by (intro ceiling_mono) simp
  show ?thesis unfolding dyceil_def using lo hi by (intro image_eqI) auto
qed

lemma finite_dyceil_range:
  "finite ((\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>})"
  by (rule finite_imageI) simp

text \<open>The key computation: below the horizon, \<open>dyceil\<close> is at most \<open>t\<close> exactly
  when the original time is at most the grid point just below \<open>t\<close>, which is
  \<open>\<le> t\<close>, so the event lands in the filtration at \<open>t\<close>.\<close>

lemma dyceil_le_iff:
  assumes t: "0 \<le> t" and tU: "t < U"
  shows "(dyceil n U x \<le> t) = (x \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n)"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have "(dyceil n U x \<le> t) = (real_of_int \<lceil>2^n * x\<rceil> / 2^n \<le> t)"
    unfolding dyceil_def using tU by (auto simp: min_le_iff_disj)
  also have "\<dots> = (real_of_int \<lceil>2^n * x\<rceil> \<le> 2^n * t)"
    using p by (simp add: field_simps)
  also have "\<dots> = (\<lceil>2^n * x\<rceil> \<le> \<lfloor>2^n * t\<rfloor>)" by (simp add: le_floor_iff)
  also have "\<dots> = (2^n * x \<le> real_of_int \<lfloor>2^n * t\<rfloor>)" by (simp add: ceiling_le_iff)
  also have "\<dots> = (x \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n)"
    using p by (simp add: field_simps)
  finally show ?thesis .
qed

lemma dyceil_grid_le:
  assumes t: "0 \<le> t"
  shows "real_of_int \<lfloor>2^n * t\<rfloor> / 2^n \<le> t" and "0 \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have "real_of_int \<lfloor>2^n * t\<rfloor> \<le> 2^n * t" by (rule of_int_floor_le)
  then show "real_of_int \<lfloor>2^n * t\<rfloor> / 2^n \<le> t" using p by (simp add: field_simps)
  have "0 \<le> 2^n * t" using t by simp
  then have "(0 :: int) \<le> \<lfloor>2^n * t\<rfloor>" by simp
  then show "0 \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n" by simp
qed

lemma dyceil_tendsto:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "(\<lambda>n. dyceil n U x) \<longlonglongrightarrow> x"
proof -
  have bnd: "\<bar>dyceil n U x - x\<bar> \<le> (1/2)^n" for n
  proof -
    have p: "(0 :: real) < 2^n" by simp
    have lo: "x \<le> dyceil n U x" by (rule dyceil_ge[OF x xU])
    have "real_of_int \<lceil>2^n * x\<rceil> < 2^n * x + 1"
      using ceiling_correct[of "2^n * x"] by simp
    then have "real_of_int \<lceil>2^n * x\<rceil> / 2^n \<le> x + 1 / 2^n"
      using p by (simp add: field_simps)
    then have "dyceil n U x \<le> x + 1 / 2^n"
      unfolding dyceil_def by simp
    with lo show ?thesis by (simp add: power_one_over)
  qed
  have "(\<lambda>n. dyceil n U x - x) \<longlonglongrightarrow> 0"
  proof (rule Lim_null_comparison)
    show "\<forall>\<^sub>F n in sequentially. norm (dyceil n U x - x) \<le> (1/2)^n"
      using bnd by simp
    show "(\<lambda>n. ((1 :: real)/2)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) simp_all
  qed
  then show ?thesis by (rule Lim_transform[OF tendsto_const])
qed

text \<open>And the stopping-time property survives: \<open>{dyceil \<circ> \<sigma> \<le> t}\<close> is
  \<open>{\<sigma> \<le> (grid point below t)}\<close>, an event of the filtration at that grid
  point, hence at \<open>t\<close>.\<close>

lemma dyceil_stopping:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} \<in> sets (F t)"
proof (cases "t < U")
  case True
  define g where "g = real_of_int \<lfloor>2^n * t\<rfloor> / 2^n"
  have g0: "0 \<le> g" unfolding g_def by (rule dyceil_grid_le(2)[OF t])
  have gt: "g \<le> t" unfolding g_def by (rule dyceil_grid_le(1)[OF t])
  have "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} = {\<omega> \<in> space M. \<sigma> \<omega> \<le> g}"
    unfolding g_def using dyceil_le_iff[OF t True] by simp
  moreover have "{\<omega> \<in> space M. \<sigma> \<omega> \<le> g} \<in> sets (F t)"
    using stop[OF g0] mono[OF g0 gt] by blast
  ultimately show ?thesis by simp
next
  case False
  have "dyceil n U (\<sigma> \<omega>) \<le> t" for \<omega>
  proof -
    have "dyceil n U (\<sigma> \<omega>) \<le> U" by (rule dyceil_le_U)
    then show ?thesis using False by simp
  qed
  then have "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} = space M" by blast  moreover have "space M \<in> sets (F t)"
  proof -
    have "space (F t) = space M" using sub[OF t] by (simp add: subalgebra_def)
    then show ?thesis using sets.top[of "F t"] by simp
  qed
  ultimately show ?thesis by simp
qed

(*<*)
end
(*>*)
