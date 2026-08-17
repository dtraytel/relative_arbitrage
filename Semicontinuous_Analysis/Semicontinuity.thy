
(*<*)
theory Semicontinuity
  imports "HOL-Analysis.Analysis"
begin

(*>*)

text \<open>
  Upper and lower semicontinuity, in the \<open>\<epsilon>\<close>-\<open>\<delta>\<close> form the comparison-principle
  machinery consumes throughout: closure under \<open>+\<close>, positive scaling, and
  subtracting a continuous function; usc/lsc from ordinary continuity;
  attainment of the sup/inf of a semicontinuous function on a nonempty
  compact set; and bounded extension of an usc function off a closed set.
\<close>

subsection \<open>Attainment for semicontinuous functions on compact sets\<close>

lemma lsc_attains_inf_gen:
  fixes f :: "'a::metric_space \<Rightarrow> real" and S :: "'a set"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and B: "\<And>y. y \<in> S \<Longrightarrow> B \<le> f y"
    and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S" and "\<And>y. y \<in> S \<Longrightarrow> f z \<le> f y"
proof -
  define m where "m = (INF y \<in> S. f y)"
  have bdd: "bdd_below (f ` S)" by (rule bdd_belowI[of _ B]) (use B in auto)
  have neI: "f ` S \<noteq> {}" using neS by auto
  have mlow: "\<And>y. y \<in> S \<Longrightarrow> m \<le> f y"
    unfolding m_def by (rule cInf_lower[OF _ bdd]) auto
  have pick: "\<exists>zz. zz \<in> S \<and> f zz < m + 1 / real (Suc j)" for j :: nat
  proof -
    have "m < m + 1 / real (Suc j)" by simp
    then have "Inf (f ` S) < m + 1 / real (Suc j)" unfolding m_def .
    then have "\<exists>t \<in> f ` S. t < m + 1 / real (Suc j)"
      using cInf_less_iff[OF neI bdd, of "m + 1 / real (Suc j)"] by blast
    then show ?thesis by auto
  qed
  then obtain zs where zsS: "\<And>j. zs j \<in> S"
    and zsm: "\<And>j. f (zs j) < m + 1 / real (Suc j)" by metis
  obtain z r where zS: "z \<in> S" and rm: "strict_mono r"
    and lim: "(zs \<circ> r) \<longlonglongrightarrow> z"
    using compact_eq_seq_compact_metric[THEN iffD1, OF cS]
      zsS unfolding seq_compact_def by blast
  have zle: "f z \<le> m"
  proof (rule ccontr)
    assume "\<not> f z \<le> m"
    then have mlt: "m < f z" by simp
    define c where "c = (m + f z) / 2"
    have c2: "2 * c = m + f z" unfolding c_def by simp
    have cm: "m < c" and cz: "c < f z" using mlt c2 by linarith+
    obtain e where e0: "0 < e"
      and en: "\<forall>y. dist z y < e \<longrightarrow> c < f y" using lsc[OF cz] by blast
    obtain N1 where N1: "\<And>l. N1 \<le> l \<Longrightarrow> dist ((zs \<circ> r) l) z < e"
      using lim e0 unfolding lim_sequentially by blast
    have tend: "(\<lambda>l. 1 / real (Suc (r l))) \<longlonglongrightarrow> 0"
      using LIMSEQ_subseq_LIMSEQ[OF LIMSEQ_Suc[OF lim_1_over_n] rm]
      by (simp add: o_def)
    have "eventually (\<lambda>l. 1 / real (Suc (r l)) < c - m) sequentially"
      by (rule order_tendstoD(2)[OF tend]) (use cm in simp)
    then obtain N2 where N2: "\<And>l. N2 \<le> l \<Longrightarrow> 1 / real (Suc (r l)) < c - m"
      unfolding eventually_sequentially by blast
    define l where "l = max N1 N2"
    have "c < f (zs (r l))"
      using en N1[of l] unfolding l_def by (simp add: o_def dist_commute)
    moreover have "f (zs (r l)) < m + 1 / real (Suc (r l))" by (rule zsm)
    moreover have "1 / real (Suc (r l)) < c - m"
      using N2[of l] unfolding l_def by simp
    ultimately show False by linarith
  qed
  show ?thesis
  proof (rule that[OF zS])
    fix y assume yS: "y \<in> S"
    show "f z \<le> f y" using zle mlow[OF yS] by linarith
  qed
qed

lemma usc_attains_sup_gen:
  fixes f :: "'a::metric_space \<Rightarrow> real" and S :: "'a set"
  assumes usc: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and B: "\<And>y. y \<in> S \<Longrightarrow> f y \<le> B"
    and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S" and "\<And>y. y \<in> S \<Longrightarrow> f y \<le> f z"
proof -
  have lsc': "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < - f y" if "c < - f z" for c z
  proof -
    have "f z < - c" using that by linarith
    from usc[OF this] obtain e where e0: "0 < e"
      and ey: "\<forall>y. dist z y < e \<longrightarrow> f y < - c" by blast
    show ?thesis by (rule exI[of _ e]) (use e0 ey in force)
  qed
  have B': "\<And>y. y \<in> S \<Longrightarrow> - B \<le> - f y" using B by simp
  show ?thesis
  proof (rule lsc_attains_inf_gen[where f = "\<lambda>y. - f y" and S = S and B = "- B",
          OF lsc' B' cS neS])
    fix z assume zS: "z \<in> S" and zm: "\<And>y. y \<in> S \<Longrightarrow> - f z \<le> - f y"
    show thesis
    proof (rule that[OF zS])
      fix y assume "y \<in> S"
      then show "f y \<le> f z" using zm by simp
    qed
  qed
qed

text \<open>Existential repackaging: an \<open>obtains\<close>-rule cannot be consumed by
  \<open>obtain \<dots> by (rule \<dots>)\<close> (the schematic \<open>thesis\<close> swallows the whole goal), so
  the consumers below use these forms.\<close>

lemma lsc_attains_inf_ex:
  fixes f :: "'a::metric_space \<Rightarrow> real" and S :: "'a set"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and B: "\<And>y. y \<in> S \<Longrightarrow> B \<le> f y"
    and cS: "compact S" and neS: "S \<noteq> {}"
  shows "\<exists>z \<in> S. \<forall>y \<in> S. f z \<le> f y"
proof (rule lsc_attains_inf_gen[OF lsc B cS neS])
  fix z assume zS: "z \<in> S" and zm: "\<And>y. y \<in> S \<Longrightarrow> f z \<le> f y"
  show ?thesis using zS zm by blast
qed

subsection \<open>A little upper-semicontinuity calculus\<close>

text \<open>All in the \<open>\<epsilon>\<close>-form the comparison machinery uses, and on an arbitrary
  metric space so that they apply on the product \<open>K \<times> K'\<close> of the two-domain
  doubling.\<close>

lemma usc_eps_add:
  fixes f g :: "'a::metric_space \<Rightarrow> real"
  assumes F: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and G: "\<And>c z. g z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> g y < c"
    and lt: "f z + g z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y + g y < c"
proof -
  define d where "d = (c - f z - g z) / 2"
  have d0: "0 < d" unfolding d_def using lt by simp
  have fc: "f z < f z + d" using d0 by simp
  have gc: "g z < g z + d" using d0 by simp
  obtain e1 where e10: "0 < e1"
    and h1: "\<And>y. dist z y < e1 \<Longrightarrow> f y < f z + d" using F[OF fc] by blast
  obtain e2 where e20: "0 < e2"
    and h2: "\<And>y. dist z y < e2 \<Longrightarrow> g y < g z + d" using G[OF gc] by blast
  have sum: "f z + d + (g z + d) = c" unfolding d_def by simp
  show ?thesis
  proof (rule exI[of _ "min e1 e2"], intro conjI allI impI)
    show "0 < min e1 e2" using e10 e20 by simp
  next
    fix y assume "dist z y < min e1 e2"
    then have "dist z y < e1" and "dist z y < e2" by simp_all
    from h1[OF this(1)] h2[OF this(2)] show "f y + g y < c" using sum by linarith
  qed
qed

lemma usc_eps_scale:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes F: "\<And>c z. f z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
    and t0: "0 < \<theta>" and lt: "\<theta> * f z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> \<theta> * f y < c"
proof -
  have "f z < c / \<theta>" using lt t0 by (simp add: field_simps)
  from F[OF this] obtain e where e0: "0 < e"
    and h: "\<And>y. dist z y < e \<Longrightarrow> f y < c / \<theta>" by blast
  show ?thesis
  proof (rule exI[of _ e], intro conjI allI impI e0)
    fix y assume "dist z y < e"
    from h[OF this] show "\<theta> * f y < c" using t0 by (simp add: field_simps)
  qed
qed

lemma usc_eps_of_continuous:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes cf: "isCont f z" and lt: "f z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> f y < c"
proof -
  have d0: "0 < c - f z" using lt by simp
  from cf obtain s where s0: "0 < s"
    and sb: "\<And>y. y \<noteq> z \<Longrightarrow> dist y z < s \<Longrightarrow> dist (f y) (f z) < c - f z"
    unfolding isCont_def LIM_def using d0 by blast
  show ?thesis
  proof (rule exI[of _ s], intro conjI allI impI s0)
    fix y assume dzy: "dist z y < s"
    show "f y < c"
    proof (cases "y = z")
      case True then show ?thesis using lt by simp
    next
      case False
      have "dist y z < s" using dzy by (simp add: dist_commute)
      from sb[OF False this] show ?thesis by (simp add: dist_real_def)
    qed
  qed
qed

text \<open>Extension of a bounded usc function off a closed set.  The extension
  value must be \<^emph>\<open>below\<close> every value on \<open>K\<close>: extending by \<open>0\<close> need not be
  usc.  Semicontinuity is stated in the \<open>\<epsilon>\<close>-form the comparison chain
  consumes.\<close>

lemma usc_extension_bounded:
  fixes u :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes cl: "closed K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y \<in> K. dist z y < e \<longrightarrow> u y < c"
    and Bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
    and B0: "0 \<le> B"
  obtains u' where "\<And>y. y \<in> K \<Longrightarrow> u' y = u y"
    and "\<And>y. \<bar>u' y\<bar> \<le> B"
    and "\<And>c z. u' z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u' y < c"
proof -
  define u' where "u' = (\<lambda>y. if y \<in> K then u y else - B)"
  have agree: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y" unfolding u'_def by simp
  have bnd: "\<And>y. \<bar>u' y\<bar> \<le> B" unfolding u'_def using Bd B0 by auto
  have ue: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u' y < c" if lt: "u' z < c" for c z
  proof (cases "z \<in> K")
    case True
    have uzc: "u z < c" using lt agree[OF True] by simp
    obtain e where e0: "0 < e"
      and eK: "\<forall>y \<in> K. dist z y < e \<longrightarrow> u y < c"
      using usc[OF True uzc] by blast
    have "- B \<le> u z" using Bd[OF True] by linarith
    then have mBc: "- B < c" using uzc by linarith
    have "u' y < c" if "dist z y < e" for y
      using eK that mBc unfolding u'_def by (cases "y \<in> K") auto
    then show ?thesis using e0 by blast
  next
    case False
    then have znK: "z \<notin> K" by simp
    have mBc: "- B < c" using lt znK unfolding u'_def by simp
    show ?thesis
    proof (cases "K = {}")
      case True
      have "u' y < c" for y using mBc True unfolding u'_def by simp
      then show ?thesis by (intro exI[of _ 1]) auto
    next
      case False
      have d0: "0 < infdist z K"
        by (rule infdist_pos_not_in_closed[OF cl False znK])
      have "u' y < c" if dy: "dist z y < infdist z K" for y
      proof -
        have "y \<notin> K" using infdist_le[of y K z] dy by (auto simp: dist_commute)
        then show ?thesis using mBc unfolding u'_def by simp
      qed
      then show ?thesis using d0 by blast
    qed
  qed
  show ?thesis by (rule that[OF agree bnd ue])
qed

lemma lsc_diff_continuous:
  fixes f \<psi> :: "real^'n::finite \<Rightarrow> real"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and cont: "continuous_on UNIV \<psi>"
    and lt: "c < f z - \<psi> z"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y - \<psi> y"
proof -
  define d where "d = (f z - \<psi> z - c) / 2"
  have d0: "0 < d" using lt unfolding d_def by simp
  have cz: "continuous (at z) \<psi>"
    using cont by (simp add: continuous_on_eq_continuous_at)
  obtain s where s0: "0 < s"
    and sd: "\<And>y. dist y z < s \<Longrightarrow> dist (\<psi> y) (\<psi> z) < d"
    using cz d0 unfolding continuous_at_eps_delta by blast
  have dd: "2 * d = f z - \<psi> z - c" unfolding d_def by simp
  have big: "c + \<psi> z + d < f z" using lt dd d0 by linarith
  obtain e where e0: "0 < e"
    and en: "\<forall>y. dist z y < e \<longrightarrow> c + \<psi> z + d < f y"
    using lsc[OF big] by blast
  have "0 < min e s" using e0 s0 by simp
  moreover have "\<forall>y. dist z y < min e s \<longrightarrow> c < f y - \<psi> y"
  proof (intro allI impI)
    fix y assume dy: "dist z y < min e s"
    then have f1: "c + \<psi> z + d < f y" using en by simp
    have "dist (\<psi> y) (\<psi> z) < d"
      using dy by (intro sd) (simp add: dist_commute)
    then have f2: "\<psi> y - \<psi> z < d" by (simp add: dist_real_def abs_less_iff)
    show "c < f y - \<psi> y" using f1 f2 by linarith
  qed
  ultimately show ?thesis by blast
qed

text \<open>A continuous real-valued difference attains its supremum on a nonempty
  compact set.\<close>

lemma sup_diff_attained_on_compact:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and ne: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>x \<in> K. \<forall>y \<in> K. u y - w y \<le> u x - w x"
proof -
  have "continuous_on K (\<lambda>y. u y - w y)"
    by (intro continuous_intros cu cw)
  then show ?thesis
    by (rule continuous_attains_sup[OF cK ne])
qed

(*<*)
end
(*>*)
