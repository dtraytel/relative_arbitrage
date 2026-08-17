section \<open>An adapted, everywhere-continuous quadratic variation\<close>

(*<*)
theory Adapted_Quadratic_Variation
  imports Pathwise_Quadratic_Variation Stopped_Localization
begin

(*>*)

text \<open>
  \<open>qvp\<close> is a Borel path functional, but it is neither adapted nor continuous
  everywhere.  This theory repairs both: \<open>qvpc\<close> is a version continuous in
  the time argument, \<open>qvsa\<close> is adapted -- it reads the path only up to the
  current time -- and \<open>qvmata\<close> assembles the matrix-valued form.  The good
  events \<open>qvp_good\<close> and \<open>qvp_goodupto\<close> are where the repair is exact.

  Nothing here mentions the paper; the construction is consumed by it and
  not otherwise specific to it.
\<close>

subsection \<open>The functional reads the path only up to the current time\<close>

text \<open>
  The scalar theory assumes \<open>X\<close> uniformly bounded, because Eq. (2.7)
  (\<open>fourth_moment_bound_bounded\<close>) does.  A member of the class is not bounded,
  so the identification has to be localised --- which is what
  @{theory Continuous_Path_Spaces.Stopped_Localization} was built for: stopping an
  \<open>L\<^sup>2\<close> martingale with continuous paths at any stopping time yields a
  martingale, unconditionally, and the same holds for the compensated square.

  The functional cooperates: \<open>qvps w t\<close> reads \<open>w\<close> only on \<open>{0..t}\<close> --- the
  dyadic grid of \<open>{0..q}\<close> for rational \<open>q < t\<close> --- so on the event that the
  stopping time exceeds \<open>t\<close>, stopping does not change it.  These three
  congruences are what make that precise.
\<close>

lemma dyadic_qsum_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> w s = w' s" and T: "0 \<le> T"
  shows "dyadic_qsum w T n = dyadic_qsum w' T n"
  unfolding dyadic_qsum_def
proof (rule sum.cong[OF refl])
  fix k :: nat assume "k \<in> {..<2 ^ n}"
  then have k: "Suc k \<le> 2 ^ n" by simp
  then have k': "k \<le> 2 ^ n" by simp
  show "(w (T * real (Suc k) / 2 ^ n) - w (T * real k / 2 ^ n))\<^sup>2
      = (w' (T * real (Suc k) / 2 ^ n) - w' (T * real k / 2 ^ n))\<^sup>2"
    using eq[OF grid_bounds(1)[OF T k] grid_bounds(2)[OF T k]]
      eq[OF grid_bounds(1)[OF T k'] grid_bounds(2)[OF T k']]
    by simp
qed

lemma qvp_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> w s = w' s" and T: "0 \<le> T"
  shows "qvp w T = qvp w' T"
  unfolding qvp_def by (simp add: dyadic_qsum_cong[OF eq T])

lemma qvps_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> w s = w' s"
  shows "qvps w t = qvps w' t"
  unfolding qvps_def
proof (intro arg_cong[where f = real_of_ereal] SUP_cong refl)
  fix q :: rat assume "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < t}"
  then have q: "0 \<le> real_of_rat q" and qt: "real_of_rat q < t" by auto
  have "qvp w (real_of_rat q) = qvp w' (real_of_rat q)"
    by (rule qvp_cong[OF _ q]) (use eq qt in auto)
  then show "ereal (qvp w (real_of_rat q)) = ereal (qvp w' (real_of_rat q))"
    by simp
qed

subsection \<open>A continuous version of the scalar functional\<close>

text \<open>
  The pushforward into the pair space needs the second coordinate to be a
  CONTINUOUS path for EVERY path, not merely almost every one, and transferring
  an almost-everywhere statement along a pushforward needs the exceptional set
  to be measurable.  Both are settled at once by cutting the functional down to
  the event where its rational-time data is nondecreasing and Lipschitz.  That
  event is a countable condition, hence measurable; and on it the \<open>limsup\<close>
  extension --- a supremum over rationals below \<open>t\<close> --- inherits the two
  properties, so it is Lipschitz on \<open>{0..}\<close> and therefore continuous.
\<close>

text \<open>At time \<open>0\<close> every dyadic grid collapses to a point, so the functional
  vanishes there for EVERY path.\<close>

lemma qvp_zero [simp]: "qvp w 0 = 0"
  unfolding qvp_def dyadic_qsum_def by (simp add: Limsup_const)

definition qvp_good :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "qvp_good C w \<longleftrightarrow> qvp w 0 = 0 \<and>
     (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat p) \<and>
        qvp w (real_of_rat q) - qvp w (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"

lemma qvp_good_nonneg:
  assumes g: "qvp_good C w" and q: "0 \<le> (q :: rat)"
  shows "0 \<le> qvp w (real_of_rat q)"
  using g q unfolding qvp_good_def by (metis diff_ge_0_iff_ge of_rat_0 order_refl)

lemma qvp_good_ub:
  assumes g: "qvp_good C w" and q: "0 \<le> (q :: rat)"
  shows "qvp w (real_of_rat q) \<le> C * real_of_rat q"
proof -
  have "qvp w (real_of_rat q) - qvp w (real_of_rat 0)
      \<le> C * (real_of_rat q - real_of_rat 0)"
    using g q unfolding qvp_good_def by blast
  then show ?thesis using g unfolding qvp_good_def by simp
qed

lemma qvps_as_Sup:
  assumes g: "qvp_good C w" and C: "0 \<le> C" and t: "0 < t"
  shows "qvps w t
       = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
proof -
  define Q where "Q = {q :: rat. 0 \<le> q \<and> real_of_rat q < t}"
  have ne: "Q \<noteq> {}"
  proof -
    obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < t"
      using t of_rat_dense[of 0 t] by auto
    then show ?thesis unfolding Q_def by (auto simp: less_le)
  qed
  have ub: "qvp w (real_of_rat q) \<le> C * t" if "q \<in> Q" for q
  proof -
    have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
      using that qvp_good_ub[OF g] unfolding Q_def by simp
    also have "\<dots> \<le> C * t" using that C unfolding Q_def by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  have bdd: "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` Q)"
    using ub by (intro bdd_aboveI2) blast
  have fin: "\<bar>SUP q \<in> Q. ereal (qvp w (real_of_rat q))\<bar> \<noteq> \<infinity>"
  proof -
    have le: "(SUP q \<in> Q. ereal (qvp w (real_of_rat q))) \<le> ereal (C * t)"
      using ub by (intro SUP_least) simp
    obtain q0 where q0: "q0 \<in> Q" using ne by blast
    have ge: "ereal (qvp w (real_of_rat q0))
        \<le> (SUP q \<in> Q. ereal (qvp w (real_of_rat q)))"
      using q0 by (rule SUP_upper)
    show ?thesis
    proof (cases "SUP q \<in> Q. ereal (qvp w (real_of_rat q))" rule: ereal_cases)
      case (real r) then show ?thesis by simp
    next
      case PInf then show ?thesis using le by simp
    next
      case MInf then show ?thesis using ge by simp
    qed
  qed
  have E: "ereal (Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` Q))
      = (SUP q \<in> Q. ereal (qvp w (real_of_rat q)))"
    by (rule ereal_SUP[OF fin])
  show ?thesis unfolding qvps_def Q_def[symmetric] by (simp add: E[symmetric])
qed

lemma qvps_mono_lip:
  assumes g: "qvp_good C w" and C: "0 \<le> C" and s: "0 \<le> s" and st: "s \<le> t"
  shows "0 \<le> qvps w t - qvps w s \<and> qvps w t - qvps w s \<le> C * (t - s)"
proof (cases "0 < s")
  case False
  then have s0: "s = 0" using s by simp
  then have qs: "qvps w s = 0" by simp
  show ?thesis
  proof (cases "0 < t")
    case True
    have img: "qvps w t
        = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
      by (rule qvps_as_Sup[OF g C True])
    have ne: "{q :: rat. 0 \<le> q \<and> real_of_rat q < t} \<noteq> {}"
    proof -
      obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < t"
        using True of_rat_dense[of 0 t] by auto
      then show ?thesis by (auto simp: less_le)
    qed
    have le: "qvp w (real_of_rat q) \<le> C * t"
      if "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < t}" for q
    proof -
      have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
        using that qvp_good_ub[OF g] by simp
      also have "\<dots> \<le> C * t" using that C by (intro mult_left_mono) auto
      finally show ?thesis .
    qed
    have nn: "0 \<le> qvps w t"
    proof -
      obtain q0 :: rat where q0: "q0 \<in> {q. 0 \<le> q \<and> real_of_rat q < t}"
        using ne by blast
      have a: "0 \<le> qvp w (real_of_rat q0)"
        using q0 qvp_good_nonneg[OF g] by simp
      have b: "qvp w (real_of_rat q0) \<le> qvps w t"
        unfolding img
        by (rule cSup_upper[OF imageI[OF q0]]) (use le in \<open>auto intro!: bdd_aboveI2\<close>)
      show ?thesis using a b by simp
    qed
    have ub: "qvps w t \<le> C * t"
      unfolding img using ne le by (intro cSup_least) auto
    show ?thesis using qs nn ub s0 by simp
  next
    case False
    then show ?thesis using qs st s0 by simp
  qed
next
  case True
  then have t: "0 < t" using st by simp
  have imgs: "qvps w s
      = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s})"
    by (rule qvps_as_Sup[OF g C True])
  have imgt: "qvps w t
      = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
    by (rule qvps_as_Sup[OF g C t])
  have bddt: "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q))
      ` {q. 0 \<le> q \<and> real_of_rat q < t})"
  proof (intro bdd_aboveI2)
    fix q :: rat assume "q \<in> {q. 0 \<le> q \<and> real_of_rat q < t}"
    then have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
      using qvp_good_ub[OF g] by simp
    also have "\<dots> \<le> C * t"
      using \<open>q \<in> _\<close> C by (intro mult_left_mono) auto
    finally show "qvp w (real_of_rat q) \<le> C * t" .
  qed
  have nes: "{q :: rat. 0 \<le> q \<and> real_of_rat q < s} \<noteq> {}"
  proof -
    obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < s"
      using True of_rat_dense[of 0 s] by auto
    then show ?thesis by (auto simp: less_le)
  qed
  have mono: "qvps w s \<le> qvps w t"
    unfolding imgs imgt
  proof (rule cSup_subset_mono)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s} \<noteq> {}"
      using nes by blast
    show "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q))
        ` {q. 0 \<le> q \<and> real_of_rat q < t})" by (rule bddt)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s}
        \<subseteq> (\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t}"
      using st by auto
  qed
  have lip: "qvps w t \<le> qvps w s + C * (t - s)"
    unfolding imgt
  proof (intro cSup_least)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t} \<noteq> {}"
      using t of_rat_dense[of 0 t] by (auto simp: less_le)
    fix y assume "y \<in> (\<lambda>q :: rat. qvp w (real_of_rat q))
        ` {q. 0 \<le> q \<and> real_of_rat q < t}"
    then obtain q :: rat where q: "0 \<le> q" "real_of_rat q < t"
      and y: "y = qvp w (real_of_rat q)" by auto
    show "y \<le> qvps w s + C * (t - s)"
    proof (cases "real_of_rat q < s")
      case True
      then have "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < s}" using q by simp
      then have "y \<le> qvps w s"
        unfolding y imgs
        by (intro cSup_upper bdd_above_mono[OF bddt]) (use st in auto)
      moreover have "0 \<le> C * (t - s)" using C st by simp
      ultimately show ?thesis by simp
    next
      case False
      then have sq: "s \<le> real_of_rat q" by simp
      show ?thesis
      proof (rule field_le_epsilon)
        fix e :: real assume e: "0 < e"
        have pos: "0 < e / (C + 1)" using e C by simp
        obtain p :: rat where p1: "max 0 (s - e / (C + 1)) < real_of_rat p"
          and p2: "real_of_rat p < s"
          using of_rat_dense[of "max 0 (s - e / (C + 1))" s] pos \<open>0 < s\<close> by auto
        have p0: "0 \<le> p"
        proof -
          have "0 < real_of_rat p" using p1 by simp
          then show ?thesis by simp
        qed
        have pq: "p \<le> q"
        proof -
          have "real_of_rat p \<le> real_of_rat q" using p2 sq by simp
          then show ?thesis by (simp add: of_rat_less_eq)
        qed
        have d1: "y - qvp w (real_of_rat p) \<le> C * (real_of_rat q - real_of_rat p)"
          using g p0 pq unfolding qvp_good_def y by blast
        have d2: "qvp w (real_of_rat p) \<le> qvps w s"
          using p0 p2 unfolding imgs
          by (intro cSup_upper bdd_above_mono[OF bddt]) (use st in auto)
        have d3: "real_of_rat q - real_of_rat p \<le> (t - s) + e / (C + 1)"
          using q p1 by simp
        have d4: "C * (real_of_rat q - real_of_rat p) \<le> C * ((t - s) + e / (C + 1))"
          by (rule mult_left_mono[OF d3 C])
        have "y \<le> qvps w s + C * ((t - s) + e / (C + 1))"
          using d1 d2 d4 by simp
        moreover have "C * ((t - s) + e / (C + 1)) \<le> C * (t - s) + e"
        proof -
          have "C * (e / (C + 1)) \<le> (C + 1) * (e / (C + 1))"
            using pos by (intro mult_right_mono) auto
          also have "\<dots> = e" using C by simp
          finally show ?thesis by (simp add: algebra_simps)
        qed
        ultimately show "y \<le> qvps w s + C * (t - s) + e" by simp
      qed
    qed
  qed
  show ?thesis using mono lip by simp
qed

lemma qvps_continuous:
  assumes g: "qvp_good C w" and C: "0 \<le> C"
  shows "continuous_on {0..} (qvps w)"
proof -
  have "C-lipschitz_on {0..} (qvps w)"
  proof (rule lipschitz_onI)
    show "0 \<le> C" by (rule C)
    fix a b :: real assume ab: "a \<in> {0..}" "b \<in> {0..}"
    show "dist (qvps w a) (qvps w b) \<le> C * dist a b"
    proof (cases "a \<le> b")
      case True
      with qvps_mono_lip[OF g C, of a b] ab show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    next
      case False
      with qvps_mono_lip[OF g C, of b a] ab show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    qed
  qed
  then show ?thesis by (rule lipschitz_on_continuous_on)
qed

subsection \<open>The good event has full measure\<close>

text \<open>The cut-down functional is only useful if the cut discards nothing: under
  the hypotheses of the scalar theory the rational-time data of \<open>qvp\<close> IS the compensator,
  so it is nondecreasing and Lipschitz almost surely.  Stated inside the locale,
  where \<open>qvp_eq_A\<close> identifies \<open>qvp\<close> at each fixed time; the rationals are
  countable, so one intersection covers them all.\<close>

lemma (in bounded_martingale_compensator) qvp_good_ae:
  "AE \<omega> in M. qvp_good C (\<lambda>s. X s \<omega>)"
proof -
  have rat: "AE \<omega> in M. \<forall>q :: rat. 0 \<le> q \<longrightarrow>
      qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
  proof (subst AE_all_countable, intro allI)
    fix q :: rat
    show "AE \<omega> in M. 0 \<le> q \<longrightarrow>
        qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
    proof (cases "0 \<le> q")
      case True
      then have "(0::real) \<le> real_of_rat q" by simp
      from qvp_eq_A[OF this] show ?thesis by eventually_elim simp
    qed simp
  qed
  from rat A0 Arate show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have qeq: "\<And>q :: rat. 0 \<le> q \<Longrightarrow>
        qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
      and z: "A 0 \<omega> = 0"
      and rate: "\<And>p r. 0 \<le> p \<Longrightarrow> p \<le> r \<Longrightarrow>
          0 \<le> A r \<omega> - A p \<omega> \<and> A r \<omega> - A p \<omega> \<le> C * (r - p)" by blast+
    show ?case unfolding qvp_good_def
    proof (intro conjI)
      show "qvp (\<lambda>s. X s \<omega>) 0 = 0" using qeq[of 0] z by simp
      show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
          0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
          \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
              \<le> C * (real_of_rat q - real_of_rat p)"
      proof (intro allI impI)
      fix p q :: rat assume p: "0 \<le> p" and pq: "p \<le> q"
      then have q: "0 \<le> q" by simp
      have pr: "real_of_rat p \<le> real_of_rat q" using pq by (simp add: of_rat_less_eq)
      have p0: "(0::real) \<le> real_of_rat p" using p by simp
      show "0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
          \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
              \<le> C * (real_of_rat q - real_of_rat p)"
        using rate[OF p0 pr] qeq[OF p] qeq[OF q] by simp
      qed
    qed
  qed
qed

subsection \<open>An ADAPTED continuous version\<close>

text \<open>
  Cutting the functional down to the GLOBAL good event of the previous
  subsection makes it continuous for every path, but not adapted: that event
  reads the path at all times.  That is fatal for the bridge --- both
  pushforwards go through \<open>martingale_distr\<close>, whose \<open>pull\<close> hypothesis says
  exactly that the second coordinate of the map is measurable at the current
  time.

  The repair is to cut at a time rather than globally: keep the value
  \<open>qvp w q\<close> only when the rational data BELOW \<open>q\<close> is already nondecreasing and
  Lipschitz.  The resulting supremum reads only times \<open>< t\<close>, so it is adapted;
  it is still monotone and \<open>C\<close>-Lipschitz, hence continuous for EVERY path; and
  on the good event nothing is discarded, so it agrees with \<open>qvps\<close>.
\<close>

definition qvp_goodupto :: "real \<Rightarrow> rat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "qvp_goodupto C u w \<longleftrightarrow>
     (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
        0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat p) \<and>
        qvp w (real_of_rat q) - qvp w (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"

lemma qvp_goodupto_mono:
  assumes g: "qvp_goodupto C u w" and uv: "v \<le> u"
  shows "qvp_goodupto C v w"
  using g uv unfolding qvp_goodupto_def by (meson order_trans)

lemma qvp_good_goodupto:
  assumes g: "qvp_good C w"
  shows "qvp_goodupto C u w"
  using g unfolding qvp_good_def qvp_goodupto_def by blast

lemma qvp_goodupto_nonneg:
  assumes g: "qvp_goodupto C u w" and q: "0 \<le> (q :: rat)" and qu: "q \<le> u"
  shows "0 \<le> qvp w (real_of_rat q)"
proof -
  have "0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat 0)"
    using g q qu unfolding qvp_goodupto_def by blast
  then show ?thesis by simp
qed

lemma qvp_goodupto_ub:
  assumes g: "qvp_goodupto C u w" and q: "0 \<le> (q :: rat)" and qu: "q \<le> u"
  shows "qvp w (real_of_rat q) \<le> C * real_of_rat q"
proof -
  have "qvp w (real_of_rat q) - qvp w (real_of_rat 0)
      \<le> C * (real_of_rat q - real_of_rat 0)"
    using g q qu unfolding qvp_goodupto_def by blast
  then show ?thesis by simp
qed

text \<open>The value kept at a rational time, and the supremum of the values kept
  strictly below \<open>t\<close>.  The index \<open>q = -1\<close> contributes \<open>0\<close>, so the family is
  never empty and the supremum is nonnegative without a case split on \<open>t\<close>.\<close>

definition qvpc :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> rat \<Rightarrow> real" where
  "qvpc C w t q = (if 0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w
                   then qvp w (real_of_rat q) else 0)"

definition qvsa :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "qvsa C w t = (SUP q. qvpc C w t q)"

lemma qvpc_keep:
  assumes "0 \<le> q" and "real_of_rat q < t" and "qvp_goodupto C q w"
  shows "qvpc C w t q = qvp w (real_of_rat q)"
  using assms by (simp add: qvpc_def)

lemma qvpc_drop:
  assumes "\<not> (0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w)"
  shows "qvpc C w t q = 0"
  using assms by (auto simp: qvpc_def)

lemma qvpc_nonneg: "0 \<le> qvpc C w t q"
proof (cases "0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w")
  case True
  then have "qvpc C w t q = qvp w (real_of_rat q)" by (intro qvpc_keep) auto
  moreover have "0 \<le> qvp w (real_of_rat q)"
    using True by (intro qvp_goodupto_nonneg[of C q w q]) auto
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis by (simp add: qvpc_drop)
qed

lemma qvpc_ub:
  assumes C: "0 \<le> C"
  shows "qvpc C w t q \<le> max 0 (C * t)"
proof (cases "0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w")
  case True
  then have v: "qvpc C w t q = qvp w (real_of_rat q)" by (intro qvpc_keep) auto
  have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
    using True by (intro qvp_goodupto_ub[of C q w q]) auto
  also have "\<dots> \<le> C * t" using True C by (simp add: mult_left_mono)
  finally show ?thesis using v by simp
next
  case False
  then show ?thesis by (simp add: qvpc_drop)
qed

lemma qvpc_bdd:
  assumes C: "0 \<le> C"
  shows "bdd_above (range (qvpc C w t))"
  by (rule bdd_aboveI[of _ "max 0 (C * t)"]) (use qvpc_ub[OF C] in blast)

lemma qvsa_upper:
  assumes C: "0 \<le> C"
  shows "qvpc C w t q \<le> qvsa C w t"
  unfolding qvsa_def by (rule cSUP_upper[OF UNIV_I qvpc_bdd[OF C]])

lemma qvsa_nonneg:
  assumes C: "0 \<le> C"
  shows "0 \<le> qvsa C w t"
proof -
  have "qvpc C w t (- 1) = 0" by (rule qvpc_drop) simp
  then show ?thesis using qvsa_upper[OF C, of w t "- 1"] by simp
qed

lemma qvsa_nonpos [simp]:
  assumes C: "0 \<le> C" and t: "t \<le> 0"
  shows "qvsa C w t = 0"
proof -
  have z: "qvpc C w t q = 0" for q
  proof (rule qvpc_drop, rule notI)
    assume "0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w"
    then have "0 \<le> q" and "real_of_rat q < t" by auto
    then have "(0 :: real) \<le> real_of_rat q" and "real_of_rat q < t" by simp_all
    with t show False by simp
  qed
  show ?thesis unfolding qvsa_def by (simp add: z)
qed

lemma qvsa_mono:
  assumes C: "0 \<le> C" and st: "s \<le> t"
  shows "qvsa C w s \<le> qvsa C w t"
proof -
  have pt: "qvpc C w s q \<le> qvpc C w t q" for q
  proof (cases "0 \<le> q \<and> real_of_rat q < s \<and> qvp_goodupto C q w")
    case True
    then have "qvpc C w s q = qvp w (real_of_rat q)" by (intro qvpc_keep) auto
    moreover from True st have "qvpc C w t q = qvp w (real_of_rat q)"
      by (intro qvpc_keep) auto
    ultimately show ?thesis by simp
  next
    case False
    then have "qvpc C w s q = 0" by (simp add: qvpc_drop)
    then show ?thesis using qvpc_nonneg[of C w t q] by simp
  qed
  show ?thesis unfolding qvsa_def
    by (rule cSUP_mono[OF UNIV_not_empty qvpc_bdd[OF C]]) (use pt in blast)
qed

text \<open>The Lipschitz bound.  A value kept at a time \<open>q\<close> beyond \<open>s\<close> is compared
  with one kept just below \<open>s\<close>: the rational data is nondecreasing and Lipschitz
  up to \<open>q\<close>, so the two differ by at most \<open>C\<close> times the gap, and the gap tends to
  \<open>t - s\<close> as the comparison time rises to \<open>s\<close>.\<close>

lemma qvsa_lip:
  assumes C: "0 \<le> C" and st: "s \<le> t"
  shows "qvsa C w t \<le> qvsa C w s + C * (t - s)"
proof -
  have step: "qvpc C w t q \<le> qvsa C w s + C * (t - s)" for q
  proof (cases "0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w")
    case False
    then have "qvpc C w t q = 0" by (simp add: qvpc_drop)
    then show ?thesis using qvsa_nonneg[OF C, of w s] C st by simp
  next
    case True
    then have q0: "0 \<le> q" and qt: "real_of_rat q < t" and gq: "qvp_goodupto C q w"
      by auto
    have v: "qvpc C w t q = qvp w (real_of_rat q)" using True by (intro qvpc_keep) auto
    have main: "qvp w (real_of_rat q) \<le> qvsa C w s + C * (t - s)"
    proof (cases "real_of_rat q < s")
      case True
      have "qvpc C w s q = qvp w (real_of_rat q)"
        using q0 True gq by (intro qvpc_keep) auto
      then have "qvp w (real_of_rat q) \<le> qvsa C w s"
        using qvsa_upper[OF C, of w s q] by simp
      moreover have "0 \<le> C * (t - s)"
        by (rule mult_nonneg_nonneg) (use C st in auto)
      ultimately show ?thesis by simp
    next
      case False
      then have sq: "s \<le> real_of_rat q" by simp
      show ?thesis
      proof (cases "0 < s")
        case False
        then have s0: "s \<le> 0" by simp
        have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
          by (rule qvp_goodupto_ub[OF gq q0 order_refl])
        also have "\<dots> \<le> C * t" using qt C by (simp add: mult_left_mono)
        also have "\<dots> \<le> C * (t - s)" using s0 C by (simp add: mult_left_mono)
        finally show ?thesis using qvsa_nonneg[OF C, of w s] by simp
      next
        case True
        have eps: "qvp w (real_of_rat q) \<le> (qvsa C w s + C * (t - s)) + e"
          if e: "0 < e" for e
        proof -
          define d where "d = e / (C + 1)"
          have d0: "0 < d" using e C by (simp add: d_def)
          have lt: "max 0 (s - d) < s" using True d0 by simp
          obtain r where rQ: "r \<in> \<rat>" and r1: "max 0 (s - d) < r" and r2: "r < s"
            using Rats_dense_in_real[OF lt] by blast
          obtain p :: rat where rp: "r = real_of_rat p"
            using rQ by (auto simp: Rats_def)
          have p0: "0 \<le> p"
          proof -
            have "real_of_rat 0 \<le> real_of_rat p" using r1 rp by simp
            then show ?thesis by (simp add: of_rat_less_eq)
          qed
          have ps: "real_of_rat p < s" using r2 rp by simp
          have pq: "p \<le> q"
          proof -
            have "real_of_rat p < real_of_rat q" using ps sq by simp
            then show ?thesis by (simp add: of_rat_less less_imp_le)
          qed
          have gp: "qvp_goodupto C p w" by (rule qvp_goodupto_mono[OF gq pq])
          have "qvpc C w s p = qvp w (real_of_rat p)"
            using p0 ps gp by (intro qvpc_keep) auto
          then have ple: "qvp w (real_of_rat p) \<le> qvsa C w s"
            using qvsa_upper[OF C, of w s p] by simp
          have gap: "qvp w (real_of_rat q) - qvp w (real_of_rat p)
              \<le> C * (real_of_rat q - real_of_rat p)"
            using gq p0 pq unfolding qvp_goodupto_def by blast
          have "real_of_rat q - real_of_rat p \<le> t - s + d"
            using qt r1 rp by simp
          then have "C * (real_of_rat q - real_of_rat p) \<le> C * (t - s + d)"
            using C by (simp add: mult_left_mono)
          also have "C * (t - s + d) = C * (t - s) + C * d" by (simp add: algebra_simps)
          finally have g2: "C * (real_of_rat q - real_of_rat p)
              \<le> C * (t - s) + C * d" .
          have "C * d \<le> e"
          proof -
            have "C * d = C * e / (C + 1)" by (simp add: d_def)
            also have "\<dots> \<le> e" using C e by (simp add: pos_divide_le_eq field_simps)
            finally show ?thesis .
          qed
          with g2 gap ple show ?thesis by simp
        qed
        show ?thesis by (rule field_le_epsilon) (use eps in blast)
      qed
    qed
    show ?thesis using v main by simp
  qed
  have "qvsa C w t = (SUP q. qvpc C w t q)" by (simp add: qvsa_def)
  also have "\<dots> \<le> qvsa C w s + C * (t - s)"
    by (rule cSUP_least[OF UNIV_not_empty]) (use step in blast)
  finally show ?thesis .
qed

lemma qvsa_continuous:
  assumes C: "0 \<le> C"
  shows "continuous_on {0..} (qvsa C w)"
proof -
  have "C-lipschitz_on {0..} (qvsa C w)"
  proof (rule lipschitz_onI[OF _ C])
    fix a b :: real assume ab: "a \<in> {0..}" "b \<in> {0..}"
    show "dist (qvsa C w a) (qvsa C w b) \<le> C * dist a b"
    proof (cases "a \<le> b")
      case True
      with qvsa_lip[OF C, of a b w] qvsa_mono[OF C, of a b w] show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    next
      case False
      with qvsa_lip[OF C, of b a w] qvsa_mono[OF C, of b a w] show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    qed
  qed
  then show ?thesis by (rule lipschitz_on_continuous_on)
qed

text \<open>On the good event no value is discarded, so the running cut agrees with
  the left-regularisation \<open>qvps\<close>.\<close>

lemma qvsa_eq_qvps:
  assumes g: "qvp_good C w" and C: "0 \<le> C"
  shows "qvsa C w t = qvps w t"
proof (cases "0 < t")
  case False
  then have t: "t \<le> 0" by simp
  show ?thesis using C t by simp
next
  case True
  define A where "A = {q :: rat. 0 \<le> q \<and> real_of_rat q < t}"
  define f where "f = (\<lambda>q :: rat. qvp w (real_of_rat q))"
  have S: "qvps w t = Sup (f ` A)"
    unfolding f_def A_def by (rule qvps_as_Sup[OF g C True])
  have zA: "(0 :: rat) \<in> A" using True by (simp add: A_def)
  have ne: "f ` A \<noteq> {}" using zA by blast
  have im: "f ` A \<subseteq> range (qvpc C w t)"
  proof
    fix y assume "y \<in> f ` A"
    then obtain q :: rat where q: "0 \<le> q" "real_of_rat q < t" and y: "y = f q"
      by (auto simp: A_def)
    have "qvpc C w t q = y"
      using q y qvp_good_goodupto[OF g] by (simp add: f_def qvpc_keep)
    then show "y \<in> range (qvpc C w t)" by (metis rangeI)
  qed
  have bd: "bdd_above (range (qvpc C w t))" by (rule qvpc_bdd[OF C])
  have bd2: "bdd_above (f ` A)" by (rule bdd_above_mono[OF bd im])
  have z: "0 \<le> Sup (f ` A)"
  proof -
    have "f 0 \<le> Sup (f ` A)" using zA by (intro cSup_upper bd2) blast
    then show ?thesis by (simp add: f_def)
  qed
  have le1: "Sup (f ` A) \<le> qvsa C w t"
    unfolding qvsa_def by (rule cSup_subset_mono[OF ne bd im])
  have le2: "qvsa C w t \<le> Sup (f ` A)"
    unfolding qvsa_def
  proof (rule cSup_least)
    show "range (qvpc C w t) \<noteq> {}" by simp
    fix y assume "y \<in> range (qvpc C w t)"
    then obtain q :: rat where y: "y = qvpc C w t q" by blast
    show "y \<le> Sup (f ` A)"
    proof (cases "0 \<le> q \<and> real_of_rat q < t \<and> qvp_goodupto C q w")
      case True
      then have "y = f q" using y by (simp add: f_def qvpc_keep)
      moreover have "q \<in> A" using True by (simp add: A_def)
      ultimately show ?thesis by (metis cSup_upper bd2 imageI)
    next
      case False
      then have "y = 0" using y by (simp add: qvpc_drop)
      then show ?thesis using z by simp
    qed
  qed
  show ?thesis using S le1 le2 by simp
qed

text \<open>Measurability, and the point of the whole construction: the value at
  \<open>t\<close> reads the path only at times \<open>< t\<close>, so the hypothesis is the ADAPTED one.\<close>

lemma qvp_goodupto_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real" and N :: "'b measure"
  assumes Y: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> real_of_rat u \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "Measurable.pred N (\<lambda>\<omega>. qvp_goodupto C u (\<lambda>s. Y s \<omega>))"
proof -
  have m: "(\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) (real_of_rat r)) \<in> borel_measurable N"
    if r: "0 \<le> (r :: rat)" and ru: "r \<le> u" for r
  proof (rule qvp_measurable)
    show "0 \<le> real_of_rat r" using r by simp
    fix s assume s: "0 \<le> s" and sr: "s \<le> real_of_rat r"
    have "real_of_rat r \<le> real_of_rat u" using ru by (simp add: of_rat_less_eq)
    then show "Y s \<in> borel_measurable N" using Y[OF s] sr by simp
  qed
  show ?thesis unfolding qvp_goodupto_def
  proof (intro pred_intros_countable)
    fix p q :: rat
    show "Measurable.pred N (\<lambda>\<omega>. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
        0 \<le> qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p) \<and>
        qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"
    proof (cases "0 \<le> p \<and> p \<le> q \<and> q \<le> u")
      case True
      then have p: "0 \<le> p" and pq: "p \<le> q" and qu: "q \<le> u" by auto
      then have q: "0 \<le> q" and pu: "p \<le> u" by auto
      note [measurable] = m[OF p pu] m[OF q qu]
      show ?thesis by measurable
    next
      case False
      then show ?thesis by simp
    qed
  qed
qed

lemma qvpc_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real" and N :: "'b measure"
  assumes Y: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. qvpc C (\<lambda>s. Y s \<omega>) t q) \<in> borel_measurable N"
proof (cases "0 \<le> q \<and> real_of_rat q < t")
  case False
  then have "\<And>w. qvpc C w t q = 0" by (intro qvpc_drop) auto
  then show ?thesis by simp
next
  case True
  then have q0: "0 \<le> q" and qt: "real_of_rat q < t" by auto
  have Y': "Y s \<in> borel_measurable N" if s: "0 \<le> s" and sq: "s \<le> real_of_rat q" for s
    using Y[OF s] sq qt by simp
  have g [measurable]: "Measurable.pred N (\<lambda>\<omega>. qvp_goodupto C q (\<lambda>s. Y s \<omega>))"
    by (rule qvp_goodupto_measurable) (use Y' in blast)
  have p [measurable]: "(\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) (real_of_rat q)) \<in> borel_measurable N"
    by (rule qvp_measurable) (use q0 Y' in auto)
  have eq: "(\<lambda>\<omega>. qvpc C (\<lambda>s. Y s \<omega>) t q)
      = (\<lambda>\<omega>. if qvp_goodupto C q (\<lambda>s. Y s \<omega>)
             then qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) else 0)"
    using True by (auto simp: qvpc_def)
  show ?thesis unfolding eq by measurable
qed

lemma qvsa_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real" and N :: "'b measure"
  assumes Y: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> Y s \<in> borel_measurable N" and C: "0 \<le> C"
  shows "(\<lambda>\<omega>. qvsa C (\<lambda>s. Y s \<omega>) t) \<in> borel_measurable N"
  unfolding qvsa_def
proof (rule borel_measurable_cSUP)
  show "countable (UNIV :: rat set)" by simp
  show "(\<lambda>\<omega>. qvpc C (\<lambda>s. Y s \<omega>) t q) \<in> borel_measurable N" if "q \<in> (UNIV :: rat set)"
    for q by (rule qvpc_measurable) (use Y in blast)
  show "bdd_above ((\<lambda>q. qvpc C (\<lambda>s. Y s \<omega>) t q) ` UNIV)" if "\<omega> \<in> space N" for \<omega>
    using qvpc_bdd[OF C, of "\<lambda>s. Y s \<omega>" t] by simp
qed

text \<open>The functional reads the path only on \<open>{0..}\<close>, so restricting a path
  there does not change it --- which is what the pushforwards need, since a
  point of the path space IS a restricted function.\<close>

lemma qvp_goodupto_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> w s = w' s"
  shows "qvp_goodupto C u w = qvp_goodupto C u w'"
proof -
  have e: "qvp w (real_of_rat r) = qvp w' (real_of_rat r)" if "0 \<le> (r :: rat)" for r
    by (rule qvp_cong) (use eq that in auto)
  have "(\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
      0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat p) \<and>
      qvp w (real_of_rat q) - qvp w (real_of_rat p)
        \<le> C * (real_of_rat q - real_of_rat p))
    \<longleftrightarrow> (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
      0 \<le> qvp w' (real_of_rat q) - qvp w' (real_of_rat p) \<and>
      qvp w' (real_of_rat q) - qvp w' (real_of_rat p)
        \<le> C * (real_of_rat q - real_of_rat p))"
  proof (intro iff_allI)
    fix p q :: rat
    show "(0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
        0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat p) \<and>
        qvp w (real_of_rat q) - qvp w (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))
      \<longleftrightarrow> (0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> q \<le> u \<longrightarrow>
        0 \<le> qvp w' (real_of_rat q) - qvp w' (real_of_rat p) \<and>
        qvp w' (real_of_rat q) - qvp w' (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"
    proof (cases "0 \<le> p \<and> p \<le> q")
      case True
      then have "0 \<le> p" and "0 \<le> q" by auto
      then show ?thesis using e[of p] e[of q] by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  then show ?thesis unfolding qvp_goodupto_def by simp
qed

lemma qvsa_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> w s = w' s"
  shows "qvsa C w t = qvsa C w' t"
proof -
  have "qvpc C w t q = qvpc C w' t q" for q
  proof (cases "0 \<le> q")
    case True
    then have e1: "qvp w (real_of_rat q) = qvp w' (real_of_rat q)"
      by (intro qvp_cong) (use eq in auto)
    have e2: "qvp_goodupto C q w = qvp_goodupto C q w'"
      by (rule qvp_goodupto_cong[OF eq])
    show ?thesis unfolding qvpc_def by (simp add: e1 e2)
  next
    case False
    then show ?thesis unfolding qvpc_def by simp
  qed
  then show ?thesis unfolding qvsa_def by simp
qed

subsection \<open>The adapted matrix functional\<close>

text \<open>Polarisation of \<open>qvsa\<close>, exactly as \<open>qvmat\<close> polarises \<open>qvps\<close>.  It is
  continuous in \<open>t\<close> for EVERY path, adapted, vanishes at \<open>0\<close>, and agrees with
  \<open>qvmat\<close> whenever the polarised scalars are good.\<close>

definition qvmata ::
  "real \<Rightarrow> (real \<Rightarrow> real^'n::finite) \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where
  "qvmata C w t = (\<chi> i. \<chi> j. (qvsa C (\<lambda>s. w s $ i + w s $ j) t
                              - qvsa C (\<lambda>s. w s $ i + (- 1) * (w s $ j)) t) / 4)"

lemma qvmata_continuous:
  assumes C: "0 \<le> C"
  shows "continuous_on {0..} (qvmata C w)"
  unfolding qvmata_def
  by (intro continuous_on_vec_lambda continuous_intros qvsa_continuous[OF C]) simp

lemma qvmata_zero [simp]:
  assumes C: "0 \<le> C" and t: "t \<le> 0"
  shows "qvmata C w t = 0"
  unfolding qvmata_def using C t by (simp add: vec_eq_iff)

lemma qvmata_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real^'n::finite" and N :: "'b measure"
  assumes Y: "\<And>s i. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> (\<lambda>\<omega>. Y s \<omega> $ i) \<in> borel_measurable N"
    and C: "0 \<le> C"
  shows "(\<lambda>\<omega>. qvmata C (\<lambda>s. Y s \<omega>) t) \<in> borel_measurable N"
proof (rule measurable_mat_entries)
  fix i j :: 'n
  have p: "(\<lambda>\<omega>. qvsa C (\<lambda>s. Y s \<omega> $ i + c * (Y s \<omega> $ j)) t) \<in> borel_measurable N"
    for c by (rule qvsa_measurable[OF _ C]) (use Y in simp)
  have "(\<lambda>\<omega>. qvmata C (\<lambda>s. Y s \<omega>) t $ i $ j)
      = (\<lambda>\<omega>. (qvsa C (\<lambda>s. Y s \<omega> $ i + 1 * (Y s \<omega> $ j)) t
              - qvsa C (\<lambda>s. Y s \<omega> $ i + (- 1) * (Y s \<omega> $ j)) t) / 4)"
    by (simp add: qvmata_def)
  then show "(\<lambda>\<omega>. qvmata C (\<lambda>s. Y s \<omega>) t $ i $ j) \<in> borel_measurable N"
    using p[of 1] p[of "- 1"] by simp
qed

lemma qvmata_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> w s = w' s"
  shows "qvmata C w t = qvmata C w' t"
proof -
  have p: "qvsa C (\<lambda>s. w s $ i + w s $ j) t = qvsa C (\<lambda>s. w' s $ i + w' s $ j) t"
    for i j by (rule qvsa_cong) (use eq in simp)
  have m: "qvsa C (\<lambda>s. w s $ i - w s $ j) t = qvsa C (\<lambda>s. w' s $ i - w' s $ j) t"
    for i j by (rule qvsa_cong) (use eq in simp)
  show ?thesis unfolding qvmata_def by (simp add: vec_eq_iff p m)
qed

lemma qvmata_eq_qvmat:
  assumes gp: "\<And>i j. qvp_good C (\<lambda>s. w s $ i + w s $ j)"
    and gm: "\<And>i j. qvp_good C (\<lambda>s. w s $ i - w s $ j)"
    and C: "0 \<le> C"
  shows "qvmata C w t = qvmat w t"
  unfolding qvmata_def qvmat_def
  by (simp add: qvsa_eq_qvps[OF gp C] qvsa_eq_qvps[OF gm C])


(*<*)
end
(*>*)
