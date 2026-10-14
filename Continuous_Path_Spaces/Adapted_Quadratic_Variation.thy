section \<open>An adapted, everywhere-continuous quadratic variation\<close>

(*<*)
theory Adapted_Quadratic_Variation
  imports Pathwise_Quadratic_Variation "Continuous_Time_Martingales.Stopped_Localization"
begin

(*>*)

text \<open>
  \<open>qvp\<close> is a Borel path functional, but it is neither adapted nor continuous
  everywhere.  This theory repairs both: \<open>qvpc\<close> is a version continuous in
  the time argument, \<open>qvsa\<close> is adapted -- it reads the path only up to the
  current time -- and \<open>qvmata\<close> assembles the matrix-valued form.  The good
  events \<open>qvp_good\<close> and \<open>qvp_goodupto\<close> are where the repair is exact.

  The construction is consumed by the relative-arbitrage development it was
  extracted from, and is not otherwise specific to it.
\<close>

subsection \<open>The functional reads the path only up to the current time\<close>

text \<open>
  The scalar theory assumes \<open>X\<close> uniformly bounded, because Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close>
  (\<open>fourth_moment_bound_bounded\<close>) does.  A member of the class is not bounded,
  so the identification has to be localised --- which is what
  @{theory Continuous_Time_Martingales.Stopped_Localization} was built for: stopping an
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

subsection \<open>The good event has full measure\<close>

text \<open>The cut-down functional is only useful if the cut discards nothing: under
  the hypotheses of the scalar theory the rational-time data of \<open>qvp\<close> IS the compensator,
  so it is nondecreasing and Lipschitz almost surely.  Stated inside the locale,
  where \<open>qvp_eq_A_rat\<close> identifies \<open>qvp\<close> at all rational times on one event.\<close>

lemma (in bounded_martingale_compensator) qvp_good_ae:
  "AE \<omega> in M. qvp_good C (\<lambda>s. X s \<omega>)"
proof -
  from qvp_eq_A_rat A0 Arate show ?thesis
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
proof (rule rate_continuous_on[OF C], intro allI impI conjI)
  fix u v :: real assume "0 \<le> u" "u \<le> v"
  then show "0 \<le> qvsa C w v - qvsa C w u" "qvsa C w v - qvsa C w u \<le> C * (v - u)"
    using qvsa_mono[OF C, of u v w] qvsa_lip[OF C, of u v w] by simp_all
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

text \<open>So on the good event \<open>qvps\<close> itself is nondecreasing, \<open>C\<close>-Lipschitz and
  continuous on \<open>{0..}\<close>.\<close>

lemma qvps_mono_lip:
  assumes g: "qvp_good C w" and C: "0 \<le> C" and s: "0 \<le> s" and st: "s \<le> t"
  shows "0 \<le> qvps w t - qvps w s \<and> qvps w t - qvps w s \<le> C * (t - s)"
  using qvsa_mono[OF C st, of w] qvsa_lip[OF C st, of w]
  by (simp add: qvsa_eq_qvps[OF g C])

lemma qvps_continuous:
  assumes g: "qvp_good C w" and C: "0 \<le> C"
  shows "continuous_on {0..} (qvps w)"
proof -
  have "qvsa C w = qvps w" by (rule ext) (rule qvsa_eq_qvps[OF g C])
  then show ?thesis using qvsa_continuous[OF C, of w] by simp
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


subsection \<open>The scalar identification without the boundedness hypothesis\<close>

text \<open>Stopping at the exit time from a ball of radius \<open>r\<close> makes the process
  bounded, which is the one hypothesis of the scalar theory that a class member fails.
  Everything else survives stopping: the martingale property by
  \<open>stopped_martingale_L2\<close>, the compensator relation by
  \<open>stopped_compensated_square\<close>, and the rate because \<open>min u tau \<le> min v tau\<close> with
  \<open>min v tau - min u tau \<le> v - u\<close>.\<close>

lemma qvps_eq_A_stopped:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and T0: "0 < T" and r0: "0 < r"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega>\<bar> < r"
  defines "tau \<equiv> etime T {y :: real. r \<le> norm y} X"
  shows "AE \<omega> in M. qvp_good C (\<lambda>s. X (min s (tau \<omega>)) \<omega>)
           \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
                qvps (\<lambda>s. X (min s (tau \<omega>)) \<omega>) t = A (min t (tau \<omega>)) \<omega>)"proof -
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have Tnn: "0 \<le> T" using T0 by simp
  have Acl: "closed {y :: real. r \<le> norm y}"
    by (intro closed_Collect_le continuous_intros)
  have Ane: "{y :: real. r \<le> norm y} \<noteq> {}" using r0 by (auto intro!: exI[of _ r])
  have contT: "continuous_on {0..T} (\<lambda>s. X s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF contX[OF w]]) auto

  text \<open>The exit time is a stopping time.\<close>
  interpret CA: cont_adapted_process M F X T
  proof (intro cont_adapted_process.intro cont_adapted_process_axioms.intro)
    show "adapted_process M F 0 X" by (rule MX.adapted_process_axioms)
    show "0 \<le> T" by (rule Tnn)
    show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>s. X s \<omega>)" by (rule contT)
  qed
  have tau_stop: "{\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)" if s: "0 \<le> s" for s
    unfolding tau_def by (rule CA.etime_stopping_time[OF Acl Ane s])
  have tau_nn: "0 \<le> tau \<omega>" for \<omega> unfolding tau_def by (rule etime_nonneg[OF Tnn])
  have tau_le: "tau \<omega> \<le> T" for \<omega> unfolding tau_def by (rule etime_le_T[OF Tnn])

  text \<open>The stopped process is bounded by the radius.\<close>
  have bndS: "\<bar>X (min v (tau \<omega>)) \<omega>\<bar> \<le> r" if w: "\<omega> \<in> space M" and v: "0 \<le> v" for v \<omega>
  proof -
    have s1: "0 \<le> min v (tau \<omega>)" using v tau_nn[of \<omega>] by simp
    have s2: "min v (tau \<omega>) \<le> etime T {y :: real. r \<le> norm y} X \<omega>"
      unfolding tau_def[symmetric] by simp
    have "X (min v (tau \<omega>)) \<omega> \<in> cball 0 r"
      by (rule etime_stays_in_cball[where T = T and r = r and X = X and \<omega> = \<omega>
            and s = "min v (tau \<omega>)"])
         (use X0[OF w] contT[OF w] s1 s2 r0 Tnn in simp_all)
    then show ?thesis by (simp add: dist_norm)
  qed

  text \<open>The stopped compensator keeps the rate.\<close>
  have rateS: "0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
      \<and> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega> \<le> C * (v - u)"
    if w: "\<omega> \<in> space M" and u: "0 \<le> u" and uv: "u \<le> v" for u v \<omega>
  proof -
    have m1: "0 \<le> min u (tau \<omega>)" using u tau_nn[of \<omega>] by simp
    have m2: "min u (tau \<omega>) \<le> min v (tau \<omega>)" using uv by simp
    have le: "min v (tau \<omega>) - min u (tau \<omega>) \<le> v - u" using uv by simp
    from A_rate[OF w, rule_format, OF m1 m2] have
      nn: "0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>"
      and ub: "A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
                 \<le> C * (min v (tau \<omega>) - min u (tau \<omega>))" by simp_all
    have "C * (min v (tau \<omega>) - min u (tau \<omega>)) \<le> C * (v - u)"
      using C0 le by (rule mult_left_mono[rotated])
    with nn ub show ?thesis by simp
  qed

  text \<open>The stopped pair satisfies the hypotheses of the scalar theory.\<close>
  interpret S: bounded_martingale_compensator M F
      "\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>" "\<lambda>v \<omega>. A (min v (tau \<omega>)) \<omega>" C r
  proof (rule bounded_martingale_compensator.intro)
    show "prob_space M" by (rule P)
    show "0 \<le> C" by (rule C0)
    show "0 \<le> r" using r0 by simp
    show "martingale M F 0 (\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>)"
      by (rule stopped_martingale_L2[OF P mgX sqX contX tau_nn tau_stop])
    show "martingale M F 0 (\<lambda>v \<omega>. (X (min v (tau \<omega>)) \<omega>)\<^sup>2 - A (min v (tau \<omega>)) \<omega>)"
      by (rule stopped_compensated_square
            [OF P mgX sqX contX mgZ A0 A_rate C0 tau_nn tau_stop])
    show "AE \<omega> in M. \<bar>X (min v (tau \<omega>)) \<omega>\<bar> \<le> r" if "0 \<le> v" for v
      using bndS[OF _ that] by (intro AE_I2) blast
    show "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
        \<and> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega> \<le> C * (v - u)"
      using rateS by (intro AE_I2) blast
    show "AE \<omega> in M. A (min 0 (tau \<omega>)) \<omega> = 0"
      using A0 tau_nn by (intro AE_I2) simp
    show "AE \<omega> in M. continuous_on {0..} (\<lambda>p. X (min p (tau \<omega>)) \<omega>)"
    proof (intro AE_I2)
      fix \<omega> assume w: "\<omega> \<in> space M"
      have "continuous_on {0..} (\<lambda>p. min p (tau \<omega>))" by (intro continuous_intros)
      moreover have "(\<lambda>p. min p (tau \<omega>)) ` {0..} \<subseteq> {0..}"
        using tau_nn[of \<omega>] by auto
      ultimately show "continuous_on {0..} (\<lambda>p. X (min p (tau \<omega>)) \<omega>)"
        by (rule continuous_on_compose2[OF contX[OF w], unfolded o_def])
    qed
  qed
  show ?thesis using S.qvp_good_ae S.qvps_eq_A by eventually_elim blast
qed

text \<open>Letting the radius and the horizon grow together.  For a fixed time the
  path is bounded on \<open>{0..t}\<close> by continuity, so some level is never reached
  before \<open>t\<close>; there the stopped process agrees with \<open>X\<close> and the stopped
  compensator with \<open>A\<close>, and the congruence carries the identification across.
  The levels are indexed by naturals, so one countable intersection serves all
  of them.\<close>

theorem qvps_eq_A_localised:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and B0: "0 \<le> B" and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega>\<bar> \<le> B"
  shows "AE \<omega> in M. qvp_good C (\<lambda>s. X s \<omega>)
           \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega>) t = A t \<omega>)"
proof -
  define lev where "lev = (\<lambda>R::nat. B + real (Suc R))"
  define tau where
    "tau = (\<lambda>R::nat. etime (real (Suc R)) {y :: real. lev R \<le> norm y} X)"
  have lev_pos: "0 < lev R" for R using B0 by (simp add: lev_def)
  have T_pos: "(0::real) < real (Suc R)" for R by simp
  have X0lt: "\<bar>X 0 \<omega>\<bar> < lev R" if "\<omega> \<in> space M" for \<omega> R
    using X0[OF that] by (simp add: lev_def)
  have step: "AE \<omega> in M. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>)" for R
    unfolding tau_def
    by (rule qvps_eq_A_stopped
          [OF P mgX sqX contX mgZ A0 A_rate C0 T_pos lev_pos X0lt])
  have all: "AE \<omega> in M. \<forall>R::nat. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>)"
    by (subst AE_all_countable) (rule allI, rule step)
  have sp: "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  from all sp show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have key: "\<And>R t. 0 \<le> t \<Longrightarrow>
        qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>"
      and keyg: "\<And>R. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)"
      and w: "\<omega> \<in> space M" by blast+

    text \<open>Some level is not reached before a given time, because the path is
      bounded on the compact interval.\<close>
    have esc: "\<exists>n :: nat. t < tau n \<omega>" if t: "0 \<le> t" for t
    proof -
      have contt: "continuous_on {0..t} (\<lambda>s. X s \<omega>)"
        by (rule continuous_on_subset[OF contX[OF w]]) auto
      have "compact ((\<lambda>s. X s \<omega>) ` {0..t})"
        by (rule compact_continuous_image[OF contt compact_Icc])
      then have "bounded ((\<lambda>s. X s \<omega>) ` {0..t})" by (rule compact_imp_bounded)
      then obtain Bd where Bd: "\<And>y. y \<in> (\<lambda>s. X s \<omega>) ` {0..t} \<Longrightarrow> norm y \<le> Bd"
        by (auto simp: bounded_iff)
      obtain n :: nat where n: "max t Bd < real n" using reals_Archimedean2 by blast
      have nt: "t < real (Suc n)" using n by simp
      have nB: "Bd < lev n" using n B0 by (simp add: lev_def)
      have "t < tau n \<omega>"
      proof (rule ccontr)
        assume "\<not> t < tau n \<omega>"
        then have le: "tau n \<omega> \<le> t" by simp
        have "tau n \<omega> \<le> t \<longleftrightarrow> (\<exists>s\<in>{0..t}. X s \<omega> \<in> {y :: real. lev n \<le> norm y})"
          unfolding tau_def
        proof (rule etime_le_iff[OF _ t nt])
          show "(0::real) \<le> real (Suc n)" by simp
          show "closed {y :: real. lev n \<le> norm y}"
            by (intro closed_Collect_le continuous_intros)
          show "continuous_on {0..real (Suc n)} (\<lambda>s. X s \<omega>)"
            by (rule continuous_on_subset[OF contX[OF w]]) auto
        qed
        with le obtain s where s: "s \<in> {0..t}" and hit: "lev n \<le> \<bar>X s \<omega>\<bar>" by auto
        have "\<bar>X s \<omega>\<bar> \<le> Bd" using Bd[of "X s \<omega>"] s by auto
        with hit nB show False by simp
      qed
      then show ?thesis by blast
    qed

    show ?case
    proof
      show "\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega>) t = A t \<omega>"
      proof (intro allI impI)
        fix t :: real assume t: "0 \<le> t"
        obtain n :: nat where taut: "t < tau n \<omega>" using esc[OF t] by blast
        have "qvps (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) t = qvps (\<lambda>s. X s \<omega>) t"
          by (rule qvps_cong) (use taut in simp)
        moreover have "A (min t (tau n \<omega>)) \<omega> = A t \<omega>" using taut by simp
        ultimately show "qvps (\<lambda>s. X s \<omega>) t = A t \<omega>" using key[OF t, of n] by simp
      qed
    next
      show "qvp_good C (\<lambda>s. X s \<omega>)"
        unfolding qvp_good_def
      proof (intro conjI)
        show "qvp (\<lambda>s. X s \<omega>) 0 = 0" by simp
        show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
            0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
            \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
                \<le> C * (real_of_rat q - real_of_rat p)"
        proof (intro allI impI)
        fix p q :: rat assume p: "0 \<le> p" and pq: "p \<le> q"
        then have q: "0 \<le> q" by simp
        have pq': "real_of_rat p \<le> real_of_rat q" using pq by (simp add: of_rat_less_eq)
        have q': "(0::real) \<le> real_of_rat q" using q by simp
        obtain n :: nat where taut: "real_of_rat q < tau n \<omega>" using esc[OF q'] by blast
        have ep: "qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
            = qvp (\<lambda>s. X s \<omega>) (real_of_rat p)"
          by (rule qvp_cong) (use taut pq' p in auto)
        have eq: "qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
            = qvp (\<lambda>s. X s \<omega>) (real_of_rat q)"
          by (rule qvp_cong) (use taut q in auto)
        from keyg[of n] p pq have
          "0 \<le> qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
                 - qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
           \<and> qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
                 - qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
               \<le> C * (real_of_rat q - real_of_rat p)"
          unfolding qvp_good_def by blast
        then show "0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
            \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
                \<le> C * (real_of_rat q - real_of_rat p)"
          using ep eq by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>The matrix identification without the boundedness hypothesis\<close>

text \<open>The polarisation, run through the localised scalar theorem.  The
  hypotheses are pointwise on \<open>space M\<close> rather than almost everywhere, which is
  what the stopping arguments need.  Almost-sure hypotheses reach that form by
  restricting the probability space to a full-measure event, which changes
  neither the laws nor the martingale property (the \<open>*_restrict_full\<close> facts
  of @{theory Continuous_Time_Martingales.Martingale_Transfer}).\<close>

theorem qvmat_eq_A_localised:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" and A :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
  assumes P: "prob_space M"
    and Xcomp: "\<And>i. martingale M F (0::real) (\<lambda>v \<omega>. X v \<omega> $ i)"
    and XAcomp: "\<And>i j. martingale M F (0::real)
                    (\<lambda>v \<omega>. X v \<omega> $ i * X v \<omega> $ j - A v \<omega> $ i $ j)"
    and contX: "\<And>\<omega> i. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega> $ i)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and Apsd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                  (\<forall>y. 0 \<le> y \<bullet> ((A q \<omega> - A p \<omega>) *v y))"
    and Arate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                  \<bar>A q \<omega> $ i $ j - A p \<omega> $ i $ j\<bar> \<le> C * (q - p)"
    and C0: "0 \<le> C"
    and B0: "0 \<le> B" and X0: "\<And>\<omega> i. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega> $ i\<bar> \<le> B"
  shows "AE \<omega> in M.
     (\<forall>i j. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
          \<and> qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j))
     \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
          qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2))"
proof -
  interpret P: prob_space M by (rule P)
  have pol: "AE \<omega> in M. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + c * (X s \<omega> $ j))
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X s \<omega> $ i + c * (X s \<omega> $ j)) t
             = A t \<omega> $ i $ i + c * (A t \<omega> $ i $ j + A t \<omega> $ j $ i)
               + c\<^sup>2 * (A t \<omega> $ j $ j))"
    if c: "\<bar>c\<bar> \<le> 1" for c i j
  proof -
    define Y where "Y = (\<lambda>v \<omega>. X v \<omega> $ i + c * (X v \<omega> $ j))"
    define G where "G = (\<lambda>v \<omega>. A v \<omega> $ i $ i
        + c * (A v \<omega> $ i $ j + A v \<omega> $ j $ i) + c\<^sup>2 * (A v \<omega> $ j $ j))"
    have mgY: "martingale M F 0 Y"
      unfolding Y_def by (rule polarised_martingale(1)[OF Xcomp XAcomp])
    have mgZ: "martingale M F 0 (\<lambda>v \<omega>. (Y v \<omega>)\<^sup>2 - G v \<omega>)"
      unfolding Y_def G_def by (rule polarised_martingale(2)[OF Xcomp XAcomp])
    have Grate: "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> G v \<omega> - G u \<omega> \<and> G v \<omega> - G u \<omega> \<le> (4 * C) * (v - u)"
      if w: "\<omega> \<in> space M" for \<omega>
      unfolding G_def by (rule polarised_rate[OF c C0 Apsd[OF w] Arate[OF w]])
    have G0: "G 0 \<omega> = 0" if w: "\<omega> \<in> space M" for \<omega>
      unfolding G_def using A0[OF w] by simp
    have contY: "continuous_on {0..} (\<lambda>s. Y s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
      unfolding Y_def
      by (intro continuous_on_add continuous_on_mult_left contX[OF w])
    have Y0: "\<bar>Y 0 \<omega>\<bar> \<le> 2 * B" if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have "\<bar>Y 0 \<omega>\<bar> \<le> \<bar>X 0 \<omega> $ i\<bar> + \<bar>c * (X 0 \<omega> $ j)\<bar>"
        unfolding Y_def by (rule abs_triangle_ineq)
      also have "\<dots> = \<bar>X 0 \<omega> $ i\<bar> + \<bar>c\<bar> * \<bar>X 0 \<omega> $ j\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> B + 1 * B"
        using X0[OF w] c B0 by (intro add_mono mult_mono) auto
      finally show ?thesis by simp
    qed
    have "AE \<omega> in M. qvp_good (4 * C) (\<lambda>s. Y s \<omega>)
        \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. Y s \<omega>) t = G t \<omega>)"
      by (rule qvps_eq_A_localised[OF P mgY
            compensator_sq_integrable(2)[OF P mgY mgZ G0 Grate] contY mgZ G0 Grate _ _ Y0])
         (use C0 B0 in auto)
    then show ?thesis unfolding Y_def G_def .
  qed
  have c1: "\<bar>(1::real)\<bar> \<le> 1" by simp
  have cm1: "\<bar>(- 1::real)\<bar> \<le> 1" by simp
  have all1: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set).
      qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
           = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j)"
    by (intro AE_finite_allI; use pol[OF c1] in simp)
  have all2: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set).
      qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
           = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j)"
    by (intro AE_finite_allI; use pol[OF cm1] in simp)
  from all1 all2 show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    have e1: "qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
      if "0 \<le> t" for i j t using elim(1) that by blast
    have e2: "qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
      if "0 \<le> t" for i j t using elim(2) that by blast
    show ?case
    proof
      show "\<forall>i j. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
          \<and> qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j)"
        using elim(1) elim(2) by blast
    next
      show "\<forall>t. 0 \<le> t \<longrightarrow>
          qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
      proof (intro allI impI)
        fix t :: real assume t: "0 \<le> t"
        have ent: "qvmat (\<lambda>s. X s \<omega>) t $ i $ j = (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2"
          for i j by (simp add: qvmat_def e1[OF t] e2[OF t])
        show "qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
          by (simp add: vec_eq_iff ent)
      qed
    qed
  qed
qed

(*<*)
end
(*>*)
