(*
  Title:   Threshold_Chain.thy
  Content: Every threshold set contains threshold subsets of all smaller
           sizes.  This is the missing ingredient for Eq. (3.5): it says
           that the ordered eigenvalues lambda_(1), ..., lambda_(m) are
           exactly the S-eigenvalues of a threshold set S of size m, listed
           in decreasing order.

  Recall (Eigenvalues.thy) that T is a THRESHOLD set of B when every value
  inside dominates every value outside; threshold_remove_min says deleting a
  minimal element of a threshold set leaves a threshold set.  Iterating that
  deletion produces the whole descending chain.

  Three Isabelle notes, all learned the hard way here.  Each of the first two
  produced a NON-TERMINATING proof, invisible to `isabelle build` (which
  reports nothing at all until it finishes) but pinpointed by PIDE in
  milliseconds, so develop this file under PIDE.
  * The shrinking step is stated as an EXISTENTIAL, not with `obtains`.  An
    `obtains` rule with three conclusions, one of them a \<And>-statement, makes
    `obtain ... by metis` fall back on metis (full_types) and diverge.
  * But an existential is NOT enough on its own: discharging the resulting
    `obtain` with `blast` also diverges here, because the induction
    hypothesis and all of `Suc.prems` are in scope and `blast` searches
    rather than just eliminating.  Every existential below is therefore
    introduced with `rule exI` and eliminated with `rule exE`, and the
    conjuncts are projected with small `simp` steps.
  * `threshold_remove_min` must be instantiated explicitly (lam, T, B, w):
    with those schematic, `OF` reports "multiple unifiers".
*)

theory Threshold_Chain
  imports Eigenvalue_Continuity
begin

text \<open>The import is \<open>Eigenvalue_Continuity\<close> rather than \<open>Eigenvalues\<close> so that
  the whole development forms a single chain
  \<open>Eigenvalues \<rightarrow> Eigenvalue_Continuity \<rightarrow> Threshold_Chain \<rightarrow> Operator_Continuity
   \<rightarrow> Poincare_Separation\<close>,
  making the Lipschitz facts (\<open>entrysum\<close>, \<open>kyfan_lipschitz\<close>,
  \<open>eigval_lipschitz\<close>) available downstream.  Nothing in this theory uses
  them.\<close>

lemma threshold_shrink_one:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finS: "finite S" and Sne: "S \<noteq> {}"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> lam v \<le> lam u"
  shows "\<exists>T. T \<subseteq> S \<and> card T = card S - 1
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof -
  obtain w where w: "w \<in> S"
    and wmin: "\<And>u. u \<in> S \<Longrightarrow> lam w \<le> lam u"
    using finite_arg_min_on[where f = lam, OF finS Sne] by metis
  have sub: "S - {w} \<subseteq> S"
    by blast
  have cardw: "card (S - {w}) = card S - 1"
    using finS w by simp
  have th: "\<forall>u \<in> S - {w}. \<forall>v \<in> B - (S - {w}). lam v \<le> lam u"
  proof (intro ballI)
    fix u v assume uv: "u \<in> S - {w}" "v \<in> B - (S - {w})"
    show "lam v \<le> lam u"
      by (rule threshold_remove_min[where lam = lam and T = S and B = B and w = w,
            OF thresh wmin uv(1) uv(2)])
  qed
  show ?thesis
    by (rule exI[of _ "S - {w}"]) (intro conjI sub cardw th)
qed

text \<open>The descending chain, by induction on \<open>n = card S\<close>, where the measure
  decreases visibly.  The step splits on whether \<open>j\<close> is already \<open>card S\<close>.\<close>

lemma threshold_chain_aux:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
  shows "\<And>S j. card S = n \<Longrightarrow> S \<subseteq> B
     \<Longrightarrow> (\<forall>u \<in> S. \<forall>v \<in> B - S. lam v \<le> lam u) \<Longrightarrow> j \<le> n
     \<Longrightarrow> \<exists>T. T \<subseteq> S \<and> card T = j
             \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof (induction n)
  case 0
  then have j0: "j = 0" by simp
  show ?case
    by (rule exI[of _ "{}"]) (simp add: j0)
next
  case (Suc n)
  have finS: "finite S"
    using Suc.prems(2) finB by (rule finite_subset)
  show ?case
  proof (cases "j = Suc n")
    case True
    have c: "card S = j"
      using Suc.prems(1) True by simp
    show ?thesis
      by (rule exI[of _ S]) (intro conjI subset_refl c Suc.prems(3))
  next
    case False
    then have jn: "j \<le> n"
      using Suc.prems(4) by simp
    have Sne: "S \<noteq> {}"
      using Suc.prems(1) by auto
    have thr: "lam v \<le> lam u" if "u \<in> S" "v \<in> B - S" for u v
      using Suc.prems(3) that by blast
    have ex1: "\<exists>T. T \<subseteq> S \<and> card T = card S - 1
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      by (rule threshold_shrink_one[OF finS Sne thr])
    obtain S' where S'P: "S' \<subseteq> S \<and> card S' = card S - 1
            \<and> (\<forall>u \<in> S'. \<forall>v \<in> B - S'. lam v \<le> lam u)"
      using ex1 by (rule exE)
    have S'sub: "S' \<subseteq> S"
      using S'P by simp
    have S'card: "card S' = n"
      using S'P Suc.prems(1) by simp
    have S'th: "\<forall>u \<in> S'. \<forall>v \<in> B - S'. lam v \<le> lam u"
      using S'P by simp
    have S'B: "S' \<subseteq> B"
      using S'sub Suc.prems(2) by blast
    have ex2: "\<exists>T. T \<subseteq> S' \<and> card T = j
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      by (rule Suc.IH[OF S'card S'B S'th jn])
    obtain T where TP: "T \<subseteq> S' \<and> card T = j
            \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
      using ex2 by (rule exE)
    have TS: "T \<subseteq> S"
      using TP S'sub by auto
    have Tcard: "card T = j"
      using TP by simp
    have Tth: "\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u"
      using TP by simp
    show ?thesis
      by (rule exI[of _ T]) (intro conjI TS Tcard Tth)
  qed
qed

lemma threshold_chain:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and S: "S \<subseteq> B"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> lam v \<le> lam u"
    and j: "j \<le> card S"
  shows "\<exists>T. T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. lam v \<le> lam u)"
proof -
  have th: "\<forall>u \<in> S. \<forall>v \<in> B - S. lam v \<le> lam u"
  proof (intro ballI)
    fix u v assume "u \<in> S" "v \<in> B - S"
    then show "lam v \<le> lam u" by (rule thresh)
  qed
  show ?thesis
    by (rule threshold_chain_aux[OF finB refl S th j])
qed

text \<open>Specialised to an eigenbasis: for every \<open>j \<le> m\<close> the Ky Fan sum
  \<open>kyfan j a\<close> is already computed inside a threshold set \<open>S\<close> of size \<open>m\<close>,
  which lets \<open>possum m a\<close> be identified with the positive-part sum over
  \<open>S\<close>.\<close>

lemma kyfan_within_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and j: "j \<le> m"
  shows "\<exists>T. T \<subseteq> S \<and> card T = j \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have jc: "j \<le> card S"
    using j S(2) by simp
  have ex: "\<exists>T. T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u))"
    by (rule threshold_chain[where lam = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
          OF finB S(1) thresh jc])
  obtain T where TP: "T \<subseteq> S \<and> card T = j
          \<and> (\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u))"
    using ex by (rule exE)
  have T1: "T \<subseteq> S"
    using TP by simp
  have T2: "card T = j"
    using TP by simp
  have thT: "\<forall>u \<in> T. \<forall>v \<in> B - T. v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using TP by simp
  have TB: "T \<subseteq> B"
    using T1 S(1) by blast
  have thT': "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if "u \<in> T" "v \<in> B - T" for u v
    using thT that by blast
  have kf: "kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig TB T2 thT'])
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T1 T2 kf)
qed

section \<open>The positive-part sum inside a threshold set\<close>

text \<open>The companion of \<open>possum_full_eq_sum_basis\<close>: on a threshold set \<open>S\<close> of
  size \<open>m\<close>, \<open>possum m a\<close> is the sum of the positive eigenvalues occurring in
  \<open>S\<close>, and consequently \<open>kyfan m a - possum m a\<close> is the sum of the
  nonpositive ones.  Those are exactly the two terms of the bracket of
  Eq. (3.5) once \<open>M\<^sub>p\<close> is diagonalised.

  The \<open>\<le>\<close> half uses \<open>kyfan_within_threshold\<close> for each \<open>j \<le> m\<close>; the \<open>\<ge>\<close> half
  observes that the positive part of \<open>S\<close> is again a threshold set of \<open>B\<close>, so
  \<open>kyfan_threshold\<close> evaluates it, and its size is at most \<open>m\<close>.\<close>

lemma possum_within_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "possum m a = (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
proof (rule antisym)
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finS: "finite S"
    using S(1) finB by (rule finite_subset)
  have bound: "\<forall>x \<in> (\<lambda>j. kyfan j a) ` {..m}. x \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
  proof (intro ballI)
    fix x assume "x \<in> (\<lambda>j. kyfan j a) ` {..m}"
    then obtain j where j: "j \<le> m" and x: "x = kyfan j a"
      by auto
    have exj: "\<exists>T. T \<subseteq> S \<and> card T = j \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      by (rule kyfan_within_threshold[OF B sym eig S thresh j])
    obtain T where TP: "T \<subseteq> S \<and> card T = j
            \<and> kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      using exj by (rule exE)
    have T1: "T \<subseteq> S"
      using TP by simp
    have kf: "kyfan j a = (\<Sum>u\<in>T. u \<bullet> (a *v u))"
      using TP by simp
    have "(\<Sum>u\<in>T. u \<bullet> (a *v u)) \<le> (\<Sum>u\<in>T. max (u \<bullet> (a *v u)) 0)"
      by (intro sum_mono) simp
    also have "\<dots> \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
      using finS T1 by (intro sum_mono2) auto
    finally show "x \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
      unfolding x kf .
  qed
  show "possum m a \<le> (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    using bound unfolding possum_def by (subst Max_le_iff) auto
next
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finS: "finite S"
    using S(1) finB by (rule finite_subset)
  define P where "P = {u \<in> S. 0 < u \<bullet> (a *v u)}"
  have Psub: "P \<subseteq> S"
    by (auto simp: P_def)
  have PB: "P \<subseteq> B"
    using Psub S(1) by blast
  have cardP: "card P \<le> m"
    using S(2) card_mono[OF finS Psub] by simp
  text \<open>The positive part of a threshold set is again a threshold set: a
    point outside it is either inside \<open>S\<close> with a nonpositive value, or
    outside \<open>S\<close> and hence dominated already.\<close>
  have threshP: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if u: "u \<in> P" and v: "v \<in> B - P" for u v
  proof -
    have upos: "0 < u \<bullet> (a *v u)"
      using u by (simp add: P_def)
    have uS: "u \<in> S"
      using u by (simp add: P_def)
    show ?thesis
    proof (cases "v \<in> S")
      case True
      then have "v \<bullet> (a *v v) \<le> 0"
        using v by (auto simp: P_def)
      then show ?thesis
        using upos by simp
    next
      case False
      then have "v \<in> B - S"
        using v by blast
      then show ?thesis
        by (rule thresh[OF uS])
    qed
  qed
  have kP: "kyfan (card P) a = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig PB refl threshP])
  have sumP: "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
  proof -
    have split: "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)
        = (\<Sum>u\<in>S - P. max (u \<bullet> (a *v u)) 0) + (\<Sum>u\<in>P. max (u \<bullet> (a *v u)) 0)"
      using Psub finS by (rule sum.subset_diff)
    have out: "(\<Sum>u\<in>S - P. max (u \<bullet> (a *v u)) 0) = 0"
      by (intro sum.neutral ballI) (auto simp: P_def)
    have inn: "(\<Sum>u\<in>P. max (u \<bullet> (a *v u)) 0) = (\<Sum>u\<in>P. u \<bullet> (a *v u))"
      by (intro sum.cong refl) (auto simp: P_def)
    show ?thesis
      using split out inn by simp
  qed
  have "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) = kyfan (card P) a"
    using kP sumP by simp
  also have "\<dots> \<le> possum m a"
    by (rule possum_ge_kyfan[OF cardP])
  finally show "(\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0) \<le> possum m a" .
qed

text \<open>And the negative-part companion, which is the second term of the
  bracket of Eq. (3.5).\<close>

corollary kyfan_minus_possum_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and S: "S \<subseteq> B" "card S = m"
    and thresh: "\<And>u v. u \<in> S \<Longrightarrow> v \<in> B - S \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "kyfan m a - possum m a = (\<Sum>u\<in>S. min (u \<bullet> (a *v u)) 0)"
proof -
  have kS: "kyfan m a = (\<Sum>u\<in>S. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig S thresh])
  have pS: "possum m a = (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    by (rule possum_within_threshold[OF B sym eig S thresh])
  have step: "u \<bullet> (a *v u) - max (u \<bullet> (a *v u)) 0 = min (u \<bullet> (a *v u)) 0" for u
    by (simp add: min_def max_def)
  have "kyfan m a - possum m a
      = (\<Sum>u\<in>S. u \<bullet> (a *v u)) - (\<Sum>u\<in>S. max (u \<bullet> (a *v u)) 0)"
    unfolding kS pS by (rule refl)
  also have "\<dots> = (\<Sum>u\<in>S. u \<bullet> (a *v u) - max (u \<bullet> (a *v u)) 0)"
    by (simp add: sum_subtractf)
  also have "\<dots> = (\<Sum>u\<in>S. min (u \<bullet> (a *v u)) 0)"
    using step by simp
  finally show ?thesis .
qed

end
