section \<open>Conditioning on the past, and the conditional law\<close>

(*<*)
theory Dynamic_Programming_Conditioning
  imports Dynamic_Programming_Pasting
    "Continuous_Time_Martingales.Integrability_Criteria"
begin

(*>*)

section \<open>Conditioning on the past for the \<open>\<le>\<close> half\<close>

text \<open>\<open>cInf_shift_real\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


text \<open>On the survival event the exit time splits exactly: the first piece
  contributes \<open>r\<close> and the rest is the exit time of the time-shifted path
  measured against the shortened horizon.  This is the identity that turns
  the almost-sure bound \<open>\<tau>\<^sub>K \<ge> c\<close> into a bound on the future.\<close>

lemma pexit_split_at_r:
  fixes K :: "'a::polish_space set" and f :: "real \<Rightarrow> 'a"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and surv: "pexit r K f = r" and endK: "f r \<in> K"
  shows "pexit T K f = r + pexit (T - r) K (\<lambda>s. f (r + s))"
proof -
  have stay: "f t \<in> K" if t: "t \<in> {0..r}" for t
  proof (rule ccontr)
    assume nk: "f t \<notin> K"
    have "pexit r K f \<le> t"
      unfolding pexit_def using r t nk by (intro etime_le_of_mem) auto
    with surv t have "t = r" by simp
    then show False using nk endK by simp
  qed
  define B where "B = {s. 0 \<le> s \<and> s \<le> T - r \<and> f (r + s) \<in> - K} \<union> {T - r}"
  have Beq: "{t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T} = (\<lambda>s. r + s) ` B"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> {t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T}"
    then consider (hit) "0 \<le> t" "t \<le> T" "f t \<in> - K" | (cap) "t = T" by blast
    then show "t \<in> (\<lambda>s. r + s) ` B"
    proof cases
      case hit
      have rt: "r < t"
      proof (rule ccontr)
        assume "\<not> r < t"
        then have "t \<in> {0..r}" using hit(1) by simp
        then show False using stay hit(3) by simp
      qed
      show ?thesis
      proof (rule image_eqI[where x = "t - r"])
        show "t = r + (t - r)" by simp
        show "t - r \<in> B" unfolding B_def using hit rt by simp
      qed
    next
      case cap
      show ?thesis
      proof (rule image_eqI[where x = "T - r"])
        show "t = r + (T - r)" using cap by simp
        show "T - r \<in> B" unfolding B_def by simp
      qed
    qed
  next
    fix t assume "t \<in> (\<lambda>s. r + s) ` B"
    then obtain s where s: "s \<in> B" "t = r + s" by blast
    from s(1) consider (hit) "0 \<le> s" "s \<le> T - r" "f (r + s) \<in> - K" | (cap) "s = T - r"
      unfolding B_def by blast
    then show "t \<in> {t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T}"
    proof cases
      case hit
      then show ?thesis using s(2) r by simp
    next
      case cap
      then show ?thesis using s(2) by simp
    qed
  qed
  have ne: "B \<noteq> {}" unfolding B_def by blast
  have bdd: "bdd_below B"
    unfolding B_def by (rule bdd_belowI[of _ 0]) (use rT in auto)
  have "pexit T K f = Inf ({t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  also have "\<dots> = Inf ((\<lambda>s. r + s) ` B)" unfolding Beq ..
  also have "\<dots> = r + Inf B" by (rule cInf_shift_real[OF ne bdd])
  also have "\<dots> = r + pexit (T - r) K (\<lambda>s. f (r + s))"
    unfolding pexit_def etime_def B_def ..
  finally show ?thesis .
qed

subsection \<open>The rebased future as a map of path spaces\<close>

text \<open>\<open>pfut r T \<omega>\<close> is the path after \<open>r\<close>, re-based at its own starting point,
  so that it starts at \<open>0\<close> no matter where \<open>\<omega>\<close> was at time \<open>r\<close>.  It is the
  map along which the conditional law of the future is taken.  Like the glue,
  it is Lipschitz --- with constant \<open>2\<close>, because the base point is subtracted
  and so counts once more.\<close>

definition pfut :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pfut r T \<omega> = restrict (\<lambda>s. \<omega> (r + s) - \<omega> r) {0..T - r}"

lemma pfut_apply: "s \<in> {0..T - r} \<Longrightarrow> pfut r T \<omega> s = \<omega> (r + s) - \<omega> r"
  by (simp add: pfut_def)

lemma pfut_zero: "0 \<le> T - r \<Longrightarrow> pfut r T \<omega> 0 = 0"
  by (simp add: pfut_def)

lemma pfut_fst:
  "s \<in> {0..T - r} \<Longrightarrow> fst (pfut r T \<omega> s) = fst (\<omega> (r + s)) - fst (\<omega> r)"
  by (simp add: pfut_def)

lemma pfut_in_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pfut r T \<omega> \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
proof -
  have cw: "continuous_on {0..T} \<omega>" by (rule mspace_path_metric_continuous[OF w])
  have sub: "(\<lambda>s. r + s) ` {0..T - r} \<subseteq> {0..T}" using r rT by auto
  have c1: "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s))"
    by (rule continuous_on_compose2[OF cw _ sub]) (intro continuous_intros)
  have "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s) - \<omega> r)"
    by (intro continuous_on_diff c1 continuous_on_const)
  then show ?thesis unfolding pfut_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfut:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n::finite pairpath) metric)
      (path_metric (T - r) :: ('n pairpath) metric) (pfut r T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfut r T \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric (T - r) :: ('n pairpath) metric)"
    by (intro funcsetI pfut_in_mspace[OF r rT])
  have T0: "0 \<le> T" using r rT by simp
  have Tr: "0 \<le> T - r" using rT by simp
  have key: "mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
      \<le> 2 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and g: "g \<in> mspace (path_metric T :: ('n pairpath) metric)" for f g
  proof -
    have sf: "pfut r T f \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by (rule pfut_in_mspace[OF r rT f])
    have sg: "pfut r T g \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by (rule pfut_in_mspace[OF r rT g])
    have pw: "\<forall>t\<in>{0..T}. dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T0 f g] by blast
    have pws: "dist (pfut r T f s) (pfut r T g s) \<le> 2 * mdist (path_metric T) f g"
      if s: "s \<in> {0..T - r}" for s
    proof -
      have rs: "r + s \<in> {0..T}" using s r rT by simp
      have r0: "r \<in> {0..T}" using r rT by simp
      have "dist (pfut r T f s) (pfut r T g s)
          = dist (f (r + s) - f r) (g (r + s) - g r)"
        using s by (simp add: pfut_apply)
      also have "\<dots> = norm ((f (r + s) - g (r + s)) - (f r - g r))"
        by (simp add: dist_norm algebra_simps)
      also have "\<dots> \<le> norm (f (r + s) - g (r + s)) + norm (f r - g r)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> = dist (f (r + s)) (g (r + s)) + dist (f r) (g r)"
        by (simp add: dist_norm)
      finally show ?thesis using bspec[OF pw rs] bspec[OF pw r0] by simp
    qed
    show ?thesis using path_mdist_le_iff_all[OF Tr sf sg] pws by blast
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>g\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 2] ballI key)
qed

lemma pfut_measurable:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pfut r T
      \<in> borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pfut[OF r rT])

lemma pfut_measurable_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pfut r T \<in> Q \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  using pfut_measurable[OF r rT] measurable_cong_sets[OF setsQ refl] by blast

text \<open>The exit time of the future, expressed through \<open>pfut\<close>: re-basing at the
  endpoint and adding the endpoint back is the identity on the exit time.\<close>

text \<open>Conditioning on an event of the past keeps martingales martingales:
  \<open>uniform_measure_density_real\<close>, \<open>integral_uniform_measure_eq\<close>,
  \<open>integrable_uniform_measureI\<close>, \<open>set_integral_uniform_measure_eq\<close> and
  \<open>martingale_uniform_measure\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

text \<open>\<open>pair_fst_borel\<close> lives in @{theory Relative_Arbitrage.Exit_Class_Pasting}.\<close>

theorem martingale_future_of_past:
  fixes P :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
           0 (\<lambda>v w. w v) u)"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. Z u (pfut r T \<omega>))"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0 Z"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?FF = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  interpret PP: prob_space P by (rule PS)
  have Tr: "0 \<le> ?S" using rT by simp
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsM])
  have A': "A \<in> sets (?FF 0)"
  proof -
    have "r + min 0 ?S = r" using Tr by simp
    then show ?thesis using A by simp
  qed
  have mgM: "martingale ?M ?FF 0 (\<lambda>u \<omega>. Z u (pfut r T \<omega>))"
    by (rule martingale_uniform_measure[OF PS mg A' pos])
  show ?thesis
  proof (rule martingale_pair_law[OF PM phim _ Zm mgM])
    fix u v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) \<in> borel_measurable (?FF u)"
    proof (cases "v \<le> ?S")
      case True
      have m1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v)) \<in> borel_measurable (?FF u)"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use r v vu True in auto)
      have m2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable (?FF u)"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use r v vu True Tr in auto)
      have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v) - \<omega> r) \<in> borel_measurable (?FF u)"
        by (rule borel_measurable_diff[OF m1 m2])
      moreover have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. \<omega> (r + v) - \<omega> r)"
        using v True by (auto simp: pfut_apply)
      ultimately show ?thesis by simp
    next
      case False
      then have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. undefined)"
        by (auto simp: pfut_def)
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>The four clauses of (1.7) for the conditioned future law\<close>

text \<open>Clause (i) is free: @{thm [source] pfut_zero} says the rebased future
  starts at \<open>0\<close> no matter where the path was at time \<open>r\<close>, so the initial
  condition holds identically rather than almost surely.\<close>

lemma pfut_law_start:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      fst (w 0) = 0 \<and> snd (w 0) = 0"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" using setsP by simp
  have phim: "pfut r T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pfut_measurable_law[OF r rT setsM])
  have ev: "(\<lambda>w :: 'n pairpath. w 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{w \<in> space ?B. fst (w 0) = 0 \<and> snd (w 0) = 0} \<in> sets ?B"
  proof -
    have "{w \<in> space ?B. fst (w 0) = 0 \<and> snd (w 0) = 0}
        = (\<lambda>w :: 'n pairpath. w 0) -` {(0, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have iff: "(AE w in pair_law_of ?S (pfut r T) ?M. fst (w 0) = 0 \<and> snd (w 0) = 0)
      = (AE \<omega> in ?M. fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
  have "AE \<omega> in ?M. fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0"
    by (rule AE_I2) (simp add: pfut_zero[OF Tr])
  then show ?thesis unfolding iff .
qed

text \<open>Clause (ii) is inheritance: the future's increment over \<open>[p,q]\<close> is
  the path's increment over \<open>[r+p, r+q]\<close>, the base point cancelling, and the
  two time spans agree.\<close>

lemma pfut_law_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and AM: "A \<in> sets P"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof (rule exit_class_diffquot_of_pairs[OF sets_pair_law_of])
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  fix p q :: real
  assume pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q"
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" using setsP by simp
  have phim: "pfut r T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pfut_measurable_law[OF r rT setsM])
  have mm: "{w \<in> space ?B.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L} \<in> sets ?B"
    using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
    by (simp add: space_borel_of)
  have iff: "(AE w in pair_law_of ?S (pfut r T) ?M.
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L)
      = (AE \<omega> in ?M. (1 / (q - p))
          *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
  have covM: "AE \<omega> in ?M. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule AE_uniform_measureI[OF AM]) (use cov in \<open>auto elim: eventually_mono\<close>)
  have "AE \<omega> in ?M. (1 / (q - p))
      *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L"
  proof (rule eventually_mono[OF covM])
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    have rp: "0 \<le> r + p" using r pq by simp
    have rpq: "r + p < r + q" using pq by simp
    have rqT: "r + q \<le> T" using pq by simp
    have "(1 / ((r + q) - (r + p)))
        *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p))) \<in> sconstraint k L"
      using h rp rpq rqT by blast
    then have "(1 / (q - p))
        *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p))) \<in> sconstraint k L" by simp
    moreover have "snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)
        = snd (\<omega> (r + q)) - snd (\<omega> (r + p))"
      using pq by (simp add: pfut_apply)
    ultimately show "(1 / (q - p))
        *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L" by simp
  qed
  then show "AE w in pair_law_of ?S (pfut r T) ?M.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    unfolding iff .
qed

text \<open>Clause (iii): the coordinate martingale.  Shift the clock by \<open>r\<close>
  (@{thm [source] martingale_time_change}), subtract the value at \<open>r\<close>
  (@{thm [source] martingale_sub_initial}), and hand the result to
  @{thm [source] martingale_future_of_past}, which conditions on the past
  event and pushes along \<open>pfut\<close>.\<close>

lemma pfut_law_X_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0 (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have Zm: "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)))
      \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
    if u: "0 \<le> u" for u
  proof (rule measurable_compose[OF _ pair_fst_borel])
    show "(\<lambda>w :: 'n pairpath. w (min u ?S))
        \<in> natural_filtration ?Q 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u Tr in auto)
  qed
  have MGX: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule exit_class_X_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGX s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  have mg2: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)))"
    using mg1 by (simp add: eqmin)
  have mg3: "martingale P ?FP 0
      (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S)))"
    by (rule martingale_sub_initial[OF mg2])
  have mg: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (pfut r T \<omega> (min u ?S)))"
  proof (rule martingale_cong_ge[OF mg3])
    fix u :: real assume u: "0 \<le> u"
    have m: "min u ?S \<in> {0..?S}" using u Tr by simp
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S)))
        = (\<lambda>\<omega>. fst (pfut r T \<omega> (min u ?S)))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      have "fst (pfut r T \<omega> (min u ?S)) = fst (\<omega> (r + min u ?S)) - fst (\<omega> r)"
        by (rule pfut_fst[OF m])
      then show "fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S))
          = fst (pfut r T \<omega> (min u ?S))" using Tr by simp
    qed
  qed
  show ?thesis
    by (rule martingale_future_of_past[OF r rT setsP PS A pos Zm mg])
qed

text \<open>Clause (iv) needs a separate argument, because \<^const>\<open>outerp\<close> is
  quadratic: the compensated process of the rebased future is not the
  increment of the compensated process.  Expanding
  \<open>outerp (a - b) = outerp a - (a \<otimes> b + b \<otimes> a) + outerp b\<close> with
  \<open>a = X\<^sub>t\<close>, \<open>b = X\<^sub>r\<close> gives
  \<open>outerp (X\<^sub>t - X\<^sub>r) - (Y\<^sub>t - Y\<^sub>r)
       = (outerp X\<^sub>t - Y\<^sub>t) - (X\<^sub>t \<otimes> X\<^sub>r + X\<^sub>r \<otimes> X\<^sub>t) + (outerp X\<^sub>r + Y\<^sub>r)\<close>.
  The first bracket is clause (iv) for \<open>P\<close>; the third is constant in \<open>t\<close> and
  \<open>\<F>\<^sub>r\<close>-measurable; the middle, cross term is a martingale because a
  martingale multiplied entrywise by a fixed \<open>\<F>\<^sub>r\<close>-measurable factor is again
  a martingale, lifted entrywise to \<open>real^'n^'n\<close> through @{thm [source]
  martingale_matI}, with integrability of \<open>X\<^sub>t $ i * X\<^sub>r $ j\<close> supplied by
  Cauchy--Schwarz from the class's fourth moments (@{thm [source]
  exit_class_fourth_moment}).\<close>

lemma outerp_diff:
  fixes a b :: "real^'n::finite"
  shows "outerp (a - b) = outerp a - ((\<chi> i j. a $ i * b $ j)
      + (\<chi> i j. b $ i * a $ j)) + outerp b"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_diff_compensated:
  fixes a b :: "real^'n::finite" and Ya Yb :: "real^'n^'n"
  shows "outerp (a - b) - (Ya - Yb)
      = (outerp a - Ya) - ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
        + (outerp b + Yb)"
  by (simp add: outerp_diff)

text \<open>The martingale-level form of "pulling out what is known": the AFP's
  conditional-expectation lemma \<open>cond_exp_measurable_mult\<close> feeds the
  cross term of @{thm [source] outerp_diff_compensated}.  The factor must be
  measurable for the filtration at the initial time, not merely somewhere
  along it, or it is not adapted.  \<open>martingale_mult_measurable\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>\<open>integrable_mult_of_sq\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


text \<open>\<open>martingale_cross_measurable\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>\<open>martingale_diff\<close>, the subtractive companion to \<open>martingale_add\<close>,
  lives in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

subsection \<open>The shifted processes of a class member\<close>

text \<open>\<open>pair_snd_borel\<close> lives in @{theory Relative_Arbitrage.Exit_Class_Pasting}.\<close>

lemma exit_class_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  using Q unfolding exit_class_def by blast

text \<open>Both coordinate processes of a class member, restarted at \<open>r\<close>: the
  clock is shifted by @{thm [source] martingale_time_change} and the horizon
  cap becomes invisible, since \<open>r + min u (T-r) \<le> T\<close> always.\<close>

lemma exit_class_shifted_X_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and P: "P \<in> exit_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. fst (\<omega> (r + min u (T - r))))"
proof -
  let ?S = "T - r"
  have Tr: "0 \<le> ?S" using rT by simp
  have MGX: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule exit_class_X_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGX s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  show ?thesis using mg1 by (simp add: eqmin)
qed

lemma exit_class_shifted_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and P: "P \<in> exit_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u (T - r))))
          - snd (\<omega> (r + min u (T - r))))"
proof -
  let ?S = "T - r"
  have Tr: "0 \<le> ?S" using rT by simp
  have MGY: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule exit_class_comp_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min (r + min u ?S) T)))
          - snd (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGY s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  show ?thesis using mg1 by (simp add: eqmin)
qed

text \<open>The compensated process of the rebased future is a martingale under
  \<open>P\<close> itself, in the shifted filtration.  This is the clause-(iv) analogue
  of @{thm [source] exit_class_shifted_X_martingale}, not the same
  statement since \<^const>\<open>outerp\<close> is quadratic: the decomposition
  @{thm [source] outerp_diff_compensated} splits it into the class's own
  clause (iv) restarted at \<open>r\<close>, minus the cross term
  (@{thm [source] martingale_cross_measurable}, using \<open>\<F>\<^sub>r\<close>-measurability of
  \<open>X\<^sub>r\<close>), plus an \<open>\<F>\<^sub>r\<close>-measurable constant.\<close>

lemma exit_class_pfut_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> exit_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
          - snd (pfut r T \<omega> (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have T0: "0 \<le> T" using r rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have mem: "r + min u ?S \<in> {0..T}" if "0 \<le> u" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then show ?thesis using r that Tr by simp
  qed

  \<comment> \<open>(A) the class's own clause (iv), restarted at \<open>r\<close>\<close>
  have mgA: "martingale P ?FP 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))"
    by (rule exit_class_shifted_comp_martingale[OF r rT P])
  interpret MGA: martingale P ?FP 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S))"
    by (rule mgA)

  \<comment> \<open>(B) the cross term\<close>
  have mgX: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)))"
    by (rule exit_class_shifted_X_martingale[OF r rT P])
  have mgXi: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ i)" for i
    by (rule martingale_vec_nth[OF mgX])
  have startm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable (?FP 0)"
    for j
  proof -
    interpret MX: martingale P ?FP 0 "\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ j"
      by (rule mgXi)
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min 0 ?S)) $ j)
        \<in> borel_measurable (?FP 0)"
      by (rule MX.adapted[of 0]) simp
    then show ?thesis using Tr by simp
  qed
  have PmX: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) $ i) \<in> borel_measurable P"
    if u: "0 \<le> u" for u i
  proof -
    interpret MX: martingale P ?FP 0 "\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ i"
      by (rule mgXi)
    show ?thesis
      by (rule measurable_from_subalg[OF MGA.subalgebras[OF u] MX.adapted[OF u]])
  qed
  have Pstart: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable P" for j
    using PmX[of 0 j] Tr by simp
  have intB: "integrable P
      (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j * fst (\<omega> (r + min u ?S)) $ i)"
    if u: "0 \<le> u" for u i j
  proof (rule integrable_mult_of_sq)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable P"
      by (rule Pstart)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) $ i) \<in> borel_measurable P"
      by (rule PmX[OF u])
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> r) $ j)\<^sup>2)"
      using r rT by (intro exit_class_sq_integrable[OF T0 L0 P]) simp
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> (r + min u ?S)) $ i)\<^sup>2)"
      using mem[OF u] by (intro exit_class_sq_integrable[OF T0 L0 P]) simp
  qed
  have mgB: "martingale P ?FP 0 (\<lambda>u \<omega>.
      (\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
      + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))"
  proof (rule martingale_cross_measurable)
    show "martingale P ?FP 0 (\<lambda>t \<omega>. fst (\<omega> (r + min t ?S)) $ i)" for i
      by (rule mgXi)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable (?FP 0)" for j
      by (rule startm)
    show "integrable P
        (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j * fst (\<omega> (r + min u ?S)) $ i)"
      if "0 \<le> u" for u i j by (rule intB[OF that])
  qed

  \<comment> \<open>(C) the \<open>\<F>\<^sub>r\<close>-measurable constant\<close>
  have evr: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> ?FP 0 \<rightarrow>\<^sub>M borel"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use r Tr in auto)
  have Cmeas: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))
      \<in> borel_measurable (?FP 0)"
  proof -
    have m1: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r))) \<in> borel_measurable (?FP 0)"
      by (rule measurable_compose
          [OF measurable_compose[OF evr pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> r)) \<in> borel_measurable (?FP 0)"
      by (rule measurable_compose[OF evr pair_snd_borel])
    show ?thesis by (rule borel_measurable_add[OF m1 m2])
  qed
  have CmeasP: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))
      \<in> borel_measurable P"
    by (rule measurable_from_subalg[OF MGA.subalgebras[OF order_refl] Cmeas])
  have Cint: "integrable P (\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))"
  proof (rule integrable_mat_entries[OF CmeasP])
    fix i j
    have eqf: "(\<lambda>\<omega> :: 'n pairpath. (outerp (fst (\<omega> r)) + snd (\<omega> r)) $ i $ j)
        = (\<lambda>\<omega>. fst (\<omega> r) $ i * fst (\<omega> r) $ j + snd (\<omega> r) $ i $ j)"
      by (rule ext) (simp add: outerp_def)
    have i1: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ i * fst (\<omega> r) $ j)"
      using intB[of 0 i j] Tr by simp
    have i2: "integrable P (\<lambda>\<omega> :: 'n pairpath. snd (\<omega> r) $ i $ j)"
      using r rT by (intro exit_class_Y_entry_integrable[OF T0 L0 P]) simp
    show "integrable P
        (\<lambda>\<omega> :: 'n pairpath. (outerp (fst (\<omega> r)) + snd (\<omega> r)) $ i $ j)"
      unfolding eqf by (rule Bochner_Integration.integrable_add[OF i1 i2])
  qed
  have mgC: "martingale P ?FP 0 (\<lambda>_ \<omega> :: 'n pairpath.
      outerp (fst (\<omega> r)) + snd (\<omega> r))"
    by (rule MGA.martingale_const_fun[OF Cint Cmeas])

  \<comment> \<open>combine, and recognise the result as the future's compensated process\<close>
  have mgABC: "martingale P ?FP 0 (\<lambda>u \<omega>.
      (outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
      - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
         + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
      + (outerp (fst (\<omega> r)) + snd (\<omega> r)))"
    by (rule martingale_add[OF martingale_diff[OF mgA mgB] mgC])
  show ?thesis
  proof (rule martingale_cong_ge[OF mgABC])
    fix u :: real assume u: "0 \<le> u"
    have m: "min u ?S \<in> {0..?S}" using u Tr by simp
    show "(\<lambda>\<omega> :: 'n pairpath.
          (outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
          - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
             + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
          + (outerp (fst (\<omega> r)) + snd (\<omega> r)))
        = (\<lambda>\<omega>. outerp (fst (pfut r T \<omega> (min u ?S)))
            - snd (pfut r T \<omega> (min u ?S)))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      have f1: "fst (pfut r T \<omega> (min u ?S)) = fst (\<omega> (r + min u ?S)) - fst (\<omega> r)"
        by (rule pfut_fst[OF m])
      have f2: "snd (pfut r T \<omega> (min u ?S)) = snd (\<omega> (r + min u ?S)) - snd (\<omega> r)"
        using m by (simp add: pfut_apply)
      show "(outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
          - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
             + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
          + (outerp (fst (\<omega> r)) + snd (\<omega> r))
        = outerp (fst (pfut r T \<omega> (min u ?S)))
            - snd (pfut r T \<omega> (min u ?S))"
        unfolding f1 f2 by (rule outerp_diff_compensated[symmetric])
    qed
  qed
qed

text \<open>Clause (iv) for the conditioned future law, by the same decomposition
  @{thm [source] outerp_diff_compensated}: the class's own clause (iv)
  restarted at \<open>r\<close>, the cross term (@{thm [source]
  martingale_cross_measurable}), and an \<open>\<F>\<^sub>r\<close>-measurable constant.\<close>

lemma pfut_law_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have T0: "0 \<le> T" using r rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have FP0: "?FP 0 = natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r"
    using Tr by simp
  have mem: "r + min u ?S \<in> {0..T}" if "0 \<le> u" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then show ?thesis using r that Tr by simp
  qed

  \<comment> \<open>the integrand is a random variable for the natural filtration of \<open>?Q\<close>\<close>
  have Zm: "(\<lambda>w :: 'n pairpath.
        outerp (fst (w (min u ?S))) - snd (w (min u ?S)))
      \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>w :: 'n pairpath. w (min u ?S))
        \<in> natural_filtration ?Q 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u Tr in auto)
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u ?S))))
        \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
      by (rule measurable_compose
          [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w (min u ?S)))
        \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
      by (rule measurable_compose[OF ev pair_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed

  \<comment> \<open>the whole decomposition is now a lemma of its own\<close>
  have mg: "martingale P ?FP 0 (\<lambda>u \<omega>.
      outerp (fst (pfut r T \<omega> (min u ?S))) - snd (pfut r T \<omega> (min u ?S)))"
    by (rule exit_class_pfut_comp_martingale[OF r rT L0 P])
  show ?thesis
    by (rule martingale_future_of_past[OF r rT setsP PS A pos Zm mg])
qed

text \<open>All four clauses together: \<^emph>\<open>conditioning on an event of the past
  leaves the future in the class, started at the origin.\<close>  This is the
  structural fact the \<open>\<le>\<close> half of (2.9) turns on, and it needs no regular
  conditional distribution.\<close>

theorem exit_class_future_of_past:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "pair_law_of (T - r) (pfut r T) (uniform_measure P A)
      \<in> exit_class k L (T - r) 0"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  interpret MGX: martingale P
      "natural_filtration P 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T))"
    by (rule exit_class_X_martingale[OF P])
  have AM: "A \<in> sets P" using A MGX.sets_F_subset[OF r] by blast
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsM])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule prob_space.prob_space_distr[OF PM phim])
  have cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using P unfolding exit_class_def by blast
  show ?thesis
    unfolding exit_class_def
  proof (intro CollectI conjI)
    show "prob_space ?Q" by (rule PQ)
    show "sets ?Q = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))"
      by (rule sets_pair_law_of)
    show "AE w in ?Q. fst (w 0) = 0 \<and> snd (w 0) = 0"
      by (rule pfut_law_start[OF r rT setsP])
    show "AE w in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> ?S \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
      by (rule pfut_law_diffquot[OF r rT setsP AM cov])
    show "martingale ?Q (natural_filtration ?Q 0 (\<lambda>t w. w t)) 0
        (\<lambda>t w. fst (w (min t ?S)))"
      by (rule pfut_law_X_martingale[OF r rT P A pos])
    show "martingale ?Q (natural_filtration ?Q 0 (\<lambda>t w. w t)) 0
        (\<lambda>t w. outerp (fst (w (min t ?S))) - snd (w (min t ?S)))"
      by (rule pfut_law_comp_martingale[OF r rT L0 P A pos])
  qed
qed

subsection \<open>The survival event belongs to the past\<close>

text \<open>\<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close> says exactly that the path never
  leaves \<open>K\<close> on \<open>{0..r}\<close>, and for a continuous path against a closed \<open>K\<close>
  that is decided by the rational times alone, so the survival event is
  \<open>\<F>\<^sub>r\<close>-measurable and can be used as the conditioning event \<open>A\<close> of
  @{thm [source] exit_class_future_of_past}.\<close>

subsection \<open>A set-integral criterion for the conditional law\<close>

text \<open>Every condition defining the class is linear in the measure ---
  \<open>\<mu> C = 1\<close> for the initial and covariation clauses, \<open>\<integral> (X\<^sub>t - X\<^sub>s) 1\<^sub>A d\<mu> = 0\<close>
  for the martingale clauses --- so passing from "it holds for
  \<open>P(\<sqdot> | A)\<close>, every \<open>A \<in> \<F>\<^sub>r\<close>" to "it holds for the conditional law at
  almost every \<open>\<omega>\<close>" needs only that a \<open>\<G>\<close>-measurable function all of whose
  \<open>\<G>\<close>-set integrals vanish is almost everywhere zero.\<close>

text \<open>\<open>AE_nonpos_of_set_integral_zero\<close> and \<open>AE_zero_of_set_integral_zero\<close> live
  in @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

subsection \<open>The conditional law of the future given the past\<close>

text \<open>The only hypothesis of AFP \<^theory>\<open>Disintegration.Disintegration\<close> that
  is not automatic here is that the future path space is standard Borel: this
  is immediate, since \<open>standard_borel\<close> only asks for some Polish topology
  whose Borel sets agree, and the path space already is the Borel algebra of
  one.\<close>

lemma standard_borel_path_metric:
  "standard_borel (borel_of (mtopology_of
      (path_metric U :: ('n::finite pairpath) metric)))"
  unfolding standard_borel_def
  by (intro exI[of _ "mtopology_of (path_metric U :: ('n pairpath) metric)"]
      conjI Polish_space_path_metric refl)

lemma mspace_path_metric_ne:
  assumes U: "0 \<le> U"
  shows "mspace (path_metric U :: ('n::finite pairpath) metric) \<noteq> {}"
proof -
  have "continuous_on {0..U} (\<lambda>t. (0 :: (real^'n) \<times> (real^'n^'n)))"
    by (rule continuous_on_const)
  then have "restrict (\<lambda>t. (0 :: (real^'n) \<times> (real^'n^'n))) {0..U}
      \<in> mspace (path_metric U :: ('n pairpath) metric)"
    by (rule mspace_path_metricI)
  then show ?thesis by blast
qed

lemma standard_borel_ne_path_metric:
  assumes U: "0 \<le> U"
  shows "standard_borel_ne (borel_of (mtopology_of
      (path_metric U :: ('n::finite pairpath) metric)))"
proof -
  have "space (borel_of (mtopology_of
      (path_metric U :: ('n pairpath) metric))) \<noteq> {}"
    using mspace_path_metric_ne[OF U] by (simp add: space_borel_of)
  then show ?thesis
    unfolding standard_borel_ne_def standard_borel_ne_axioms_def
    using standard_borel_path_metric by blast
qed

text \<open>The regular conditional distribution itself.  The AFP's
  \<open>disintegration\<close> constrains rectangles only, which suffices because the
  next step converts it to \<open>ksemi\<close>, for which the almost-sure and integral
  forms are already proved.\<close>

theorem exit_class_rcd:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and "\<And>A B. A \<in> sets (borel_of (mtopology_of
            (path_metric r :: ('n pairpath) metric)))
        \<Longrightarrow> B \<in> sets (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))
        \<Longrightarrow> emeasure (distr P
              (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
                \<Otimes>\<^sub>M borel_of (mtopology_of
                  (path_metric (T - r) :: ('n pairpath) metric)))
              (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))) (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of r (pcut r) P))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  have Tr: "0 \<le> T - r" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have setsnu: "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by simp

  \<comment> \<open>the marginal on the past is the law of \<open>pcut r\<close>\<close>
  have marg: "marginal_measure ?X ?Y ?\<nu> = pair_law_of r (pcut r) P"
  proof (rule measure_eqI)
    show "sets (marginal_measure ?X ?Y ?\<nu>) = sets (pair_law_of r (pcut r) P)"
      by (simp add: sets_marginal_measure)
    fix A assume "A \<in> sets (marginal_measure ?X ?Y ?\<nu>)"
    then have AX: "A \<in> sets ?X" by (simp add: sets_marginal_measure)
    have rect: "A \<times> space ?Y \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using AX by simp
    have "emeasure (marginal_measure ?X ?Y ?\<nu>) A = emeasure ?\<nu> (A \<times> space ?Y)"
      by (rule emeasure_marginal_measure[OF setsnu AX])
    also have "\<dots> = emeasure P (?\<phi> -` (A \<times> space ?Y) \<inter> space P)"
      by (rule emeasure_distr[OF mphi rect])
    also have "\<dots> = emeasure P (pcut r -` A \<inter> space P)"
    proof -
      have "?\<phi> -` (A \<times> space ?Y) \<inter> space P = pcut r -` A \<inter> space P"
        using measurable_space[OF mfut] by auto
      then show ?thesis by simp
    qed
    also have "\<dots> = emeasure (pair_law_of r (pcut r) P) A"
      unfolding pair_law_of_def by (rule emeasure_distr[OF mcut AX, symmetric])
    finally show "emeasure (marginal_measure ?X ?Y ?\<nu>) A
        = emeasure (pair_law_of r (pcut r) P) A" .
  qed

  \<comment> \<open>the two locale obligations\<close>
  have PSF: "projection_sigma_finite ?X ?Y ?\<nu>"
    unfolding projection_sigma_finite_def
  proof (intro conjI)
    show "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by (rule setsnu)
    have "prob_space (pair_law_of r (pcut r) P)"
      unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
    then show "sigma_finite_measure (marginal_measure ?X ?Y ?\<nu>)"
      unfolding marg by (rule prob_space_imp_sigma_finite)
  qed
  have SB: "standard_borel_ne ?Y" by (rule standard_borel_ne_path_metric[OF Tr])
  interpret D: projection_sigma_finite_standard ?X ?Y ?\<nu>
    unfolding projection_sigma_finite_standard_def using PSF SB by blast

  obtain \<kappa> where K: "prob_kernel ?X ?Y \<kappa>"
    and DIS: "measure_kernel.disintegration ?X ?Y \<kappa> ?\<nu>
        (marginal_measure ?X ?Y ?\<nu>)"
    using D.measure_disintegration by blast
  interpret MK: measure_kernel ?X ?Y \<kappa> using K by (simp add: prob_kernel_def)
  have Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" using K by (simp add: prob_kernel_def')

  show ?thesis
  proof (rule that)
    show "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" by (rule Km)
    show "emeasure ?\<nu> (A \<times> B)
        = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of r (pcut r) P))"
      if A: "A \<in> sets ?X" and B: "B \<in> sets ?Y" for A B
    proof -
      have "emeasure ?\<nu> (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(marginal_measure ?X ?Y ?\<nu>))"
        using DIS A B unfolding MK.disintegration_def by blast
      then show ?thesis unfolding marg .
    qed
  qed
qed

text \<open>The semidirect product on a rectangle, the shape in which the AFP's
  disintegration arrives.\<close>

lemma emeasure_ksemi_rect:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and A: "A \<in> sets M" and B: "B \<in> sets N"
  shows "emeasure (ksemi M N Kr) (A \<times> B) = (\<integral>\<^sup>+\<omega>\<in>A. emeasure (Kr \<omega>) B \<partial>M)"
proof -
  have rect: "A \<times> B \<in> sets (M \<Otimes>\<^sub>M N)" using A B by simp
  have "emeasure (ksemi M N Kr) (A \<times> B)
      = (\<integral>\<^sup>+\<omega>. emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B) \<partial>M)"
    unfolding ksemi_def
    by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] rect])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator A \<omega> * emeasure (Kr \<omega>) B \<partial>M)"
  proof (rule nn_integral_cong)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have spK: "space (Kr \<omega>) = space N" by (rule sets_eq_imp_space_eq[OF sK])
    have "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = emeasure (Kr \<omega>) (Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>))"
      by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] rect])
    also have "\<dots> = indicator A \<omega> * emeasure (Kr \<omega>) B"
    proof (cases "\<omega> \<in> A")
      case True
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = B"
        using True B sets.sets_into_space[OF B] by (auto simp: spK)
      then show ?thesis using True by simp
    next
      case False
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = {}" using False by auto
      then show ?thesis using False by simp
    qed
    finally show "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = indicator A \<omega> * emeasure (Kr \<omega>) B" .
  qed
  finally show ?thesis by (simp add: nn_integral_set_ennreal mult.commute)
qed

text \<open>Two probability measures on \<open>?X \<Otimes>\<^sub>M ?Y\<close> that agree on the rectangle
  \<open>\<pi>\<close>-system are equal, so the AFP's rectangle-level disintegration is the
  semidirect product \<open>ksemi\<close>, after which @{thm [source] AE_ksemi} and
  @{thm [source] nn_integral_ksemi} give the almost-sure and integral forms
  with no further measure-theoretic induction.\<close>

theorem exit_class_rcd_ksemi:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?E = "{a \<times> b | a b. a \<in> sets ?X \<and> b \<in> sets ?Y}"
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  interpret Pnu: prob_space ?\<nu> by (rule PP.prob_space_distr[OF mphi])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and REC: "\<And>A B. A \<in> sets ?X \<Longrightarrow> B \<in> sets ?Y \<Longrightarrow>
        emeasure ?\<nu> (A \<times> B) = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
    by (rule exit_class_rcd[OF r rT setsP PS]) blast
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Km measurable_cong_sets[OF setsQ refl] by blast
  have setsS: "sets (ksemi ?Q ?Y \<kappa>) = sets (?X \<Otimes>\<^sub>M ?Y)"
  proof -
    have "sets (ksemi ?Q ?Y \<kappa>) = sets (?Q \<Otimes>\<^sub>M ?Y)" by (rule sets_ksemi[OF KQ neQ])
    also have "\<dots> = sets (?X \<Otimes>\<^sub>M ?Y)"
      by (rule sets_pair_measure_cong[OF setsQ refl])
    finally show ?thesis .
  qed
  have eq: "?\<nu> = ksemi ?Q ?Y \<kappa>"
  proof (rule measure_eqI_generator_eq
      [where E = ?E and \<Omega> = "space ?X \<times> space ?Y"
         and A = "\<lambda>_. space ?X \<times> space ?Y"])
    show "Int_stable ?E" by (rule Int_stable_pair_measure_generator)
    show "?E \<subseteq> Pow (space ?X \<times> space ?Y)" using sets.sets_into_space by auto
    show "emeasure ?\<nu> C = emeasure (ksemi ?Q ?Y \<kappa>) C" if C: "C \<in> ?E" for C
    proof -
      from C obtain A B where AB: "A \<in> sets ?X" "B \<in> sets ?Y" "C = A \<times> B"
        by blast
      have AQ: "A \<in> sets ?Q" using AB(1) setsQ by simp
      have "emeasure ?\<nu> C = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
        unfolding AB(3) by (rule REC[OF AB(1) AB(2)])
      also have "\<dots> = emeasure (ksemi ?Q ?Y \<kappa>) C"
        unfolding AB(3)
        by (rule emeasure_ksemi_rect[OF KQ neQ AQ AB(2), symmetric])
      finally show ?thesis .
    qed
    show "sets ?\<nu> = sigma_sets (space ?X \<times> space ?Y) ?E"
      by (simp add: sets_pair_measure)
    show "sets (ksemi ?Q ?Y \<kappa>) = sigma_sets (space ?X \<times> space ?Y) ?E"
      unfolding setsS by (simp add: sets_pair_measure)
    show "range (\<lambda>_. space ?X \<times> space ?Y) \<subseteq> ?E" by auto
    show "(\<Union>i :: nat. space ?X \<times> space ?Y) = space ?X \<times> space ?Y" by simp
    show "emeasure ?\<nu> (space ?X \<times> space ?Y) \<noteq> \<infinity>" for i :: nat
      by (simp add: Pnu.emeasure_eq_measure)
  qed
  show ?thesis by (rule that[OF Km eq])
qed

subsection \<open>The almost-sure clauses pass to the kernel\<close>

text \<open>Clauses (i) and (ii) of (1.7) both say "\<open>\<mu> C = 1\<close> for a fixed
  measurable \<open>C\<close>", linear in \<open>\<mu>\<close>, so each transfers to the kernel by a
  single nonnegative-integral argument: the complement has integral \<open>0\<close>,
  hence vanishes almost everywhere.\<close>

lemma AE_kernel_full:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and C: "C \<in> sets N"
    and null: "emeasure (ksemi M N Kr) (space M \<times> (space N - C)) = 0"
  shows "AE \<omega> in M. emeasure (Kr \<omega>) C = 1"
proof -
  have C': "space N - C \<in> sets N" using C by (rule sets.compl_sets)
  have spM: "space M \<in> sets M" by simp
  have mE: "(\<lambda>\<omega>. emeasure (Kr \<omega>) (space N - C)) \<in> borel_measurable M"
    by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
          measurable_emeasure_subprob_algebra[OF C']])
  have "(\<integral>\<^sup>+\<omega>. emeasure (Kr \<omega>) (space N - C) \<partial>M)
      = (\<integral>\<^sup>+\<omega>\<in>space M. emeasure (Kr \<omega>) (space N - C) \<partial>M)"
    by (intro nn_integral_cong) simp
  also have "\<dots> = emeasure (ksemi M N Kr) (space M \<times> (space N - C))"
    by (rule emeasure_ksemi_rect[OF K ne spM C', symmetric])
  also have "\<dots> = 0" by (rule null)
  finally have "(\<integral>\<^sup>+\<omega>. emeasure (Kr \<omega>) (space N - C) \<partial>M) = 0" .
  then have ae: "AE \<omega> in M. emeasure (Kr \<omega>) (space N - C) = 0"
    using mE by (simp add: nn_integral_0_iff_AE)
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with ae show ?thesis
  proof eventually_elim
    fix \<omega> assume z: "emeasure (Kr \<omega>) (space N - C) = 0" and w: "\<omega> \<in> space M"
    interpret PK: prob_space "Kr \<omega>" by (rule ksemi_sets_kernel(2)[OF K w])
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have spK: "space (Kr \<omega>) = space N" by (rule sets_eq_imp_space_eq[OF sK])
    have CK: "C \<in> sets (Kr \<omega>)" using C sK by simp
    have C'K: "space N - C \<in> sets (Kr \<omega>)" using C' sK by simp
    have "emeasure (Kr \<omega>) (C \<union> (space N - C))
        = emeasure (Kr \<omega>) C + emeasure (Kr \<omega>) (space N - C)"
      by (rule plus_emeasure[OF CK C'K, symmetric]) auto
    moreover have "C \<union> (space N - C) = space (Kr \<omega>)"
      using sets.sets_into_space[OF C] by (auto simp: spK)
    ultimately have "emeasure (Kr \<omega>) C = 1"
      using z PK.emeasure_space_1 by simp
    then show "emeasure (Kr \<omega>) C = 1" .
  qed
qed

text \<open>Clause (i) for the kernel, the easiest of the four: @{thm [source]
  pfut_zero} makes the initial condition hold identically, so the offending
  set has empty preimage, not merely a null one.\<close>

lemma pfut_rcd_start:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
  shows "AE p in pair_law_of r (pcut r) P.
      emeasure (\<kappa> p) {w \<in> space (borel_of (mtopology_of
          (path_metric (T - r) :: ('n pairpath) metric))).
        fst (w 0) = 0 \<and> snd (w 0) = 0} = 1"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?C = "{w :: 'n pairpath \<in> space ?Y. fst (w 0) = 0 \<and> snd (w 0) = 0}"
  have Tr: "0 \<le> T - r" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w 0) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have CY: "?C \<in> sets ?Y"
  proof -
    have "?C = (\<lambda>w :: 'n pairpath. w 0) -` {(0, 0)} \<inter> space ?Y"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have C': "space ?Y - ?C \<in> sets ?Y" using CY by (rule sets.compl_sets)
  have rect: "space ?X \<times> (space ?Y - ?C) \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using C' by simp
  have empty: "?\<phi> -` (space ?X \<times> (space ?Y - ?C)) \<inter> space P = {}"
  proof -
    have "pfut r T \<omega> \<notin> space ?Y - ?C" for \<omega> :: "'n pairpath"
    proof -
      have z: "pfut r T \<omega> 0 = 0" by (rule pfut_zero[OF Tr])
      have "fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0" by (simp add: z)
      then show ?thesis by simp
    qed
    then show ?thesis by auto
  qed
  have "emeasure (ksemi ?Q ?Y \<kappa>) (space ?X \<times> (space ?Y - ?C))
      = emeasure (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) (space ?X \<times> (space ?Y - ?C))"
    unfolding eq ..
  also have "\<dots> = emeasure P (?\<phi> -` (space ?X \<times> (space ?Y - ?C)) \<inter> space P)"
    by (rule emeasure_distr[OF mphi rect])
  also have "\<dots> = 0" unfolding empty by simp
  finally have null: "emeasure (ksemi ?Q ?Y \<kappa>)
      (space ?X \<times> (space ?Y - ?C)) = 0" .
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])
  have null': "emeasure (ksemi ?Q ?Y \<kappa>) (space ?Q \<times> (space ?Y - ?C)) = 0"
    using null spQ by simp
  show ?thesis by (rule AE_kernel_full[OF KQ neQ CY null'])
qed

text \<open>A rational-hypothesis variant of
  @{thm [source] exit_class_diffquot_of_pairs}.  The original demands
  the pairwise bound at all real pairs, which an almost-sure argument cannot
  supply, since only countably many conditions survive the passage from "for
  each, almost surely" to "almost surely, for all".  Its proof already uses
  the hypothesis at rational pairs only, so the weakening is free.\<close>

lemma exit_class_diffquot_of_rational_pairs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and one: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> p \<in> {0..T} \<Longrightarrow> q \<in> {0..T} \<Longrightarrow> p < q \<Longrightarrow>
      AE \<omega> in Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have rat: "AE \<omega> in Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume p: "p \<in> \<rat>"
    show "AE \<omega> in Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume q: "q \<in> \<rat>"
      show "AE \<omega> in Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF p q pq] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

text \<open>The transfer that every full-measure clause needs: an almost-sure
  property of the future under \<open>P\<close> makes the corresponding rectangle
  \<open>ksemi\<close>-null, which is the hypothesis of @{thm [source] AE_kernel_full}.\<close>

lemma ksemi_rect_null_of_AE:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and C: "C \<in> sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and ae: "AE \<omega> in P. pfut r T \<omega> \<in> C"
  shows "emeasure (ksemi (pair_law_of r (pcut r) P)
        (borel_of (mtopology_of
          (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>)
      (space (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric)))
        \<times> (space (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric))) - C)) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have C': "space ?Y - C \<in> sets ?Y" using C by (rule sets.compl_sets)
  have rect: "space ?X \<times> (space ?Y - C) \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using C' by simp
  have preim: "?\<phi> -` (space ?X \<times> (space ?Y - C)) \<inter> space P
      = pfut r T -` (space ?Y - C) \<inter> space P"
    using measurable_space[OF mcut] by auto
  have mset: "pfut r T -` (space ?Y - C) \<inter> space P \<in> sets P"
    by (rule measurable_sets[OF mfut C'])
  have null: "emeasure P (pfut r T -` (space ?Y - C) \<inter> space P) = 0"
  proof -
    have aeS: "AE \<omega> in P. \<omega> \<notin> pfut r T -` (space ?Y - C) \<inter> space P"
      using ae by (auto elim: eventually_mono)
    have setseq: "{\<omega> \<in> space P. \<not> (\<omega> \<notin> pfut r T -` (space ?Y - C) \<inter> space P)}
        = pfut r T -` (space ?Y - C) \<inter> space P" by auto
    show ?thesis using aeS AE_iff_measurable[OF mset setseq] by blast
  qed
  have "emeasure (ksemi (pair_law_of r (pcut r) P) ?Y \<kappa>)
        (space ?X \<times> (space ?Y - C))
      = emeasure (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) (space ?X \<times> (space ?Y - C))"
    unfolding eq ..
  also have "\<dots> = emeasure P (?\<phi> -` (space ?X \<times> (space ?Y - C)) \<inter> space P)"
    by (rule emeasure_distr[OF mphi rect])
  also have "\<dots> = 0" unfolding preim by (rule null)
  finally show ?thesis .
qed

text \<open>@{thm [source] AE_kernel_full} delivers \<open>emeasure (\<kappa> p) C = 1\<close>, while
  the class's clauses are stated as \<open>AE\<close> properties; the bridge from the
  library's real-valued @{thm [source] prob_space.AE_prob_1} goes through
  @{thm [source] finite_measure.emeasure_eq_measure}.\<close>

text \<open>\<open>AE_mem_of_emeasure_1\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

text \<open>Clause (ii) for the conditional law, at rational pairs only, since an
  almost-sure statement survives only countably many conditions, which is
  what @{thm [source] exit_class_diffquot_of_rational_pairs} supplies.\<close>

lemma pfut_rcd_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of r (pcut r) P.
      AE w in \<kappa> p'. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  have Tr: "0 \<le> ?S" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  define C where "C p q = {w :: 'n pairpath \<in> space ?Y.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L}"
    for p q :: real
  have CY: "C p q \<in> sets ?Y" if "p \<in> {0..?S}" "q \<in> {0..?S}" for p q
    unfolding C_def
    using borel_of_closed[OF closedin_diffquot_constraint[OF that]]
    by (simp add: space_borel_of)
  have aeC: "AE \<omega> in P. pfut r T \<omega> \<in> C p q"
    if pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q" for p q
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    with cov show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have rp: "0 \<le> r + p" using r pq by simp
      have rpq: "r + p < r + q" using pq by simp
      have rqT: "r + q \<le> T" using pq by simp
      have "(1 / ((r + q) - (r + p))) *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p)))
          \<in> sconstraint k L" using elim rp rpq rqT by blast
      moreover have "snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)
          = snd (\<omega> (r + q)) - snd (\<omega> (r + p))"
        using pq by (simp add: pfut_apply)
      ultimately have inC: "(1 / (q - p))
          *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L"
        by simp
      have spw: "pfut r T \<omega> \<in> space ?Y"
        using measurable_space[OF mfut] elim by simp
      show ?case unfolding C_def using inC spw by simp
    qed
  qed
  have one: "AE p' in ?Q. emeasure (\<kappa> p') (C p q) = 1"
    if pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q" for p q
  proof -
    have null: "emeasure (ksemi ?Q ?Y \<kappa>)
        (space ?X \<times> (space ?Y - C p q)) = 0"
      by (rule ksemi_rect_null_of_AE
          [OF r rT setsP PS eq CY[OF pq(1) pq(2)] aeC[OF pq]])
    have "emeasure (ksemi ?Q ?Y \<kappa>) (space ?Q \<times> (space ?Y - C p q)) = 0"
      using null spQ by simp
    then show ?thesis by (rule AE_kernel_full[OF KQ neQ CY[OF pq(1) pq(2)]])
  qed
  have rat: "AE p' in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE p' in ?Q. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE p' in ?Q. p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q
          \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
      proof (cases "p \<in> {0..?S} \<and> q \<in> {0..?S} \<and> p < q")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have "AE p' in ?Q. p' \<in> space ?Q" by (rule AE_space)
  with rat show ?thesis
  proof eventually_elim
    case (elim p')
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> p \<in> {0..?S} \<Longrightarrow> q \<in> {0..?S}
        \<Longrightarrow> p < q \<Longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
      and W: "p' \<in> space ?Q" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    show ?case
    proof (rule exit_class_diffquot_of_rational_pairs[OF sK])
      fix p q :: real
      assume pq: "p \<in> \<rat>" "q \<in> \<rat>" "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q"
      have "AE w in \<kappa> p'. w \<in> C p q"
        by (rule AE_mem_of_emeasure_1[OF PK R[OF pq]])
      then show "AE w in \<kappa> p'.
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
        unfolding C_def by (auto elim: eventually_mono)
    qed
  qed
qed

subsection \<open>Unbounded disintegration for the martingale clauses\<close>

text \<open>Clauses (i) and (ii) needed only \<open>emeasure\<close>, so the unconditional
  @{thm [source] nn_integral_ksemi} sufficed.  The martingale clauses need
  \<open>\<integral>\<^sub>A\<^sub>' X\<^sub>i d\<kappa> p'\<close>, and the coordinate process is not bounded on the path
  space, while @{thm [source] integral_ksemi_bounded} assumes a uniform
  bound; the unbounded version is built through the positive and negative
  parts, where @{thm [source] nn_integral_ksemi} applies with no boundedness
  hypothesis.\<close>

lemma AE_integrable_ksemi_section:
  fixes g :: "'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "integrable (ksemi M N Kr) g"
    and ne: "space M \<noteq> {}"
  shows "AE \<omega> in M. integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
proof -
  have gabs: "(\<lambda>p. ennreal (norm (g p))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using gm by measurable
  have fin: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr)) < \<top>"
    using gi by (simp add: integrable_iff_bounded)
  have split: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_ksemi[OF K gabs])
  have minner: "(\<lambda>\<omega>. \<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>))
      \<in> borel_measurable M"
  proof (rule nn_integral_measurable_subprob_algebra2)
    show "(\<lambda>(x, y). ennreal (norm (g (x, y)))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
      using gabs by (simp add: case_prod_unfold)
    show "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N" by (rule measurable_prob_algebraD[OF K])
  qed
  have fin': "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M) \<noteq> \<infinity>"
    using fin split by (simp add: less_top)
  have aefin: "AE \<omega> in M. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF minner fin'])
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aefin show ?thesis
  proof eventually_elim
    fix \<omega> assume z: "(\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
      and w: "\<omega> \<in> space M"
    have sec: "(\<lambda>\<omega>'. g (\<omega>, \<omega>')) \<in> borel_measurable (Kr \<omega>)"
      by (rule measurable_compose[OF ksemi_Pair_measurable[OF K w] gm])
    show "integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      using sec z by (simp add: integrable_iff_bounded less_top)
  qed
qed

text \<open>The unbounded disintegration of Bochner integrals, through the
  positive and negative parts.  @{thm [source] real_lebesgue_integral_def}
  splits both sides into \<open>enn2real\<close> of nonnegative integrals, and on those
  @{thm [source] nn_integral_ksemi} applies with no boundedness hypothesis at
  all.\<close>

lemma integral_ksemi_real:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "integrable (ksemi M N Kr) g"
    and ne: "space M \<noteq> {}"
    and msec: "(\<lambda>\<omega>. \<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  shows "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  define A where "A \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (g (\<omega>, \<omega>')) \<partial>(Kr \<omega>))" for \<omega>
  define B where "B \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (- g (\<omega>, \<omega>')) \<partial>(Kr \<omega>))" for \<omega>
  have Ksub: "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N"
    by (rule measurable_prob_algebraD[OF K])
  have mA: "A \<in> borel_measurable M"
    unfolding A_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have mB: "B \<in> borel_measurable M"
    unfolding B_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have nnA: "(\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
    unfolding A_def by (rule nn_integral_ksemi[OF K]) (use gm in measurable)
  have nnB: "(\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    unfolding B_def by (rule nn_integral_ksemi[OF K]) (use gm in measurable)
  have absfin: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr)) < \<top>"
    using gi by (simp add: integrable_iff_bounded)
  have leA: "(\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr))
      \<le> (\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))"
    by (intro nn_integral_mono ennreal_leI) simp
  have leB: "(\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr))
      \<le> (\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))"
    by (intro nn_integral_mono ennreal_leI) simp
  have finA: "(\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M) < \<top>"
    using leA absfin unfolding nnA[symmetric] by simp
  have finB: "(\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M) < \<top>"
    using leB absfin unfolding nnB[symmetric] by simp
  have aeA: "AE \<omega> in M. A \<omega> \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF mA]) (use finA in \<open>simp add: less_top\<close>)
  have aeB: "AE \<omega> in M. B \<omega> \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF mB]) (use finB in \<open>simp add: less_top\<close>)
  have eqA: "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (A \<omega>)) \<partial>M) = (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
    using aeA by (intro nn_integral_cong_AE) (auto simp: less_top)
  have eqB: "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (B \<omega>)) \<partial>M) = (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    using aeB by (intro nn_integral_cong_AE) (auto simp: less_top)
  have iA: "integrable M (\<lambda>\<omega>. enn2real (A \<omega>))"
    using mA eqA finA by (simp add: integrable_iff_bounded)
  have iB: "integrable M (\<lambda>\<omega>. enn2real (B \<omega>))"
    using mB eqB finB by (simp add: integrable_iff_bounded)
  have intA: "(\<integral>\<omega>. enn2real (A \<omega>) \<partial>M) = enn2real (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (A \<omega>)) \<partial>M) = (\<integral>\<omega>. enn2real (A \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF iA]) simp
    then show ?thesis using eqA by simp
  qed
  have intB: "(\<integral>\<omega>. enn2real (B \<omega>) \<partial>M) = enn2real (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (B \<omega>)) \<partial>M) = (\<integral>\<omega>. enn2real (B \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF iB]) simp
    then show ?thesis using eqB by simp
  qed
  have aesec: "AE \<omega> in M. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))
      = enn2real (A \<omega>) - enn2real (B \<omega>)"
  proof -
    have "AE \<omega> in M. integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      by (rule AE_integrable_ksemi_section[OF K gm gi ne])
    then show ?thesis
    proof eventually_elim
      fix \<omega> assume "integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      then show "(\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) = enn2real (A \<omega>) - enn2real (B \<omega>)"
        unfolding A_def B_def by (rule real_lebesgue_integral_def)
    qed
  qed
  have "(\<integral>p. g p \<partial>(ksemi M N Kr))
      = enn2real (\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr))
        - enn2real (\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr))"
    by (rule real_lebesgue_integral_def[OF gi])
  also have "\<dots> = enn2real (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M) - enn2real (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    unfolding nnA nnB ..
  also have "\<dots> = (\<integral>\<omega>. enn2real (A \<omega>) \<partial>M) - (\<integral>\<omega>. enn2real (B \<omega>) \<partial>M)"
    unfolding intA intB ..
  also have "\<dots> = (\<integral>\<omega>. enn2real (A \<omega>) - enn2real (B \<omega>) \<partial>M)"
    by (rule Bochner_Integration.integral_diff[OF iA iB, symmetric])
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    using aesec msec iA iB
    by (intro Bochner_Integration.integral_cong_AE) auto
  finally show ?thesis .
qed

text \<open>The shape actually needed: the integrand is an indicator of a
  rectangle times a function of the future only.  The \<open>msec\<close> hypothesis of
  @{thm [source] integral_ksemi_real} is then discharged by the AFP's
  fixed-integrand @{thm [source] integral_measurable_subprob_algebra}, and
  the section integral factors as a constant times an integral over the
  kernel.\<close>

lemma integral_ksemi_rect_real:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
    and gi: "integrable (ksemi M N Kr)
        (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
  shows "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p))
        \<partial>(ksemi M N Kr))
      = (\<integral>\<omega>. indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using A A' hm by measurable
  have inner: "(\<integral>\<omega>'. ?g (\<omega>, \<omega>') \<partial>(Kr \<omega>))
      = indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))" for \<omega>
    by simp
  have msec: "(\<lambda>\<omega>. \<integral>\<omega>'. ?g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  proof -
    have "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
      by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
            integral_measurable_subprob_algebra[OF hm']])
    then show ?thesis using A by (simp add: inner)
  qed
  show ?thesis
    using integral_ksemi_real[OF K gm gi ne msec] by (simp add: inner)
qed

text \<open>Two small facts used repeatedly in what follows: the map
  \<open>\<omega> \<mapsto> \<integral> h d(Kr \<omega>)\<close> is measurable when the integrand does not depend on \<open>\<omega>\<close>,
  and every measure is a subalgebra of itself --- the form @{thm [source]
  AE_zero_of_set_integral_zero} gets applied in, its \<open>\<G>\<close>-measurability
  supplied by the kernel rather than by a genuine sub-\<open>\<sigma>\<close>-algebra.\<close>

text \<open>\<open>measurable_integral_kernel\<close> lives in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

text \<open>\<open>subalgebra_self\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

text \<open>At the \<open>ksemi\<close> level: if every rectangle integral of \<open>1\<^sub>A\<^sub>' \<sqdot> h\<close>
  vanishes, then the kernel's own integral of \<open>1\<^sub>A\<^sub>' \<sqdot> h\<close> vanishes almost
  everywhere.  It isolates what the path-specific part has to supply:
  integrability, and the vanishing of the rectangle integrals, which for the
  martingale clauses is @{thm [source] martingale.set_integral_eq} applied to
  \<open>P\<close>.\<close>

lemma AE_kernel_integral_zero:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A': "A' \<in> sets N"
    and gi: "\<And>A. A \<in> sets M \<Longrightarrow> integrable (ksemi M N Kr)
        (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
    and fi: "integrable M (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))"
    and z: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>p. indicator A (fst p)
        * (indicator A' (snd p) * h (snd p)) \<partial>(ksemi M N Kr)) = 0"
  shows "AE \<omega> in M. (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) = 0"
proof -
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have fmeas: "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
    by (rule measurable_integral_kernel[OF K hm'])
  have zz: "set_lebesgue_integral M A
      (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) = 0" if A: "A \<in> sets M" for A
  proof -
    have "set_lebesgue_integral M A (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))
        = (\<integral>\<omega>. indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<partial>M)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p. indicator A (fst p)
        * (indicator A' (snd p) * h (snd p)) \<partial>(ksemi M N Kr))"
      by (rule integral_ksemi_rect_real[OF K ne hm A A' gi[OF A], symmetric])
    also have "\<dots> = 0" by (rule z[OF A])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule AE_zero_of_set_integral_zero[OF subalgebra_self fi fmeas zz])
qed

text \<open>Two path-specific facts the instantiation needs.  First: an increment
  of the rebased future is an increment of the original path, the base point
  cancelling, which is why the martingale property of \<open>P\<close> applies to it
  unchanged.\<close>

text \<open>Second: \<open>pfut\<close> pulls the future's natural filtration back into \<open>P\<close>'s,
  with the clock shifted by \<open>r\<close>, which puts the conditioning set
  \<open>(pcut r) -` A \<inter> (pfut r T) -` A'\<close> into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, where the martingale
  property of \<open>P\<close> applies to it.\<close>

lemma pfut_filtration_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))
        \<rightarrow>\<^sub>M natural_filtration
            (pair_law_of (T - r) (pfut r T) P) 0 (\<lambda>v w. w v) u"
proof -
  let ?S = "T - r"
  let ?FF = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)
      (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have phim: "pfut r T \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsP])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for v
  proof (cases "v \<le> ?S")
    case True
    have m1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v)) \<in> borel_measurable (?FF u)"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r v vu True in auto)
    have m2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable (?FF u)"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r v vu True Tr in auto)
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v) - \<omega> r) \<in> borel_measurable (?FF u)"
      by (rule borel_measurable_diff[OF m1 m2])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. \<omega> (r + v) - \<omega> r)"
      using v True by (auto simp: pfut_apply)
    ultimately show ?thesis by simp
  next
    case False
    then have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. undefined)"
      by (auto simp: pfut_def)
    then show ?thesis by simp
  qed
  have spF: "space (?FF u) = space P" by simp
  show ?thesis
    by (rule phi_filtration_measurable
        [where FF = "\<lambda>u. natural_filtration P 0
            (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)" and u = u,
         OF phim adap spF])
qed

text \<open>The \<open>gi\<close> hypothesis of @{thm [source] AE_kernel_integral_zero}: since
  the semidirect product is a pushforward of \<open>P\<close>, integrability of the
  rectangle integrand reduces to integrability of the future part under \<open>P\<close>,
  the two indicators only shrinking the norm.\<close>

lemma integrable_ksemi_of_distr_rect:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
    and hi: "integrable P (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
  shows "integrable (ksemi M N Kr)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have comp: "integrable P (\<lambda>\<omega>. ?g (\<phi> \<omega>))"
  proof (rule Bochner_Integration.integrable_bound[OF hi])
    show "(\<lambda>\<omega>. ?g (\<phi> \<omega>)) \<in> borel_measurable P"
      by (rule measurable_compose[OF phim gm])
    show "AE \<omega> in P. norm (?g (\<phi> \<omega>)) \<le> norm (h (snd (\<phi> \<omega>)))"
      by (rule AE_I2) (auto simp: indicator_def abs_mult)
  qed
  have "integrable (distr P (M \<Otimes>\<^sub>M N) \<phi>) ?g"
    using comp by (simp add: integrable_distr_eq[OF phim gm])
  then show ?thesis unfolding eq .
qed

text \<open>The \<open>fi\<close> hypothesis: the outer integral of the kernel integral is
  dominated by the \<open>ksemi\<close> integral of \<open>|h|\<close>, because the section integral is
  almost surely bounded in norm by the section's own nonnegative integral,
  where @{thm [source] AE_integrable_ksemi_section} earns its keep.\<close>

lemma integrable_kernel_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A': "A' \<in> sets N"
    and hi: "integrable (ksemi M N Kr) (\<lambda>p. h (snd p))"
  shows "integrable M (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))"
proof -
  have hm2: "(\<lambda>p :: 'a \<times> 'b. h (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using hm by measurable
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have fmeas: "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
    by (rule measurable_integral_kernel[OF K hm'])
  have aei: "AE \<omega> in M. integrable (Kr \<omega>) h"
    using AE_integrable_ksemi_section[OF K hm2 hi ne] by simp
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aei have bnd: "AE \<omega> in M.
      ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
  proof eventually_elim
    fix \<omega> assume i: "integrable (Kr \<omega>) h" and w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have AK: "A' \<in> sets (Kr \<omega>)" using A' sK by simp
    have i2: "integrable (Kr \<omega>) (\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>')"
      using integrable_mult_indicator[OF AK i] by simp
    have "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (indicator A' \<omega>' * h \<omega>')) \<partial>(Kr \<omega>))"
      by (rule integral_norm_bound_ennreal[OF i2])
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
      by (intro nn_integral_mono ennreal_leI) (simp add: indicator_def abs_mult)
    finally show "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))" .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))) \<partial>M)
      \<le> (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_mono_AE[OF bnd])
  also have "\<dots> = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
  proof -
    have gmm: "(\<lambda>p :: 'a \<times> 'b. ennreal (norm (h (snd p))))
        \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using hm2 by measurable
    show "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)
        = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
      using nn_integral_ksemi[OF K gmm] by simp
  qed
  also have "\<dots> < \<top>" using hi by (simp add: integrable_iff_bounded)
  finally show ?thesis using fmeas by (simp add: integrable_iff_bounded)
qed

text \<open>The \<open>z\<close> hypothesis: the rectangle integral over the semidirect product
  is a single set integral over \<open>P\<close>, the two indicators combining into the
  indicator of \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  That set is where the martingale property
  of \<open>P\<close> is applied, so this lemma is the bridge from the kernel back to the
  original law.\<close>

lemma integral_ksemi_rect_of_set_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
  shows "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p))
        \<partial>(ksemi M N Kr))
      = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have "(\<integral>p. ?g p \<partial>(ksemi M N Kr)) = (\<integral>p. ?g p \<partial>(distr P (M \<Otimes>\<^sub>M N) \<phi>))"
    unfolding eq ..
  also have "\<dots> = (\<integral>\<omega>. ?g (\<phi> \<omega>) \<partial>P)" by (rule integral_distr[OF phim gm])
  also have "\<dots> = (\<integral>\<omega>. indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>)) \<partial>P)"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix \<omega> assume "\<omega> \<in> space P"
    then show "?g (\<phi> \<omega>)
        = indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>))"
      by (auto simp: indicator_def mem_Times_iff)
  qed
  also have "\<dots> = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
      (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
    unfolding set_lebesgue_integral_def by simp
  finally show ?thesis .
qed

text \<open>The companion of @{thm [source] pfut_filtration_measurable} for the
  past: together they put \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close> into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, with \<open>A\<close> in the
  past law's filtration and \<open>A'\<close> in the future law's at level \<open>i\<close>, which is
  what @{thm [source] integral_ksemi_rect_of_set_integral} hands to the
  martingale property of \<open>P\<close>.\<close>

lemma pcut_filtration_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pcut r \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration (pair_law_of r (pcut r) P) 0 (\<lambda>v w. w v) u"
proof -
  have phim: "pcut r \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric))"
    by (rule pcut_measurable[OF r rT setsP])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pcut r \<omega> v)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    if "0 \<le> v" and "v \<le> u" for v
    by (rule pcut_adapted[OF r that])
  have spF: "space (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u)
      = space P" by simp
  show ?thesis
    by (rule phi_filtration_measurable
        [where FF = "\<lambda>u. natural_filtration P 0
            (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u" and u = u,
         OF phim adap spF])
qed

subsection \<open>The evaluations generate the path space's Borel sets\<close>

text \<open>@{thm [source] pcut_filtration_measurable} lands in the natural
  filtration of the cut law, while the per-\<open>(i,j,A')\<close> statement quantifies
  the conditioning set over all of \<open>sets ?Q\<close>, since
  @{thm [source] AE_zero_of_set_integral_zero} is applied with \<open>\<G> = ?Q\<close>.  So
  the two must be the same \<open>\<sigma>\<close>-algebra: the coordinate evaluations have to
  generate the Borel sets of the path space.  The proof is metric: the
  distance to a fixed path is decided by the rational times alone, hence
  measurable in the filtration, hence so is every ball, and the balls
  generate since the path space is second countable.\<close>

lemma path_eval_measurable_natural_filtration:
  fixes U v :: real
  assumes v: "v \<in> {0..U}"
  shows "(\<lambda>\<omega> :: 'n::finite pairpath. \<omega> v) \<in> borel_measurable (natural_filtration
      (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
      0 (\<lambda>v \<omega>. \<omega> v) U)"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use v in auto)

lemma sets_natural_filtration_path_subset:
  fixes U u :: real
  shows "sets (natural_filtration
        (borel_of (mtopology_of (path_metric U :: ('n::finite pairpath) metric)))
        0 (\<lambda>v \<omega>. \<omega> v) u)
      \<subseteq> sets (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  have "(\<Union>i\<in>{0..u}.
      {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?B | A. A \<in> sets borel})
      \<subseteq> sets ?B"
  proof clarsimp
    fix i :: real and A :: "((real^'n) \<times> (real^'n^'n)) set"
    assume "A \<in> sets borel"
    then show "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?B \<in> sets ?B"
      by (rule measurable_sets[OF pair_law_eval_measurable[OF refl]])
  qed
  then show ?thesis
    unfolding sets_natural_filtration by (rule sets.sigma_sets_subset)
qed

text \<open>The metric half.  @{thm [source] path_mdist_le_iff} turns the sup
  distance into a condition at the rational times only, countably many, so
  @{thm [source] sets.countable_INT'} applies.  The intersection must be over
  a nonempty index set to keep \<open>\<omega> \<in> space \<FF>\<close> on the \<open>\<supseteq>\<close> side; over an empty
  one it would be the universe.\<close>

lemma mdist_measurable_natural_filtration:
  fixes U :: real and f :: "'n::finite pairpath"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ('n pairpath) metric)"
  shows "(\<lambda>\<omega>. mdist (path_metric U :: ('n pairpath) metric) f \<omega>)
      \<in> borel_measurable (natural_filtration
          (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have Q0: "(0::real) \<in> {0..U} \<inter> \<rat>" using U by simp
  have neQ: "{0..U} \<inter> (\<rat> :: real set) \<noteq> {}" using Q0 by blast
  have cQ: "countable ({0..U} \<inter> (\<rat> :: real set))"
    by (rule countable_subset[OF _ countable_rat]) simp
  show ?thesis
  proof (subst borel_measurable_iff_le, intro allI)
    fix q :: real
    have iff: "mdist ?m f \<omega> \<le> q \<longleftrightarrow> (\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q)"
      if w: "\<omega> \<in> mspace ?m" for \<omega> :: "'n pairpath"
      by (rule path_mdist_le_iff[OF U f w])
    have mem: "{\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q} \<in> sets ?F"
      if t: "t \<in> {0..U} \<inter> \<rat>" for t
    proof -
      have m: "(\<lambda>\<omega> :: 'n pairpath. dist (f t) (\<omega> t)) \<in> borel_measurable ?F"
        using path_eval_measurable_natural_filtration[of t U] t
        by (intro borel_measurable_dist) auto
      show ?thesis using iffD1[OF borel_measurable_iff_le m] by blast
    qed
    have seteq: "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
        = (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
    proof
      show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
          \<subseteq> (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        using iff spF by auto
    next
      show "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
          \<subseteq> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}"
      proof
        fix \<omega> :: "'n pairpath"
        assume w: "\<omega> \<in> (\<Inter>t \<in> {0..U} \<inter> \<rat>.
            {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        have sp: "\<omega> \<in> space ?F" using w Q0 by blast
        then have mw: "\<omega> \<in> mspace ?m" using spF by simp
        have "\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q" using w by blast
        then have "mdist ?m f \<omega> \<le> q" using iff[OF mw] by blast
        then show "\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}" using sp by simp
      qed
    qed
    have "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
        \<in> sets ?F"
      by (rule sets.countable_INT'[OF cQ neQ]) (use mem in auto)
    then show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q} \<in> sets ?F"
      unfolding seteq .
  qed
qed

text \<open>Hence every metric ball is a filtration event.\<close>

lemma mball_in_natural_filtration:
  fixes U :: real and f :: "'n::finite pairpath"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ('n pairpath) metric)"
  shows "Metric_space.mball (mspace (path_metric U :: ('n pairpath) metric))
        (mdist (path_metric U :: ('n pairpath) metric)) f e
      \<in> sets (natural_filtration
          (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have mb: "MS.mball f e = {\<omega> \<in> space ?F. mdist ?m f \<omega> < e}"
  proof (rule set_eqI)
    fix \<omega> :: "'n pairpath"
    have "(\<omega> \<in> MS.mball f e)
        = (f \<in> mspace ?m \<and> \<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (rule MS.in_mball)
    also have "\<dots> = (\<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (simp only: eqTrueI[OF f] simp_thms)
    also have "\<dots> = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})"
      by (simp only: spF mem_Collect_eq)
    finally show "(\<omega> \<in> MS.mball f e)
        = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})" .
  qed
  have "{\<omega> \<in> space ?F. mdist ?m f \<omega> < e} \<in> sets ?F"
    by (rule borel_measurable_less[OF mdist_measurable_natural_filtration[OF U f]
        borel_measurable_const])
  then show ?thesis unfolding mb[symmetric] .
qed

text \<open>And the balls generate: the path space is second countable, so its
  Borel \<open>\<sigma>\<close>-algebra is generated by any base
  (@{thm [source] borel_of_second_countable'}), and the balls are one.\<close>

theorem sets_natural_filtration_path:
  fixes U :: real
  assumes U: "0 \<le> U"
  shows "sets (natural_filtration
        (borel_of (mtopology_of (path_metric U :: ('n::finite pairpath) metric)))
        0 (\<lambda>v \<omega>. \<omega> v) U)
      = sets (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  let ?balls = "{MS.mball a \<epsilon> | a \<epsilon>. a \<in> mspace ?m \<and> \<epsilon> > 0}"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have sub: "?balls \<subseteq> Pow (mspace ?m)" using MS.mball_subset_mspace by auto
  have base: "base_in (mtopology_of ?m) ?balls"
    using MS.mtopology_base_in_balls by (simp add: mtopology_of_def)
  have "?B = sigma (topspace (mtopology_of ?m)) ?balls"
    by (rule borel_of_second_countable'
        [OF second_countable_path_metric base_is_subbase[OF base]])
  then have "sets ?B = sigma_sets (mspace ?m) ?balls"
    using sets_measure_of[OF sub] by simp
  also have "\<dots> \<subseteq> sets ?F"
  proof -
    have "?balls \<subseteq> sets ?F" using mball_in_natural_filtration[OF U] by blast
    then have "sigma_sets (space ?F) ?balls \<subseteq> sets ?F"
      by (rule sets.sigma_sets_subset)
    then show ?thesis using spF by simp
  qed
  finally show ?thesis
    using sets_natural_filtration_path_subset[of U U] by blast
qed

subsection \<open>The conditioning rectangle lives in the past-plus-\<open>i\<close> filtration\<close>

text \<open>What @{thm [source] integral_ksemi_rect_of_set_integral} hands to the
  martingale property of \<open>P\<close> is the set \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  For the martingale
  property to apply at time \<open>r + i\<close> that set must lie in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>: the
  past factor is in \<open>\<F>\<^sub>r\<close> by @{thm [source] sets_natural_filtration_path},
  since \<open>A\<close> ranges over all Borel sets of the \<open>r\<close>-path space and not merely
  over the cut law's natural filtration, and the future factor is in
  \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> by @{thm [source] pfut_filtration_measurable}.\<close>

text \<open>\<open>sets_natural_filtration_mono\<close> and \<open>natural_filtration_cong_space\<close> live
  in @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

lemma pcut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
  shows "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  have sp: "space (pair_law_of r (pcut r) P) = space ?X"
    by (simp add: space_pair_law_of space_borel_of)
  have nfeq: "natural_filtration (pair_law_of r (pcut r) P) 0
        (\<lambda>v w :: 'n pairpath. w v) r
      = natural_filtration ?X 0 (\<lambda>v w. w v) r"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A \<in> sets (natural_filtration (pair_law_of r (pcut r) P) 0
      (\<lambda>v w :: 'n pairpath. w v) r)"
    unfolding nfeq sets_natural_filtration_path[OF r] using A .
  have m: "pcut r \<in> natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r
      \<rightarrow>\<^sub>M natural_filtration (pair_law_of r (pcut r) P) 0 (\<lambda>v w. w v) r"
    by (rule pcut_filtration_measurable[OF r rT setsP])
  have "pcut r -` A \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r)
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    by (rule measurable_sets[OF m AQ])
  then show ?thesis by simp
qed

lemma pfut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  have sp: "space (pair_law_of (T - r) (pfut r T) P) = space ?Y"
    by (simp add: space_pair_law_of space_borel_of)
  have nfeq: "natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
        (\<lambda>v w :: 'n pairpath. w v) i
      = natural_filtration ?Y 0 (\<lambda>v w. w v) i"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A' \<in> sets (natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
      (\<lambda>v w :: 'n pairpath. w v) i)"
    unfolding nfeq using A' .
  have m: "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min i (T - r))
        \<rightarrow>\<^sub>M natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
            (\<lambda>v w. w v) i"
    by (rule pfut_filtration_measurable[OF r rT setsP])
  have mm: "min i (T - r) = i" using iS by simp
  have "pfut r T -` A' \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
    using measurable_sets[OF m AQ] unfolding mm .
  then show ?thesis by simp
qed

lemma rect_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "(\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  have c1: "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r)"
    by (rule pcut_vimage_natural_filtration[OF r rT setsP A])
  have c1': "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
    using c1 sets_natural_filtration_mono[of r "r + i"] i by auto
  have c2: "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
    by (rule pfut_vimage_natural_filtration[OF r rT setsP i iS A'])
  have "(\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      = (pcut r -` A \<inter> space P) \<inter> (pfut r T -` A' \<inter> space P)" by auto
  then show ?thesis using sets.Int[OF c1' c2] by simp
qed

subsection \<open>The martingale increment vanishes under the kernel\<close>

text \<open>The per-\<open>(i,j,A')\<close> statement, chained as follows:
  @{thm [source] AE_kernel_integral_zero} reduces the almost-sure vanishing
  of the kernel integral to the vanishing of every rectangle integral;
  @{thm [source] integral_ksemi_rect_of_set_integral} turns each rectangle
  integral into a set integral over \<open>P\<close>; @{thm [source]
  rect_vimage_natural_filtration} puts that set into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>; and there
  @{thm [source] martingale.set_integral_eq} closes it, with integrability
  from @{thm [source] integrable_ksemi_of_distr_rect} and
  @{thm [source] integrable_kernel_integral}.  The statement is componentwise,
  since the workhorse @{thm [source] AE_zero_of_set_integral_zero} is
  real-valued and \<open>'n\<close> is finite.\<close>

lemma pfut_rcd_X_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w * ((fst (w j) - fst (w i)) $ c) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?h = "\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) $ c"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

  \<comment> \<open>transport \<open>eq\<close> from the Borel algebra to the cut law, which have the
      same sets but are different terms\<close>
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast

  \<comment> \<open>the integrand and its integrability under \<open>P\<close>\<close>
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have hvec: "(\<lambda>w :: 'n pairpath. fst (w j) - fst (w i)) \<in> borel_measurable ?Y"
    by (intro borel_measurable_diff measurable_compose[OF ev pair_fst_borel])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?Y"
      by (intro borel_measurable_inner hvec borel_measurable_const)
    then show ?thesis by (simp add: inner_axis)
  qed
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)))"
    if u: "u \<in> {0..?S}" for u
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + u) T)))"
      by (rule Mg.integrable) (use r u in simp)
    moreover have "min (r + u) T = r + u" using u rT by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>stated as an equation of FUNCTIONS, and consumed by \<open>unfolding\<close>:
      \<open>simp\<close> distributes the \<open>$ c\<close> over the difference and then the rule's own
      left-hand side no longer matches anything\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)"
    by (rule ext) (simp add: pfut_fst[OF j0S] pfut_fst[OF i0S])
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth
        Bochner_Integration.integrable_diff[OF Xint[OF j0S] Xint[OF i0S]]])
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
      by (rule measurable_compose[OF measurable_snd hm])
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) (\<lambda>p. ?h (snd p))"
      unfolding integrable_distr_eq[OF mphi' hm2] by (rule hi)
    then show ?thesis unfolding eq' .
  qed

  \<comment> \<open>the three hypotheses of @{thm [source] AE_kernel_integral_zero}\<close>
  have gi: "integrable (ksemi ?Q ?Y \<kappa>)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p)))"
    if A: "A \<in> sets ?Q" for A
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P
        \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
      by (rule rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'])
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
    proof -
      have "(0 :: real) \<le> r + i" using r i0 by simp
      then have "sets (natural_filtration P 0
          (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i)) \<subseteq> sets P"
        by (rule Mg.sets_F_subset)
      then show ?thesis using Sfilt by blast
    qed
    have mi: "min (r + i) T = r + i" using i0 iS rT by simp
    have mj: "min (r + j) T = r + j" using jS rT by simp
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + i) T)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (min (r + j) T)))"
      by (rule Mg.set_integral_eq[OF Sfilt]) (use r i0 ij in simp_all)
    then have vec: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)))"
      unfolding mi mj .
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)"
      unfolding set_integral_vec_component[OF SP Xint[OF i0S]]
        set_integral_vec_component[OF SP Xint[OF j0S]]
      using vec by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)" if u: "u \<in> {0..?S}" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)"
        by (rule integrable_bounded_linear[OF bounded_linear_vec_nth Xint[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + i)) $ c)"
      using set_integral_diff(2)[OF si[OF j0S] si[OF i0S]] by simp
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP .
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

text \<open>The other hypothesis
  @{thm [source] sigma_finite_filtered_measure.martingale_of_set_integral_eq}
  wants: the coordinate process is \<open>\<kappa> p'\<close>-integrable at almost every \<open>p'\<close>.
  This needs no filtration at all --- only that the section of a
  \<open>ksemi\<close>-integrable function is almost surely integrable, which is
  @{thm [source] AE_integrable_ksemi_section} (generalised above from real
  to Banach values).\<close>

lemma pfut_rcd_X_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w u))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). fst (snd p u)"
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd
        measurable_compose[OF ev pair_fst_borel]])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = (\<lambda>\<omega>. fst (\<omega> (r + u)) - fst (\<omega> r))"
    by (rule ext) (simp add: pfut_fst[OF u])
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + v)))"
    if v: "v \<in> {0..?S}" for v
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + v) T)))"
      by (rule Mg.integrable) (use r v in simp)
    moreover have "min (r + v) T = r + v" using v rT by simp
    ultimately show ?thesis by simp
  qed
  have r0S: "(0::real) \<in> {0..?S}" using rT by simp
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP
      by (rule Bochner_Integration.integrable_diff[OF Xint[OF u]])
         (use Xint[OF r0S] r in simp)
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

subsection \<open>From rational times to all times\<close>

text \<open>Only countably many conditions survive the passage from "for each,
  almost surely" to "almost surely, for all", so the martingale identity
  arrives at rational times only.  Extending it to every real time is not a
  matter of path continuity alone: pointwise convergence does not move a set
  integral, so uniform integrability is needed.  The family in question is a
  family of conditional expectations of the single terminal value, so
  @{thm [source] prob_space.unif_integrable_of_averaging} applies verbatim
  and @{thm [source] finite_measure.vitali_convergence} finishes, both from
  @{theory Continuous_Path_Spaces.Conditional_UI}.

  Larsson--Ruf's argument instead uses a regular conditional distribution
  citing Stroock--Varadhan, Thm 1.3.4; their classical conditioning theorem
  needs none of this because the martingale problem there is stated with
  test functions in \<open>C\<^sub>c\<^sup>\<infinity>\<close>, whose martingales are bounded, while the
  paper's class (1.7) makes \<open>X\<close> itself and \<open>outerp X - Y\<close> the martingales,
  and those are not.\<close>

lemma subalgebra_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric S :: ('n pairpath) metric)))"
  shows "subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  have "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u
      = natural_filtration ?B 0 (\<lambda>v w. w v) u"
    by (rule natural_filtration_cong_space)
       (simp add: sets_eq_imp_space_eq[OF setsQ])
  then have "sets (natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u)
      \<subseteq> sets Q"
    using sets_natural_filtration_path_subset[of S u] setsQ by simp
  then show ?thesis unfolding subalgebra_def by simp
qed

lemma sigma_finite_subalgebra_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes PS: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
  shows "sigma_finite_subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof (rule finite_measure_subalgebra_is_sigma_finite)
  show "finite_measure_subalgebra Q
      (natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u)"
    by (simp add: finite_measure_subalgebra_def
        finite_measure_subalgebra_axioms_def prob_space.finite_measure[OF PS]
        subalgebra_natural_filtration_path[OF setsQ])
qed

theorem integrable_and_set_integral_eq_of_rational_times:
  fixes Q :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
    and i: "i \<in> {0..S}"
  shows "integrable Q (Z i)
      \<and> (\<forall>A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) i).
          set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S))"
proof (cases "i = S")
  case True
  then show ?thesis using ZintS by simp
next
  case False
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  interpret PQ: prob_space Q by (rule PS)
  have iS: "i < S" using i False by simp
  have SS: "S \<in> {0..S}" using S by simp

  \<comment> \<open>rationals decreasing to \<open>i\<close> from above, inside the horizon\<close>
  have ex: "\<exists>q\<in>(\<rat> :: real set). i < q \<and> q < min S (i + inverse (real (Suc n)))"
    for n
  proof (rule Rats_dense_in_real)
    show "i < min S (i + inverse (real (Suc n)))" using iS by simp
  qed
  then obtain q :: "nat \<Rightarrow> real" where qrat: "\<And>n. q n \<in> \<rat>"
    and qgt: "\<And>n. i < q n"
    and qlt: "\<And>n. q n < min S (i + inverse (real (Suc n)))" by metis
  have qle: "q n \<le> S" for n using qlt[of n] by simp
  have q0S: "q n \<in> {0..S}" for n using i qgt[of n] qle[of n] by simp
  have qconv: "q \<longlonglongrightarrow> i"
  proof (rule tendsto_sandwich[of "\<lambda>_. i" _ _ "\<lambda>n. i + inverse (real (Suc n))"])
    show "\<forall>\<^sub>F n in sequentially. i \<le> q n" using qgt by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. q n \<le> i + inverse (real (Suc n))"
      using qlt by (simp add: less_imp_le)
  qed (use LIMSEQ_inverse_real_of_nat_add in auto)

  \<comment> \<open>the filtration facts\<close>
  have subA: "subalgebra Q (?F u)" for u
    by (rule subalgebra_natural_filtration_path[OF setsQ])
  have sfs: "sigma_finite_subalgebra Q (?F u)" for u
    by (rule sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])
  have ZmQ: "Z u \<in> borel_measurable Q" if u: "u \<in> {0..S}" for u
    by (rule measurable_from_subalg[OF subA Zm[OF u]])

  \<comment> \<open>uniform integrability, straight off the averaging form\<close>
  have ui: "unif_integrable Q (\<lambda>n. Z (q n))"
  proof (rule prob_space.unif_integrable_of_averaging[OF PS])
    show "integrable Q (Z S)" by (rule ZintS)
    show "sigma_finite_subalgebra Q (?F (q n))" for n by (rule sfs)
    show "integrable Q (Z (q n))" for n by (rule Zint[OF qrat q0S])
    show "Z (q n) \<in> borel_measurable (?F (q n))" for n by (rule Zm[OF q0S])
    show "set_lebesgue_integral Q B (Z S) = set_lebesgue_integral Q B (Z (q n))"
      if "B \<in> sets (?F (q n))" for n B
      by (rule rat[OF qrat q0S that, symmetric])
  qed

  \<comment> \<open>pointwise convergence, from path continuity\<close>
  have conv: "AE w in Q. (\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w"
  proof (rule AE_I2)
    fix w :: "'n pairpath" assume w: "w \<in> space Q"
    have "((\<lambda>u. Z u w) \<circ> q) \<longlonglongrightarrow> Z i w"
      using Zcont[OF w] q0S i qconv by (simp add: continuous_on_sequentially)
    then show "(\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w" by (simp add: o_def)
  qed

  \<comment> \<open>integrability at the IRRATIONAL time comes free from the same argument\<close>
  have Zi: "integrable Q (Z i)"
    by (rule finite_measure.unif_integrable_limit_integrable
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])
  have vit: "(\<lambda>n. \<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q) \<longlonglongrightarrow> 0"
    by (rule finite_measure.vitali_convergence
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])

  \<comment> \<open>and the set integrals follow the \<open>L\<^sup>1\<close> limit\<close>
  have main: "set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S)"
    if A: "A \<in> sets (?F i)" for A
  proof -
    have AQ: "A \<in> sets Q" using A subA[of i] by (auto simp: subalgebra_def)
    have AF: "A \<in> sets (?F (q n))" for n
      using A sets_natural_filtration_mono[of i "q n"] qgt[of n] by auto
    have bnd: "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
        \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)" for n
    proof -
      have s1: "set_integrable Q A (Z (q n))"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zint[OF qrat q0S]])
      have s2: "set_integrable Q A (Z i)"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zi])
      have dd: "integrable Q (\<lambda>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w))"
        by (rule integrable_mult_indicator[OF AQ
            Bochner_Integration.integrable_diff[OF Zint[OF qrat q0S] Zi]])
      have d1: "integrable Q (\<lambda>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar>)"
        by (rule integrable_abs[OF dd])
      have d2: "integrable Q (\<lambda>w. \<bar>Z (q n) w - Z i w\<bar>)"
        by (intro integrable_abs Bochner_Integration.integrable_diff
            Zint[OF qrat q0S] Zi)
      have "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
          = \<bar>set_lebesgue_integral Q A (Z (q n))
              - set_lebesgue_integral Q A (Z i)\<bar>"
        using rat[OF qrat q0S AF] by simp
      also have "\<dots> = \<bar>\<integral>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w) \<partial>Q\<bar>"
        using set_integral_diff(2)[OF s1 s2]
        unfolding set_lebesgue_integral_def by (simp add: scaleR_diff_right)
      also have "\<dots> \<le> (\<integral>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar> \<partial>Q)"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)"
        by (rule integral_mono[OF d1 d2]) (simp add: indicator_def)
      finally show ?thesis .
    qed
    have "\<bar>set_lebesgue_integral Q A (Z S)
        - set_lebesgue_integral Q A (Z i)\<bar> \<le> 0"
      by (rule LIMSEQ_le_const[OF vit]) (use bnd in blast)
    then show ?thesis by simp
  qed
  show ?thesis using Zi main by blast
qed

subsection \<open>From a generating \<open>\<pi>\<close>-system to the whole sub-\<open>\<sigma>\<close>-algebra\<close>

text \<open>The conditioning set \<open>A'\<close> of @{thm [source] pfut_rcd_X_increment_zero}
  also ranges over a countable family, so what arrives at almost every \<open>p'\<close>
  is the vanishing of the set integral on a \<open>\<pi>\<close>-system only.  Upgrading that
  to the generated \<open>\<sigma>\<close>-algebra is a Dynkin argument: @{thm [source]
  sigma_sets_induct_disjoint} does the induction and @{thm [source]
  lebesgue_integral_countable_add} discharges its disjoint-union case.  The
  lemma is stated for a general measure and generating \<open>\<pi>\<close>-system, and also
  serves clause (iv).\<close>

text \<open>\<open>set_integral_zero_of_generator\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}: passing the
  vanishing of set integrals from a generating \<open>\<pi>\<close>-system to the whole
  generated \<open>\<sigma>\<close>-algebra.\<close>

text \<open>The \<open>\<pi>\<close>-system for the previous lemma: \<open>\<F>\<^sub>s\<close> is the pullback of the
  \<open>s\<close>-path space's Borel sets along \<^const>\<open>pcut\<close>, via @{thm [source]
  natural_filtration_eq_restrict_vimage} and @{thm [source]
  pcut_vimage_natural_filtration}, so second countability of that space
  (@{thm [source] second_countable_path_metric}) hands over a countable base
  with no limit argument.\<close>

lemma sets_natural_filtration_eq_pcut_vimage:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)
      = {pcut s -` B \<inter> space Q | B. B \<in> sets (borel_of (mtopology_of
          (path_metric s :: ('n pairpath) metric)))}"
proof (rule set_eqI, rule iffI)
  let ?Bs = "borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))"
  fix A :: "('n pairpath) set"
  assume "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)"
  then obtain Bs where Bs: "Bs \<in> sets ?Bs"
    and Aeq: "A = (\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}) -` Bs \<inter> space Q"
    by (rule natural_filtration_eq_restrict_vimage[OF setsQ s sT]) blast
  have "A = pcut s -` Bs \<inter> space Q" unfolding Aeq pcut_def ..
  with Bs show "A \<in> {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}" by blast
next
  let ?Bs = "borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))"
  fix A :: "('n pairpath) set"
  assume "A \<in> {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}"
  then obtain B where B: "B \<in> sets ?Bs" and Aeq: "A = pcut s -` B \<inter> space Q"
    by blast
  show "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)"
    unfolding Aeq by (rule pcut_vimage_natural_filtration[OF s sT setsQ B])
qed

text \<open>A countable \<open>\<pi>\<close>-system generating the path space's Borel sets.  A base
  is not \<open>\<pi>\<close>-stable, so close it under finite intersections: still countable,
  and it generates the same \<open>\<sigma>\<close>-algebra because a \<open>\<sigma>\<close>-algebra is closed under
  finite intersections.  The whole space is thrown in so that the complement
  case of @{thm [source] set_integral_zero_of_generator} has something to
  work with.\<close>

lemma countable_Int_stable_generator_path:
  fixes s :: real
  obtains D where
    "countable D"
    and "Int_stable D"
    and "D \<subseteq> Pow (mspace (path_metric s :: ('n::finite pairpath) metric))"
    and "mspace (path_metric s :: ('n pairpath) metric) \<in> D"
    and "sets (borel_of (mtopology_of (path_metric s :: ('n pairpath) metric)))
        = sigma_sets (mspace (path_metric s :: ('n pairpath) metric)) D"
proof -
  let ?m = "path_metric s :: ('n pairpath) metric"
  let ?X = "mtopology_of ?m"
  have sc: "second_countable ?X" by (rule second_countable_path_metric)
  \<comment> \<open>NB the base must not be called \<open>OO\<close>: that name is the relation-composition
      operator and the statement then fails to parse\<close>
  then obtain BB where cB: "countable BB" and bB: "base_in ?X BB"
    using second_countable_base_in by blast
  have Bsub: "U \<subseteq> mspace ?m" if "U \<in> BB" for U
    using base_in_subset[OF bB that] by simp
  define B1 where "B1 = insert (mspace ?m) BB"
  have cB1: "countable B1" unfolding B1_def using cB by simp
  have B1sub: "U \<subseteq> mspace ?m" if "U \<in> B1" for U
    using that Bsub unfolding B1_def by auto
  define FF where "FF = {F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> B1}"
  define D where "D = (\<lambda>F. \<Inter> F) ` FF"

  \<comment> \<open>membership in \<open>D\<close>, introduced and eliminated WITHOUT search: \<open>blast\<close> on
      the existential behind an image diverges (it has to invent the witness)\<close>
  have DE: "\<And>A. A \<in> D \<Longrightarrow> (\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis')
      \<Longrightarrow> thesis'" for thesis'
  proof -
    fix A assume AD: "A \<in> D"
      and W: "\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis'"
    from AD obtain F where Aeq: "A = \<Inter> F" and FF: "F \<in> FF"
      unfolding D_def by (rule imageE)
    from FF have "finite F" "F \<noteq> {}" "F \<subseteq> B1" unfolding FF_def by simp_all
    with Aeq show thesis' by (rule W)
  qed
  have DI: "\<Inter> F \<in> D" if "finite F" "F \<noteq> {}" "F \<subseteq> B1" for F
  proof -
    have "F \<in> FF" unfolding FF_def using that by simp
    then show ?thesis unfolding D_def by (rule image_eqI[OF refl])
  qed

  have cD: "countable D"
    unfolding D_def FF_def
    by (intro countable_image
        countable_subset[OF _ countable_Collect_finite_subset[OF cB1]]) auto
  have Dpow: "D \<subseteq> Pow (mspace ?m)"
  proof
    fix A assume "A \<in> D"
    then show "A \<in> Pow (mspace ?m)"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from F(2) obtain U where U: "U \<in> F" by blast
      have "A \<subseteq> U" unfolding Aeq using U by blast
      moreover have "U \<subseteq> mspace ?m" using U F(3) B1sub by blast
      ultimately show "A \<in> Pow (mspace ?m)" by auto
    qed
  qed
  have Dtop: "mspace ?m \<in> D"
  proof -
    have "\<Inter> {mspace ?m} \<in> D"
      by (rule DI) (simp_all add: B1_def)
    then show ?thesis by simp
  qed
  have DInt: "Int_stable D"
    unfolding Int_stable_def
  proof (intro ballI)
    fix A B assume A: "A \<in> D" and B: "B \<in> D"
    from A show "A \<inter> B \<in> D"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from B show "A \<inter> B \<in> D"
      proof (rule DE)
        fix G assume Beq: "B = \<Inter> G" and G: "finite G" "G \<noteq> {}" "G \<subseteq> B1"
        have "A \<inter> B = \<Inter> (F \<union> G)"
          unfolding Aeq Beq by (simp add: Inter_Un_distrib)
        moreover have "\<Inter> (F \<union> G) \<in> D"
          by (rule DI) (use F G in auto)
        ultimately show "A \<inter> B \<in> D" by simp
      qed
    qed
  qed

  \<comment> \<open>the base already generates, and closing under finite intersections
      changes nothing\<close>
  have Bpow: "BB \<subseteq> Pow (mspace ?m)" using Bsub by auto
  have bsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) BB"
  proof -
    have "borel_of ?X = sigma (topspace ?X) BB"
      by (rule borel_of_second_countable'[OF sc base_is_subbase[OF bB]])
    then have "borel_of ?X = sigma (mspace ?m) BB" by simp
    then show ?thesis using sets_measure_of[OF Bpow] by simp
  qed
  have Deq: "sigma_sets (mspace ?m) D = sigma_sets (mspace ?m) BB"
  proof (rule sigma_sets_eqI)
    fix A assume A: "A \<in> D"
    interpret SA: sigma_algebra "mspace ?m" "sigma_sets (mspace ?m) BB"
      by (rule sigma_algebra_sigma_sets[OF Bpow])
    from A show "A \<in> sigma_sets (mspace ?m) BB"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      have "U \<in> sigma_sets (mspace ?m) BB" if "U \<in> F" for U
        using that F(3) unfolding B1_def by (auto simp: sigma_sets_top)
      then have "(\<Inter>U\<in>F. U) \<in> sigma_sets (mspace ?m) BB"
        by (rule SA.finite_INT[OF F(1) F(2)])
      then show "A \<in> sigma_sets (mspace ?m) BB" unfolding Aeq by simp
    qed
  next
    fix U assume U: "U \<in> BB"
    have "\<Inter> {U} \<in> D" by (rule DI) (use U in \<open>simp_all add: B1_def\<close>)
    then have "U \<in> D" by simp
    then show "U \<in> sigma_sets (mspace ?m) D" by (rule sigma_sets.Basic)
  qed
  have Dsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) D"
    unfolding bsets Deq ..
  show thesis by (rule that[OF cD DInt Dpow Dtop Dsets])
qed

text \<open>And its pullback: the countable \<open>\<pi>\<close>-system for \<open>\<F>\<^sub>s\<close> that the
  conditioning sets of clause (iii)/(iv) range over.\<close>

lemma countable_pi_system_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
  obtains E where
    "countable E"
    and "Int_stable E"
    and "E \<subseteq> Pow (space Q)"
    and "space Q \<in> E"
    and "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s) = sigma_sets (space Q) E"
proof -
  let ?ms = "path_metric s :: ('n pairpath) metric"
  let ?Bs = "borel_of (mtopology_of ?ms)"
  let ?pb = "\<lambda>U. pcut s -` U \<inter> space Q"
  obtain D where cD: "countable D" and DInt: "Int_stable D"
    and Dpow: "D \<subseteq> Pow (mspace ?ms)" and Dtop: "mspace ?ms \<in> D"
    and Dsets: "sets ?Bs = sigma_sets (mspace ?ms) D"
    by (rule countable_Int_stable_generator_path)
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have pin: "pcut s \<in> space Q \<rightarrow> mspace ?ms"
    using restrict_in_mspace[OF s sT] spQ unfolding pcut_def by auto
  define E where "E = ?pb ` D"

  have cE: "countable E" unfolding E_def by (rule countable_image[OF cD])
  have Epow: "E \<subseteq> Pow (space Q)" unfolding E_def by auto
  have Etop: "space Q \<in> E"
  proof -
    have "space Q = ?pb (mspace ?ms)" using pin by auto
    then show ?thesis unfolding E_def by (rule image_eqI[OF _ Dtop])
  qed
  have EInt: "Int_stable E"
    unfolding Int_stable_def
  proof (intro ballI)
    fix A B assume "A \<in> E" "B \<in> E"
    then obtain U V where Aeq: "A = ?pb U" and U: "U \<in> D"
      and Beq: "B = ?pb V" and V: "V \<in> D"
      unfolding E_def by blast
    have "A \<inter> B = ?pb (U \<inter> V)" unfolding Aeq Beq by auto
    moreover have "U \<inter> V \<in> D" using U V DInt by (simp add: Int_stable_def)
    ultimately show "A \<inter> B \<in> E" unfolding E_def by (rule image_eqI)
  qed
  have Egen: "sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)
      = sigma_sets (space Q) E"
  proof -
    have "sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)
        = {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}"
      by (rule sets_natural_filtration_eq_pcut_vimage[OF setsQ s sT])
    also have "\<dots> = {pcut s -` B \<inter> space Q | B. B \<in> sigma_sets (mspace ?ms) D}"
      unfolding Dsets ..
    also have "\<dots> = sigma_sets (space Q) {pcut s -` U \<inter> space Q | U. U \<in> D}"
      by (rule sigma_sets_vimage_commute[OF pin])
    also have "\<dots> = sigma_sets (space Q) E"
      unfolding E_def by (simp add: Setcompr_eq_image)
    finally show ?thesis .
  qed
  show thesis by (rule that[OF cE EInt Epow Etop Egen])
qed

subsection \<open>The martingale property at a fixed law\<close>

text \<open>At a fixed \<open>p'\<close>, adaptedness, integrability, continuity in time, and
  the set-integral identity against the terminal value at rational times
  give the martingale property, via @{thm [source]
  integrable_and_set_integral_eq_of_rational_times} (rational to real) and,
  inside its \<open>rat\<close> hypothesis, @{thm [source] set_integral_zero_of_generator}
  (\<open>\<pi>\<close>-system to \<open>\<F>\<^sub>q\<close>).  The process must be constant past \<open>S\<close> --- the capped
  \<open>\<lambda>u w. w (min u S)\<close> is --- since the filtration is indexed by \<open>[0,\<infinity>)\<close>
  while the path space only knows \<open>[0,S]\<close>.\<close>

lemma martingale_of_rational_set_integral_eq:
  fixes Q :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zm': "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and Zcap: "\<And>u. S \<le> u \<Longrightarrow> Z u = Z S"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>v w. w v)) 0 Z"
proof -
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have fm: "filtered_measure Q ?F 0"
  proof (intro filtered_measure.intro)
    show "subalgebra Q (?F u)" if "(0::real) \<le> u" for u
      by (rule subalgebra_natural_filtration_path[OF setsQ])
    show "sets (?F u) \<subseteq> sets (?F v)" if "(0::real) \<le> u" "u \<le> v" for u v
      by (rule sets_natural_filtration_mono[OF that(2)])
  qed
  interpret SFF: sigma_finite_filtered_measure Q ?F 0
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro fm
        sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])

  \<comment> \<open>integrability AND the identity against the terminal value, both at
      every time in the horizon and both out of the rational data\<close>
  have both: "integrable Q (Z u)
      \<and> (\<forall>A \<in> sets (?F u). set_lebesgue_integral Q A (Z u)
          = set_lebesgue_integral Q A (Z S))"
    if u: "u \<in> {0..S}" for u
    by (rule integrable_and_set_integral_eq_of_rational_times
        [OF S setsQ PS Zm Zint ZintS Zcont rat u])
  have Zall: "integrable Q (Z u)" if u: "0 \<le> u" for u
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis using ZintS by simp
  qed
  have term_eq: "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
    if u: "0 \<le> u" and A: "A \<in> sets (?F u)" for u A
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis using A by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis by (rule arg_cong)
  qed

  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq)
    show "adapted_process Q ?F 0 Z"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure Q ?F 0" by (rule fm)
      show "Z u \<in> borel_measurable (?F u)" if "(0::real) \<le> u" for u
        by (rule Zm'[OF that])
    qed
    show "integrable Q (Z u)" if "(0::real) \<le> u" for u by (rule Zall[OF that])
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> ?F u"
    have AF: "A \<in> sets (?F u)" using A by simp
    have AFv: "A \<in> sets (?F v)"
      using AF sets_natural_filtration_mono[OF uv] by blast
    have "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
      by (rule term_eq[OF u AF])
    also have "\<dots> = set_lebesgue_integral Q A (Z v)"
      by (rule term_eq[OF _ AFv, symmetric]) (use u uv in simp)
    finally show "set_lebesgue_integral Q A (Z u)
        = set_lebesgue_integral Q A (Z v)" .
  qed
qed

subsection \<open>Clause (iii) for the conditional law\<close>

text \<open>The two pointwise facts about the capped coordinate that the fixed-law
  lemma asks for.  Neither depends on the measure: the natural filtration
  only sees \<open>space Q\<close>, and continuity in time is a property of the path.\<close>

lemma eval_component_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath. fst (w (min u S)) $ c)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have f1: "(\<lambda>w :: 'n pairpath. fst (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev pair_fst_borel])
  have "(\<lambda>w :: 'n pairpath. fst (w (min u S)) \<bullet> (axis c 1 :: real^'n))
      \<in> borel_measurable ?F"
    by (intro borel_measurable_inner f1 borel_measurable_const)
  then show ?thesis by (simp add: inner_axis)
qed

lemma eval_component_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)"
proof -
  have "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..S} (\<lambda>u. fst (w u))" by (rule continuous_on_fst)
  then have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)
      = continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule continuous_on_cong[OF refl]) simp
  then show ?thesis using c1 by simp
qed

text \<open>Clause (iii) of (1.7) for the conditional law, assembled from:

  \<^item> @{thm [source] pfut_rcd_X_increment_zero}, supplying one almost-sure
    condition per \<open>(q, A', c)\<close>, countably many since \<open>q\<close> is rational,
    \<open>A'\<close> ranges over the \<open>\<pi>\<close>-system of
    @{thm [source] countable_pi_system_natural_filtration_path}, and \<open>c\<close>
    ranges over the finite index type;
  \<^item> @{thm [source] AE_ball_countable'}, turning "for each, almost surely"
    into "almost surely, for all";
  \<^item> at a fixed good \<open>p'\<close>, @{thm [source] set_integral_zero_of_generator}
    widening the \<open>\<pi>\<close>-system to \<open>\<F>\<^sub>q\<close> and
    @{thm [source] martingale_of_rational_set_integral_eq} widening the
    rational times to all times;
  \<^item> @{thm [source] martingale_vecI}, putting the finitely many components
    back together.\<close>

theorem pfut_rcd_X_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  \<comment> \<open>the countable \<open>\<pi>\<close>-system, one per time\<close>
  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  \<comment> \<open>the countably many almost-sure conditions\<close>
  have step: "AE p' in ?Q.
      (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c :: 'n
    by (rule pfut_rcd_X_increment_zero[OF r rT setsP PS K eq mg _ _ _ A'])
       (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)"
          using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
          by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
             (use step[OF True AG] in blast)
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_X_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))"
    by (rule pfut_rcd_X_integrable[OF r rT setsP PS K eq mg SS])

  \<comment> \<open>and the assembly at each good \<open>p'\<close>\<close>
  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow>
          integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
      and SI: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_vecI)
      fix c :: 'n
      have Zint: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
        if qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}" for q
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        moreover have "min q ?S = q" using q by simp
        ultimately show ?thesis by simp
      qed
      have ZintS: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        then show ?thesis by simp
      qed
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. fst (w (min u ?S)) $ c)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule eval_component_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u
          by (rule eval_component_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
          if "q \<in> \<rat>" "q \<in> {0..?S}" for q by (rule Zint[OF that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
          by (rule ZintS)
        show "continuous_on {0..?S} (\<lambda>u. fst (w (min u ?S)) $ c)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro eval_component_continuous) simp
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            = (\<lambda>w. fst (w (min ?S ?S)) $ c)" if "?S \<le> u" for u
          using that by simp
        \<comment> \<open>the \<open>\<pi>\<close>-system widens to \<open>\<F>\<^sub>q\<close> at this fixed \<open>p'\<close>\<close>
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        have gi: "integrable (\<kappa> p')
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B
                (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)
              = (\<integral>w. indicator B w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')"
          using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w q) $ c) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w (min ?S ?S)) $ c)"
          using q by simp
      qed
    qed
  qed
qed

subsection \<open>Clause (iv) for the conditional law\<close>

text \<open>The clause-(iv) twin of
  @{thm [source] pfut_rcd_X_increment_zero}.  Two differences, both
  bookkeeping: the \<open>P\<close>-side martingale is
  @{thm [source] exit_class_pfut_comp_martingale}, which lives in the
  shifted filtration and is therefore read at times \<open>i, j\<close> rather than
  \<open>r+i, r+j\<close> (the two agree, since \<open>?FP i = \<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> for \<open>i \<le> T-r\<close>); and
  the component is a matrix entry, so the bounded-linear map is
  @{thm [source] bounded_linear_vec_nth} composed with itself.\<close>

lemma pfut_rcd_comp_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w
        * ((outerp (fst (w j)) - snd (w j)
            - (outerp (fst (w i)) - snd (w i))) $ c $ d) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?h = "\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j)
      - (outerp (fst (w i)) - snd (w i))) $ c $ d"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  have mi: "min i ?S = i" using iS by simp
  have mj: "min j ?S = j" using jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast

  \<comment> \<open>the integrand\<close>
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y" for u
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev pair_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j))
        - (outerp (fst (w i)) - snd (w i))) \<in> borel_measurable ?Y"
      by (rule borel_measurable_diff[OF compm compm])
    from measurable_compose[OF this entm] show ?thesis by simp
  qed

  \<comment> \<open>the shifted compensated process, and its integrability under \<open>P\<close>\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (?Zf j \<omega> - ?Zf i \<omega>) $ c $ d)"
    by (rule ext) (simp add: mi mj)
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bl
        Bochner_Integration.integrable_diff[OF Mg.integrable Mg.integrable]])
       (use i0 ij jS in simp_all)
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
      by (rule measurable_compose[OF measurable_snd hm])
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) (\<lambda>p. ?h (snd p))"
      unfolding integrable_distr_eq[OF mphi' hm2] by (rule hi)
    then show ?thesis unfolding eq' .
  qed

  \<comment> \<open>the three hypotheses of @{thm [source] AE_kernel_integral_zero}\<close>
  have gi: "integrable (ksemi ?Q ?Y \<kappa>)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p)))"
    if A: "A \<in> sets ?Q" for A
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets (?FP i)"
      using rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'] mi by simp
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
      using Mg.sets_F_subset[OF i0] Sfilt by blast
    have veq: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf i)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf j)"
      by (rule Mg.set_integral_eq[OF Sfilt i0 ij])
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)"
      unfolding set_integral_mat_component[OF SP Mg.integrable[OF i0]]
        set_integral_mat_component[OF SP Mg.integrable[OF order_trans[OF i0 ij]]]
      using veq by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)" if u: "0 \<le> u" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)"
        by (rule integrable_bounded_linear[OF bl Mg.integrable[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf j \<omega> $ c $ d - ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf i \<omega> $ c $ d)"
      by (rule set_integral_diff(2)[OF si[OF order_trans[OF i0 ij]] si[OF i0]])
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP by simp
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

lemma pfut_rcd_comp_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      outerp (fst (snd p u)) - snd (snd p u)"
  have u0: "0 \<le> u" using u by simp
  have mu: "min u ?S = u" using u by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y"
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev pair_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd compm])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = ?Zf u"
    by (rule ext) (simp add: mu)
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP by (rule Mg.integrable[OF u0])
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

text \<open>The two pointwise facts for the compensated entry, as for the
  coordinate.  Continuity is read off the expanded entry
  \<open>X\<^sub>t\<^sup>c X\<^sub>t\<^sup>d - Y\<^sub>t\<^sup>c\<^sup>d\<close> rather than through \<^const>\<open>outerp\<close>, which keeps everything
  inside products and differences of real continuous functions.\<close>

lemma comp_entry_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath.
        (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))))
      \<in> borel_measurable ?F"
    by (rule measurable_compose
        [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
  have m2: "(\<lambda>w :: 'n pairpath. snd (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev pair_snd_borel])
  have mm: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))) - snd (w (min u S)))
      \<in> borel_measurable ?F"
    by (rule borel_measurable_diff[OF m1 m2])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  from measurable_compose[OF mm entm] show ?thesis by simp
qed

lemma comp_entry_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S}
      (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)"
proof -
  have cw: "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  have cf: "continuous_on {0..S} (\<lambda>u. fst (w u))"
    using cw by (rule continuous_on_fst)
  have cs: "continuous_on {0..S} (\<lambda>u. snd (w u))"
    using cw by (rule continuous_on_snd)
  have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have c2: "continuous_on {0..S} (\<lambda>u. fst (w u) $ d)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have c3: "continuous_on {0..S} (\<lambda>u. snd (w u) $ c $ d)"
    using cs by (rule bounded_linear.continuous_on[OF bl])
  have cc: "continuous_on {0..S}
      (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (intro continuous_on_diff continuous_on_mult c1 c2 c3)
  have "continuous_on {0..S}
        (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      = continuous_on {0..S}
        (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (rule continuous_on_cong[OF refl]) (simp add: outerp_def)
  then show ?thesis using cc by simp
qed

text \<open>Clause (iv) of (1.7) for the conditional law, by the same assembly as
  clause (iii): the index set of components is now a pair, and
  @{thm [source] martingale_matI} does the reassembly.\<close>

theorem pfut_rcd_comp_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  have step: "AE p' in ?Q. (\<integral>w. indicator A' w
      * ((outerp (fst (w ?S)) - snd (w ?S)
          - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c d :: 'n
    by (rule pfut_rcd_comp_increment_zero
        [OF r rT setsP PS K eq mg _ _ _ A']) (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
            - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)" using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
        proof (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
          fix c :: 'n assume "c \<in> (UNIV :: 'n set)"
          show "AE p' in ?Q. \<forall>d \<in> (UNIV :: 'n set).
              (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
            by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
               (use step[OF True AG] in blast)
        qed
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p')
      (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))"
    by (rule pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg SS])

  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c d. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
      and SI: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_matI)
      fix c d :: 'n
      have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
        by (rule bounded_linear_compose[OF bounded_linear_vec_nth
            bounded_linear_vec_nth])
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule comp_entry_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u by (rule comp_entry_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)"
          if q: "q \<in> \<rat>" "q \<in> {0..?S}" for q
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w q)) - snd (w q)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl RI[OF q]])
          moreover have "min q ?S = q" using q by simp
          ultimately show ?thesis by simp
        qed
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl SI])
          then show ?thesis by simp
        qed
        show "continuous_on {0..?S}
            (\<lambda>u. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro comp_entry_continuous) simp
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            = (\<lambda>w. (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          if "?S \<le> u" for u using that by simp
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0
              (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl SI])
        have gi: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
                (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
                - (outerp (fst (w q)) - snd (w q)) $ c $ d)
              = (\<integral>w. indicator B w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')" using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          using q by simp
      qed
    qed
  qed
qed

subsection \<open>The conditional law is in the class\<close>

text \<open>The regular conditional distribution of the rebased future given the
  past lies, at almost every \<open>p'\<close>, in the paper's class (1.7) at the origin,
  from the four clauses: (i) @{thm [source] pfut_rcd_start}, (ii)
  @{thm [source] pfut_rcd_diffquot}, (iii)
  @{thm [source] pfut_rcd_X_martingale}, (iv)
  @{thm [source] pfut_rcd_comp_martingale}.  Under \<open>\<kappa> p'\<close> the starting point
  is a constant, so the shifted law lies in the class at that point and its
  essential infimum is bounded by \<^const>\<open>exit_val\<close> by definition, with no
  localization and no \<open>K\<^sub>\<epsilon>\<close>.\<close>

theorem exit_class_rcd_member:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> exit_class k L T x"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
  shows "AE p' in pair_law_of r (pcut r) P.
      \<kappa> p' \<in> exit_class k L (T - r) 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using P unfolding exit_class_def by blast
  have mgX: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule exit_class_X_martingale[OF P])
  have mgC: "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)) 0
      (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u ?S)))
          - snd (pfut r T \<omega> (min u ?S)))"
    by (rule exit_class_pfut_comp_martingale[OF r rT L0 P])

  from AE_space
    pfut_rcd_start[OF r rT setsP PS K eq]
    pfut_rcd_diffquot[OF r rT setsP PS K eq cov]
    pfut_rcd_X_martingale[OF r rT setsP PS K eq mgX]
    pfut_rcd_comp_martingale[OF r rT setsP PS K eq mgC]
  show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and C1: "emeasure (\<kappa> p') {w \<in> space ?Y. fst (w 0) = 0 \<and> snd (w 0) = 0} = 1"
      and C2: "AE w in \<kappa> p'. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> ?S \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
      and C3: "martingale (\<kappa> p')
          (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v)) 0
          (\<lambda>u w. fst (w (min u ?S)))"
      and C4: "martingale (\<kappa> p')
          (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v)) 0
          (\<lambda>u w. outerp (fst (w (min u ?S))) - snd (w (min u ?S)))"
      by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have C1': "AE w in \<kappa> p'. fst (w 0) = (0 :: real^'n) \<and> snd (w 0) = 0"
      using AE_mem_of_emeasure_1[OF PK C1] by (rule eventually_mono) simp
    show ?case
      unfolding exit_class_def
      by (intro CollectI conjI PK sK C1' C2 C3 C4)
  qed
qed

section \<open>The conditioning statement\<close>

text \<open>Two pathwise facts underlying the conditioning statement for the DPP
  at a deterministic time.  On the survival event the exit time splits at
  \<open>r\<close> (@{thm [source] pexit_split_at_r}), and the second piece is the exit
  time of the rebased future shifted back to where the path actually was,
  which is exactly the object \<^const>\<open>pshift_law\<close> pushes into the class at
  that point.\<close>

text \<open>The class-level step: an almost-sure lower bound on the exit time of
  the shifted law is a lower bound for \<^const>\<open>exit_val\<close> at the shift.  The
  starting point here is a single vector \<open>y\<close>, not a small ball, so the bound
  lands on \<open>exit_val \<dots> y\<close> itself, with no localization needed.\<close>

lemma exit_val_ge_of_AE_pshift:
  fixes R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and y :: "real^'n"
  assumes S: "0 \<le> S"
    and R: "R \<in> exit_class k L S 0"
    and ae: "AE w in R. b \<le> pexit S K (\<lambda>s. fst (pshift S y w s))"
  shows "ennreal b \<le> exit_val k L S K y"
proof -
  have setsR: "sets R = sets (borel_of (mtopology_of
      (path_metric S :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF R])
  have mem: "pshift_law S y R \<in> exit_class k L S y"
    using exit_class_pshift[OF S R] by simp
  have "AE w in R. ennreal b \<le> ennreal (pexit S K (\<lambda>s. fst (pshift S y w s)))"
    using ae by (rule eventually_mono) (rule ennreal_leI)
  then have "ennreal b
      \<le> ess_inf_time R (\<lambda>w. pexit S K (\<lambda>s. fst (pshift S y w s)))"
    unfolding ess_inf_time_def by (rule Sup_upper[OF CollectI])
  also have "\<dots> = ess_inf_time (pshift_law S y R) (\<lambda>w. pexit S K (\<lambda>t. fst (w t)))"
    by (rule ess_inf_time_pshift_law[OF S setsR, symmetric])
  also have "\<dots> \<le> exit_val k L S K y"
    unfolding exit_val_def by (rule SUP_upper) (rule mem)
  finally show ?thesis .
qed

text \<open>Gluing the past back onto the rebased future recovers the path, so the
  hypothesis \<open>c \<le> \<tau>\<^sub>K(\<omega>)\<close> is a statement about
  \<open>(pcut r \<omega>, pfut r T \<omega>)\<close>, and a measurable one, since
  @{thm [source] pglue_measurable} and @{thm [source] pexit_path_measurable}
  compose.  Expressing the coupling through \<^const>\<open>pglue\<close> rather than
  \<^const>\<open>pshift\<close> keeps that measurability off the shelf: \<^const>\<open>pshift\<close> is
  only Lipschitz in the path for a fixed shift, and the joint statement would
  have to be built separately.\<close>

lemma pglue_pcut_pfut:
  fixes \<omega> :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pglue r T (pcut r \<omega>) (pfut r T \<omega>) = \<omega>"
proof (rule ext)
  fix t :: real
  show "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = \<omega> t"
  proof (cases "t \<in> {0..T}")
    case True
    show ?thesis
    proof (cases "t \<le> r")
      case True
      then have tr: "t \<in> {0..r}" using \<open>t \<in> {0..T}\<close> by simp
      have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = pcut r \<omega> t"
        by (rule pglue_le[OF \<open>t \<in> {0..T}\<close> True])
      also have "\<dots> = \<omega> t" by (rule pcut_apply[OF tr])
      finally show ?thesis .
    next
      case False
      then have tr: "r \<le> t" by simp
      have m: "t - r \<in> {0..T - r}" using tr \<open>t \<in> {0..T}\<close> by simp
      have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t
          = pcut r \<omega> r + (pfut r T \<omega> (t - r) - pfut r T \<omega> 0)"
        by (rule pglue_ge[OF \<open>t \<in> {0..T}\<close> tr])
      also have "\<dots> = \<omega> r + (\<omega> (r + (t - r)) - \<omega> r - 0)"
        using r rT by (simp add: pcut_apply pfut_apply[OF m] pfut_zero)
      also have "\<dots> = \<omega> t" by simp
      finally show ?thesis .
    qed
  next
    case False
    then have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = undefined"
      unfolding pglue_def restrict_def by (rule if_not_P)
    moreover have "\<omega> t = undefined"
      using w False by (auto simp: path_metric_def extensional_def)
    ultimately show ?thesis by simp
  qed
qed

lemma pexit_pglue_measurable:
  fixes K :: "(real^'n::finite) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and Kc: "closed K"
  shows "(\<lambda>p. pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))
      \<in> borel_measurable
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  show ?thesis
    by (rule measurable_compose[OF pglue_measurable[OF r rT refl refl]
        pexit_path_measurable[OF T0 Kc refl]])
qed

lemma survival_set_measurable:
  fixes K :: "(real^'n::finite) set"
  assumes r: "0 \<le> r" and Kc: "closed K"
  shows "{p' \<in> space (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric))).
      pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
    \<in> sets (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric)))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  have pm: "(\<lambda>p' :: 'n pairpath. pexit r K (\<lambda>t. fst (p' t)))
      \<in> borel_measurable ?X"
    by (rule pexit_path_measurable[OF r Kc refl])
  have em: "(\<lambda>p' :: 'n pairpath. fst (p' r)) \<in> borel_measurable ?X"
    by (rule measurable_compose
        [OF pair_law_eval_measurable[OF refl] pair_fst_borel])
  have s1: "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r} \<in> sets ?X"
    using pm by measurable
  have s2: "{p' \<in> space ?X. fst (p' r) \<in> K} \<in> sets ?X"
    using em borel_closed[OF Kc] by (simp add: measurable_sets_Collect)
  have "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
      = {p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r}
        \<inter> {p' \<in> space ?X. fst (p' r) \<in> K}" by auto
  then show ?thesis using sets.Int[OF s1 s2] by simp
qed

text \<open>The conditioning statement itself, discharging the hypothesis of
  @{thm [source] exit_val_dpp_le_of_cond} and hence the DPP at a deterministic
  time.  The chain is:

  \<^item> the hypothesis becomes a measurable property of the pair
    \<open>(pcut r \<omega>, pfut r T \<omega>)\<close>, by @{thm [source] pglue_pcut_pfut};
  \<^item> @{thm [source] AE_ksemi} disintegrates it along the r.c.d.;
  \<^item> @{thm [source] exit_class_rcd_member} says the r.c.d. lands in the
    class at the origin, so at a fixed good \<open>p'\<close> the surviving future is a
    class member started at \<open>0\<close> and shifted by the constant \<open>fst (p' r)\<close>;
  \<^item> @{thm [source] exit_val_ge_of_AE_pshift} turns the almost-sure lower bound
    on its exit time into a lower bound for \<^const>\<open>exit_val\<close> at that point.

  No localization and no \<open>K\<^sub>\<epsilon>\<close> are needed: the starting point is a single
  vector.\<close>

theorem exit_val_cond:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
      \<longrightarrow> c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?Surv = "\<lambda>p' :: 'n pairpath. pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K"
  let ?\<Phi> = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?Surv (fst p)
      \<longrightarrow> c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  interpret PP: prob_space P by (rule PS)
  have spP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and eq: "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
    by (rule exit_class_rcd_ksemi[OF r rT setsP PS])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Km measurable_cong_sets[OF setsQ refl] by blast
  have member: "AE p' in ?Q. \<kappa> p' \<in> exit_class k L ?S 0"
    by (rule exit_class_rcd_member[OF r rT L0 P Km eq])

  \<comment> \<open>the hypothesis IS a property of the pair, and a measurable one\<close>
  have aeP: "AE \<omega> in P. ?\<Phi> (?\<phi> \<omega>)"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    with c show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using elim spP by simp
      have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) = \<omega>"
        by (rule pglue_pcut_pfut[OF r rT mw])
      then show ?case using elim by simp
    qed
  qed
  have Pm: "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). ?\<Phi> p} \<in> sets (?X \<Otimes>\<^sub>M ?Y)"
  proof -
    have m1: "(\<lambda>p. pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))
        \<in> borel_measurable (?X \<Otimes>\<^sub>M ?Y)"
      by (rule pexit_pglue_measurable[OF r rT Kc])
    have m2: "{p' \<in> space ?X. ?Surv p'} \<in> sets ?X"
      by (rule survival_set_measurable[OF r Kc])
    have "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). ?Surv (fst p)}
        = fst -` {p' \<in> space ?X. ?Surv p'} \<inter> space (?X \<Otimes>\<^sub>M ?Y)"
      by (auto simp: space_pair_measure)
    then have s1: "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). ?Surv (fst p)} \<in> sets (?X \<Otimes>\<^sub>M ?Y)"
      using measurable_sets[OF measurable_fst m2] by simp
    have s2: "{p \<in> space (?X \<Otimes>\<^sub>M ?Y).
        c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))}
      \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using m1 by measurable
    have "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). ?\<Phi> p}
        = (space (?X \<Otimes>\<^sub>M ?Y) - {p \<in> space (?X \<Otimes>\<^sub>M ?Y). ?Surv (fst p)})
          \<union> {p \<in> space (?X \<Otimes>\<^sub>M ?Y).
              c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))}"
      by auto
    then show ?thesis using sets.Un[OF sets.compl_sets[OF s1] s2] by simp
  qed
  have aeK: "AE p' in ?Q. AE w in \<kappa> p'. ?\<Phi> (p', w)"
  proof -
    have "AE p in distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>. ?\<Phi> p"
      using aeP AE_distr_iff[OF mphi Pm] by blast
    then have ks: "AE p in ksemi ?Q ?Y \<kappa>. ?\<Phi> p" unfolding eq .
    have Pm': "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y). ?\<Phi> p} \<in> sets (?Q \<Otimes>\<^sub>M ?Y)"
    proof -
      have se: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
        by (rule sets_pair_measure_cong[OF setsQ refl])
      have sp: "space (?Q \<Otimes>\<^sub>M ?Y) = space (?X \<Otimes>\<^sub>M ?Y)"
        by (rule sets_eq_imp_space_eq[OF se])
      show ?thesis using Pm unfolding se sp .
    qed
    show ?thesis using ks AE_ksemi[OF KQ Pm'] by blast
  qed

  \<comment> \<open>at a fixed good \<open>p'\<close>\<close>
  have main: "AE p' in ?Q. ?Surv p'
      \<longrightarrow> c \<le> r + enn2real (exit_val k L ?S K (fst (p' r)))"
    using member aeK
  proof eventually_elim
    case (elim p')
    then have RC: "\<kappa> p' \<in> exit_class k L ?S 0"
      and AK: "AE w in \<kappa> p'. ?\<Phi> (p', w)" by blast+
    have z0: "AE w in \<kappa> p'. fst (w 0) = (0 :: real^'n) \<and> snd (w 0) = 0"
      using RC unfolding exit_class_def by blast
    show ?case
    proof (intro impI)
      assume S: "?Surv p'"
      have step: "AE w in \<kappa> p'.
          c - r \<le> pexit ?S K (\<lambda>s. fst (pshift ?S (fst (p' r)) w s))"
        using AK z0
      proof eventually_elim
        case (elim w)
        then have Fw: "?\<Phi> (p', w)" and w0: "w 0 = 0"
          by (auto simp: prod_eq_iff)
        let ?g = "pglue r T p' w"
        have gle: "?g t = p' t" if "t \<in> {0..r}" for t
          using that r rT by (intro pglue_le) auto
        have gsurv: "pexit r K (\<lambda>t. fst (?g t)) = r"
        proof -
          have "pexit r K (\<lambda>t. fst (?g t)) = pexit r K (\<lambda>t. fst (p' t))"
            by (rule pexit_cong_on) (use gle in simp)
          then show ?thesis using S by simp
        qed
        have gend: "fst (?g r) \<in> K" using gle[of r] r S by simp
        have "pexit T K (\<lambda>t. fst (?g t)) = r + pexit ?S K (\<lambda>s. fst (?g (r + s)))"
          by (rule pexit_split_at_r[OF r rT gsurv gend])
        moreover have "pexit ?S K (\<lambda>s. fst (?g (r + s)))
            = pexit ?S K (\<lambda>s. fst (pshift ?S (fst (p' r)) w s))"
        proof (rule pexit_cong_on)
          fix s :: real assume s: "0 \<le> s" "s \<le> ?S"
          then have m: "s \<in> {0..?S}" by simp
          have rt: "r + s \<in> {0..T}" using r s by simp
          have "?g (r + s) = p' r + (w (r + s - r) - w 0)"
            by (rule pglue_ge[OF rt]) (use r s in simp)
          also have "\<dots> = p' r + w s" using w0 by simp
          finally have "?g (r + s) = p' r + w s" .
          moreover have "pshift ?S (fst (p' r)) w s
              = (fst (p' r) + fst (w s), snd (w s))"
            by (rule pshift_apply[OF m])
          ultimately show "fst (?g (r + s))
              = fst (pshift ?S (fst (p' r)) w s)" by simp
        qed
        ultimately have "c \<le> r + pexit ?S K (\<lambda>s. fst (pshift ?S (fst (p' r)) w s))"
          using Fw S by simp
        then show ?case by simp
      qed
      have vge: "ennreal (c - r) \<le> exit_val k L ?S K (fst (p' r))"
        by (rule exit_val_ge_of_AE_pshift[OF Tr RC step])
      have vfin: "exit_val k L ?S K (fst (p' r)) < \<top>"
        using exit_val_neq_top[OF Tr] by (simp add: less_top)
      have "c - r \<le> enn2real (exit_val k L ?S K (fst (p' r)))"
      proof (cases "0 \<le> c - r")
        case True
        have "enn2real (ennreal (c - r))
            \<le> enn2real (exit_val k L ?S K (fst (p' r)))"
          by (rule enn2real_mono[OF vge vfin])
        then show ?thesis using True by simp
      next
        case False
        have "c - r \<le> 0" using False by simp
        also have "(0 :: real) \<le> enn2real (exit_val k L ?S K (fst (p' r)))"
          by simp
        finally show ?thesis .
      qed
      then show "c \<le> r + enn2real (exit_val k L ?S K (fst (p' r)))" by simp
    qed
  qed

  \<comment> \<open>and back to \<open>P\<close>, where the statement only ever mentioned the past\<close>
  have "AE \<omega> in P. ?Surv (pcut r \<omega>)
      \<longrightarrow> c \<le> r + enn2real (exit_val k L ?S K (fst (pcut r \<omega> r)))"
    using main unfolding pair_law_of_def by (rule AE_distrD[OF mcut])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume H: "?Surv (pcut r \<omega>)
        \<longrightarrow> c \<le> r + enn2real (exit_val k L ?S K (fst (pcut r \<omega> r)))"
    have e1: "pexit r K (\<lambda>t. fst (pcut r \<omega> t)) = pexit r K (\<lambda>t. fst (\<omega> t))"
      by (rule pexit_cong_on) (simp add: pcut_apply)
    have e2: "pcut r \<omega> r = \<omega> r" using r by (simp add: pcut_apply)
    show "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
        \<longrightarrow> c \<le> r + enn2real (exit_val k L ?S K (fst (\<omega> r)))"
      using H unfolding e1 e2 .
  qed
qed

section \<open>The dynamic programming principle at a deterministic time\<close>

text \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close> at a deterministic \<open>\<theta> = r\<close>,
  unconditionally.  The \<open>\<ge>\<close> half is @{thm [source] exit_val_dpp_sup_ge}
  (kernel pasting); the \<open>\<le>\<close> half is @{thm [source] exit_val_dpp_le_of_cond}
  with its one hypothesis discharged by @{thm [source] exit_val_cond} via the
  regular conditional distribution.

  Both summands are read off the first piece: \<open>\<theta> \<and> \<tau>\<^sub>K\<close> is the exit time
  capped at \<open>r\<close>, and the indicator \<open>1\<^bsub>{\<theta> \<le> \<tau>\<^sub>K}\<^esub>\<close> is
  \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close>, exact for the capped exit time and
  needing no path continuity.\<close>

section \<open>The conditioning statement at a random time\<close>

text \<open>The conditioning half of the DPP holds at an arbitrary time function
  \<open>s(\<omega>)\<close>, with no stopping-time hypothesis and no measurability of \<open>s\<close>
  whatever: the statement is an almost-sure pathwise one, so all that is
  needed is the deterministic @{thm [source] exit_val_cond} at countably many
  deterministic times, and a pointwise limit at each path.  Measurability of
  \<open>s\<close> only becomes relevant when the result is fed back into an
  \<open>ess_inf_time\<close>.

  Two observations make it work.

  \<^item> Below \<open>c\<close> the survival event is free: if the path has not left \<open>K\<close>
    before \<open>c\<close> and \<open>r < c\<close>, it has not left before \<open>r\<close> either
    (\<open>pexit_surv_of_less\<close> below).  So the conditional conclusion of
    @{thm [source] exit_val_cond} becomes an unconditional one at every
    deterministic time below \<open>c\<close>, and the survival hypothesis disappears
    from the random-time statement too.
  \<^item> Approaching \<open>s(\<omega>)\<close> from above through rationals keeps the residual
    horizon smaller, and \<^const>\<open>exit_val\<close> is monotone in the horizon
    (@{thm [source] exit_val_horizon_mono}), so the bound survives replacing
    \<open>T - t\<^sub>n\<close> by \<open>T - s(\<omega>)\<close>.  What is left is a limit in the space variable,
    which is clause (1), upper semicontinuity
    (@{thm [source] exit_val_usc_unconditional}).  Approaching from below
    would not work: the horizon would grow and monotonicity would point the
    wrong way.\<close>

lemma pexit_surv_of_less:
  fixes f :: "real \<Rightarrow> 'a::polish_space" and K :: "'a set"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" and rT: "r \<le> T" and lt: "r < c"
    and ge: "c \<le> pexit T K f"
  shows "pexit r K f = r \<and> f r \<in> K"
proof -
  have stay: "f t \<in> K" if t: "t \<in> {0..r}" for t
  proof (rule ccontr)
    assume nk: "f t \<notin> K"
    have "pexit T K f \<le> t"
      unfolding pexit_def using T0 t rT nk by (intro etime_le_of_mem) auto
    moreover have "t \<le> r" using t by simp
    ultimately show False using ge lt by simp
  qed
  have empt: "{t. 0 \<le> t \<and> t \<le> r \<and> f t \<in> - K} \<union> {r} = {r}" using stay by auto
  have "pexit r K f = r" unfolding pexit_def etime_def empt by simp
  moreover have "f r \<in> K" using stay r by simp
  ultimately show ?thesis by simp
qed

text \<open>The pointwise core: at a single path, the deterministic bound at
  countably many rational times below \<open>c\<close> gives the bound at an arbitrary
  time \<open>s\<close>, with no measure theory at all.\<close>

lemma exit_val_cond_pointwise:
  fixes \<omega> :: "'n::finite pairpath" and K :: "(real^'n) set"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and pex: "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    and rat: "\<And>c' v. c' \<in> \<rat> \<Longrightarrow> v \<in> \<rat> \<Longrightarrow> c' < c \<Longrightarrow> 0 \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        pexit v K (\<lambda>t. fst (\<omega> t)) = v \<and> fst (\<omega> v) \<in> K \<Longrightarrow>
        c' \<le> v + enn2real (exit_val k L (T - v) K (fst (\<omega> v)))"
    and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "c \<le> s + enn2real (exit_val k L (T - s) K (fst (\<omega> s)))"
proof -
  let ?X = "\<lambda>t. fst (\<omega> t)"
  let ?e = "\<lambda>y. enn2real (exit_val k L (T - s) K y)"
  have cT: "c \<le> T" using pex pexit_le_T[OF T0, of K ?X] by simp
  have e0: "0 \<le> ?e y" for y by simp

  have main: "c' \<le> s + ?e (?X s)" if crat: "c' \<in> \<rat>" and clt: "c' < c" for c'
  proof (cases "c' \<le> s")
    case True
    have "0 \<le> ?e (?X s)" by simp
    with True show ?thesis by argo
  next
    case False
    then have sc: "s < c'" by simp
    have sT': "s < T" using sc clt cT by simp
    have Ts: "0 < T - s" using sT' by simp
    have Tsn: "exit_val k L (T - s) K y \<noteq> \<top>" for y
      by (rule exit_val_neq_top) (use Ts in simp)

    \<comment> \<open>rationals decreasing to \<open>s\<close> from above, all below \<open>c'\<close>\<close>
    have ex: "\<exists>q\<in>(\<rat> :: real set). s < q \<and> q < min c' (s + inverse (real (Suc n)))"
      for n
    proof (rule Rats_dense_in_real)
      show "s < min c' (s + inverse (real (Suc n)))" using sc by simp
    qed
    then obtain t :: "nat \<Rightarrow> real" where trat: "\<And>n. t n \<in> \<rat>"
      and tgt: "\<And>n. s < t n"
      and tlt: "\<And>n. t n < min c' (s + inverse (real (Suc n)))" by metis
    have tc: "t n < c'" for n using tlt[of n] by simp
    have t0: "0 \<le> t n" for n using s0 tgt[of n] by simp
    have tT: "t n \<le> T" for n using tc[of n] clt cT by simp
    have tconv: "t \<longlonglongrightarrow> s"
    proof (rule tendsto_sandwich[of "\<lambda>_. s" _ _ "\<lambda>n. s + inverse (real (Suc n))"])
      show "\<forall>\<^sub>F n in sequentially. s \<le> t n" using tgt by (simp add: less_imp_le)
      show "\<forall>\<^sub>F n in sequentially. t n \<le> s + inverse (real (Suc n))"
        using tlt by (simp add: less_imp_le)
    qed (use LIMSEQ_inverse_real_of_nat_add in auto)

    \<comment> \<open>the deterministic bound at each \<open>t n\<close>, with the horizon enlarged\<close>
    have bound: "c' \<le> t n + ?e (?X (t n))" for n
    proof -
      have surv: "pexit (t n) K ?X = t n \<and> ?X (t n) \<in> K"
        by (rule pexit_surv_of_less[OF T0 t0 tT _ pex]) (use tc[of n] clt in simp)
      have "c' \<le> t n + enn2real (exit_val k L (T - t n) K (?X (t n)))"
        by (rule rat[OF crat trat clt t0 tT surv])
      moreover have "enn2real (exit_val k L (T - t n) K (?X (t n))) \<le> ?e (?X (t n))"
      proof (rule enn2real_mono)
        show "exit_val k L (T - t n) K (?X (t n))
            \<le> exit_val k L (T - s) K (?X (t n))"
          by (rule exit_val_horizon_mono[OF _ _ L1 Kc]) (use tT tgt[of n] in simp_all)
        show "exit_val k L (T - s) K (?X (t n)) < \<top>"
          using Tsn by (simp add: less_top)
      qed
      ultimately show ?thesis by simp
    qed

    \<comment> \<open>and the limit, where clause (1) enters\<close>
    show ?thesis
    proof (rule ccontr)
      assume ng: "\<not> c' \<le> s + ?e (?X s)"
      define d where "d = c' - s - ?e (?X s)"
      have d0: "0 < d" unfolding d_def using ng by simp
      have lt: "exit_val k L (T - s) K (?X s) < ennreal (?e (?X s) + d / 2)"
      proof -
        have "exit_val k L (T - s) K (?X s) = ennreal (?e (?X s))"
          using Tsn by (simp add: less_top)
        also have "\<dots> < ennreal (?e (?X s) + d / 2)"
          using d0 by (simp add: ennreal_lessI)
        finally show ?thesis .
      qed
      have nb: "eventually (\<lambda>y. exit_val k L (T - s) K y
          < ennreal (?e (?X s) + d / 2)) (nhds (?X s))"
        by (rule exit_val_usc_unconditional[OF Ts L1 Kc lt])
      have cw: "continuous_on {0..T} ?X"
        using mspace_path_metricD[OF w] by (rule continuous_on_fst)
      have conv: "(\<lambda>n. ?X (t n)) \<longlonglongrightarrow> ?X s"
      proof -
        have "(?X \<circ> t) \<longlonglongrightarrow> ?X s"
          using cw t0 tT s0 sT tconv by (simp add: continuous_on_sequentially)
        then show ?thesis by (simp add: o_def)
      qed
      have ev1: "\<forall>\<^sub>F n in sequentially. ?e (?X (t n)) \<le> ?e (?X s) + d / 2"
      proof -
        have nn: "0 \<le> ?e (?X s) + d / 2" using d0 e0[of "?X s"] by simp
        have "\<forall>\<^sub>F n in sequentially. exit_val k L (T - s) K (?X (t n))
            < ennreal (?e (?X s) + d / 2)"
          by (rule eventually_compose_filterlim[OF nb conv])
        then show ?thesis
        proof (rule eventually_mono)
          fix n assume lt': "exit_val k L (T - s) K (?X (t n))
              < ennreal (?e (?X s) + d / 2)"
          have "enn2real (exit_val k L (T - s) K (?X (t n)))
              \<le> enn2real (ennreal (?e (?X s) + d / 2))"
            by (rule enn2real_mono[OF less_imp_le[OF lt']]) simp
          then show "?e (?X (t n)) \<le> ?e (?X s) + d / 2"
            unfolding enn2real_ennreal[OF nn] .
        qed
      qed
      have ev2: "\<forall>\<^sub>F n in sequentially. t n < s + d / 2"
        using tconv d0 by (simp add: order_tendsto_iff)
      have "\<forall>\<^sub>F n in sequentially. False"
        using ev1 ev2
      proof eventually_elim
        case (elim n)
        have "c' \<le> t n + ?e (?X (t n))" by (rule bound)
        also have "\<dots> < (s + d / 2) + (?e (?X s) + d / 2)"
          using elim by simp
        also have "\<dots> = c'" unfolding d_def by simp
        finally show ?case by simp
      qed
      then show False by simp
    qed
  qed

  show ?thesis
  proof (rule ccontr)
    assume "\<not> c \<le> s + ?e (?X s)"
    then have "s + ?e (?X s) < c" by simp
    then obtain q :: real where q: "q \<in> \<rat>" "s + ?e (?X s) < q" "q < c"
      using Rats_dense_in_real by blast
    from main[OF q(1) q(3)] q(2) show False by simp
  qed
qed

text \<open>The conditioning statement at a random time.  The time \<open>\<theta>\<close> is an
  arbitrary function of the path: no stopping-time property, no
  measurability, no adaptedness.  The survival hypothesis of
  @{thm [source] exit_val_cond} is gone, since below \<open>c\<close> it is automatic and
  above \<open>c\<close> the conclusion is trivial.\<close>

theorem exit_val_cond_time:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "AE \<omega> in P. c \<le> \<theta> \<omega>
      + enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF P])
  have spP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])

  \<comment> \<open>the deterministic statement at every rational time, for every rational
      threshold below \<open>c\<close> --- countably many instances\<close>
  have ratbound: "AE \<omega> in P. \<forall>c'\<in>(\<rat> :: real set). \<forall>v\<in>(\<rat> :: real set).
      c' < c \<longrightarrow> 0 \<le> v \<longrightarrow> v \<le> T \<longrightarrow>
      (pexit v K (\<lambda>t. fst (\<omega> t)) = v \<and> fst (\<omega> v) \<in> K
        \<longrightarrow> c' \<le> v + enn2real (exit_val k L (T - v) K (fst (\<omega> v))))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix c' :: real assume "c' \<in> \<rat>"
    show "AE \<omega> in P. \<forall>v\<in>(\<rat> :: real set). c' < c \<longrightarrow> 0 \<le> v \<longrightarrow> v \<le> T \<longrightarrow>
        (pexit v K (\<lambda>t. fst (\<omega> t)) = v \<and> fst (\<omega> v) \<in> K
          \<longrightarrow> c' \<le> v + enn2real (exit_val k L (T - v) K (fst (\<omega> v))))"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix v :: real assume "v \<in> \<rat>"
      show "AE \<omega> in P. c' < c \<longrightarrow> 0 \<le> v \<longrightarrow> v \<le> T \<longrightarrow>
          (pexit v K (\<lambda>t. fst (\<omega> t)) = v \<and> fst (\<omega> v) \<in> K
            \<longrightarrow> c' \<le> v + enn2real (exit_val k L (T - v) K (fst (\<omega> v))))"
      proof (cases "c' < c \<and> 0 \<le> v \<and> v \<le> T")
        case True
        then have v0: "0 \<le> v" and vT: "v \<le> T" and cc: "c' < c" by auto
        have c'ae: "AE \<omega> in P. c' \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
          using c by (rule eventually_mono) (use cc in simp)
        show ?thesis
          using exit_val_cond[OF v0 vT L0 Kc P c'ae] by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed

  from AE_space c ratbound show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have W: "\<omega> \<in> space P"
      and pex: "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      and R: "\<And>c' v. c' \<in> \<rat> \<Longrightarrow> v \<in> \<rat> \<Longrightarrow> c' < c \<Longrightarrow> 0 \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
          pexit v K (\<lambda>t. fst (\<omega> t)) = v \<and> fst (\<omega> v) \<in> K \<Longrightarrow>
          c' \<le> v + enn2real (exit_val k L (T - v) K (fst (\<omega> v)))" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spP by simp
    show ?case
      by (rule exit_val_cond_pointwise[OF T0 L1 Kc mw pex R th0 thT])
  qed
qed


(*<*)
end
(*>*)
