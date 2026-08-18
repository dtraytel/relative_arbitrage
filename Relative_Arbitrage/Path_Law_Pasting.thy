section \<open>Glueing laws of paths\<close>

(*<*)
theory Path_Law_Pasting
  imports Path_Stopping_Times
begin

(*>*)

text \<open>What the surgery does to laws rather than to paths: the law of a
  concrete process (\<open>pair_law_of\<close>), the glued law \<open>pglue_law\<close>, the shifted
  law, the kernel glue \<open>kglue_law\<close> that continues a law by a kernel of
  continuations, and the additive glue \<open>aglue_law\<close> that splits a law at a
  stopping time and reassembles it by addition.\<close>

text \<open>A pair process on some filtered probability space pushes forward to
  a pair law, and a martingale for the process's own filtration is a
  martingale for the law's natural filtration --- the tower property, in
  the set-integral form: the natural filtration of the law pulls back into
  the process's filtration, because the process is adapted, and the
  set-integral identity is then the one the process already satisfies over
  the pulled-back event.\<close>

definition pair_law_of ::
  "real \<Rightarrow> ('a \<Rightarrow> 'n::finite pairpath) \<Rightarrow> 'a measure \<Rightarrow> ('n pairpath) measure"
  where "pair_law_of T \<phi> M =
     distr M (path_borel T :: ('n pairpath) measure) \<phi>"

lemma sets_pair_law_of[simp]:
  "sets (pair_law_of T \<phi> M)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding pair_law_of_def by simp

lemma space_pair_law_of:
  "space (pair_law_of T \<phi> M)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pair_law_of_def by (simp add: space_borel_of)

lemma phi_filtration_measurable:
  fixes M :: "'a measure" and \<phi> :: "'a \<Rightarrow> 'n::finite pairpath"
  assumes phim: "\<phi> \<in> M \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    and adap: "\<And>r. 0 \<le> r \<Longrightarrow> r \<le> u \<Longrightarrow> (\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)"
    and spF: "space (FF u) = space M"
  shows "\<phi> \<in> FF u \<rightarrow>\<^sub>M natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?Q = "pair_law_of T \<phi> M"
  have into: "\<phi> \<omega> \<in> space ?Q" if "\<omega> \<in> space M" for \<omega>
    using measurable_space[OF phim that] by (simp add: pair_law_of_def)
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q | A. A \<in> sets borel})
        \<subseteq> Pow (space ?Q)" by auto
    show "\<phi> \<in> space (FF u) \<rightarrow> space ?Q" using spF into by auto
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q" by blast
    have e: "\<phi> -` y \<inter> space (FF u) = (\<lambda>\<omega>. \<phi> \<omega> i) -` A \<inter> space (FF u)"
      using y spF into by auto
    have "(\<lambda>\<omega>. \<phi> \<omega> i) -` A \<inter> space (FF u) \<in> sets (FF u)"
      using i A by (intro measurable_sets[OF adap]) auto
    then show "\<phi> -` y \<inter> space (FF u) \<in> sets (FF u)" unfolding e .
  qed
qed

theorem martingale_pair_law:
  fixes M :: "'a measure" and \<phi> :: "'a \<Rightarrow> 'n::finite pairpath"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes prob: "prob_space M"
    and phim: "\<phi> \<in> M \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    and adap: "\<And>u r. 0 \<le> r \<Longrightarrow> r \<le> u \<Longrightarrow>
        (\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and mg: "martingale M FF 0 (\<lambda>u \<omega>. Z u (\<phi> \<omega>))"
  shows "martingale (pair_law_of T \<phi> M)
      (natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v)) 0 Z"
proof -
  let ?Q = "pair_law_of T \<phi> M"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret MG: martingale M FF 0 "\<lambda>u \<omega>. Z u (\<phi> \<omega>)" by (rule mg)
  interpret P: prob_space M by (rule prob)
  have spF: "space (FF u) = space M" if u: "0 \<le> u" for u
    using MG.subalgebras[OF u] by (simp add: subalgebra_def)
  have prob': "prob_space ?Q"
    unfolding pair_law_of_def by (rule P.prob_space_distr[OF phim])
  have fin': "finite_measure ?Q" using prob' by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF sets_pair_law_of])
  interpret SF: finite_filtered_measure ?Q ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP fin'])
  have ZB: "Z w \<in> borel_measurable ?B" if w: "0 \<le> w" for w
  proof -
    have "Z w \<in> borel_measurable ?Q"
      by (rule measurable_from_subalg[OF SF.subalgebras[OF w] Zm[OF w]])
    then show ?thesis using measurable_cong_sets[OF sets_pair_law_of refl] by blast
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?Q ?G 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?G u)" by (rule Zm[OF u])
    qed
    show "integrable ?Q (Z u)" if u: "0 \<le> u" for u
    proof -
      have "integrable ?Q (Z u) \<longleftrightarrow> integrable M (\<lambda>\<omega>. Z u (\<phi> \<omega>))"
        unfolding pair_law_of_def by (rule integrable_distr_eq[OF phim ZB[OF u]])
      then show ?thesis using MG.integrable[OF u] by simp
    qed
    fix A and u v :: real
    assume A: "A \<in> ?G u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have AB: "A \<in> sets ?B"
      using A SF.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    \<comment> \<open>\<open>adap\<close> has TWO \<open>\<And>\<close>-bound variables, so an \<open>OF\<close> against it produces
        "multiple unifiers"; let the conclusion drive the instantiation.\<close>
    have phiFm: "\<phi> \<in> FF u \<rightarrow>\<^sub>M ?G u"
    proof (rule phi_filtration_measurable[where T = T])
      show "\<phi> \<in> M \<rightarrow>\<^sub>M ?B" by (rule phim)
      show "(\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)" if "0 \<le> r" "r \<le> u" for r
        by (rule adap[OF that])
      show "space (FF u) = space M" by (rule spF[OF uv(1)])
    qed
    have pA: "\<phi> -` A \<inter> space M \<in> FF u"
      using measurable_sets[OF phiFm A] spF[OF uv(1)] by simp
    have key: "set_lebesgue_integral ?Q A (Z w)
        = set_lebesgue_integral M (\<phi> -` A \<inter> space M) (\<lambda>\<omega>. Z w (\<phi> \<omega>))"
      if w: "0 \<le> w" for w
    proof -
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable ?B"
        using AB ZB[OF w] by measurable
      have "set_lebesgue_integral ?Q A (Z w)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>?Q)"
        unfolding set_lebesgue_integral_def ..
      also have "\<dots> = (\<integral>\<omega>. indicat_real A (\<phi> \<omega>) *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        unfolding pair_law_of_def by (rule integral_distr[OF phim gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real (\<phi> -` A \<inter> space M) \<omega>
              *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    show "set_lebesgue_integral ?Q A (Z u) = set_lebesgue_integral ?Q A (Z v)"
      unfolding key[OF uv(1)] key[OF v0]
      by (rule MG.set_integral_eq[OF pA uv(1) uv(2)])
  qed
qed

text \<open>The other plumbing piece the witness needs: the class stops its
  processes at the horizon, so a martingale must be stopped at the
  deterministic time \<open>T\<close>.  \<open>martingale_stopped_const\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

section \<open>The off-diagonal covariation of Brownian motion\<close>

text \<open>The market locale's \<open>coord_Z_martingale\<close> gives only the diagonal
  compensator, but the paper's class needs the whole matrix \<open>outerp X - Y\<close>;
  off the diagonal the compensator is \<open>0\<close>, so what is needed is that
  \<open>W\<^sub>i W\<^sub>j\<close> is a martingale for \<open>i \<noteq> j\<close>.  This follows from independence of
  the coordinates of \<open>bm_paths = Pi\<^sub>M UNIV (\<lambda>_. wiener_pre)\<close>, via
  \<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close>.\<close>

theorem martingale_future_of_past:
  fixes P :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsM: "sets ?M = sets (path_borel T :: ('n pairpath) measure)"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M (path_borel ?S :: ('n pairpath) measure)"
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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      fst (w 0) = 0 \<and> snd (w 0) = 0"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "(path_borel ?S :: ('n pairpath) measure)"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsM: "sets ?M = sets (path_borel T :: ('n pairpath) measure)" using setsP by simp
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

definition pshift_law ::
  "real \<Rightarrow> real^'n::finite \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pshift_law T x Q = distr Q
     (path_borel T :: ('n pairpath) measure)
     (pshift T x)"

lemma sets_pshift_law[simp]:
  "sets (pshift_law T x Q)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding pshift_law_def by simp

lemma space_pshift_law:
  "space (pshift_law T x Q)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pshift_law_def by (simp add: space_borel_of)

lemma prob_space_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "prob_space (pshift_law T x Q)"
proof -
  interpret P: prob_space Q by (rule prob)
  have m: "pshift T x \<in> Q \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  show ?thesis unfolding pshift_law_def by (rule P.prob_space_distr[OF m])
qed

lemma natural_filtration_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)
       = natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)"
  unfolding natural_filtration_def
  using space_of_path_sets[OF setsQ] space_pshift_law[of T x Q] by simp

text \<open>The martingale property transports.  Everything is arranged so that
  the filtration does not move (\<open>natural_filtration_pshift_law\<close>): only the
  measure and the process change, and they change by the same shift, so
  the set-integral identity is the one \<open>Q\<close> already satisfies over the
  shifted event.\<close>

lemma martingale_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and mg: "martingale Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. Z u (pshift T x \<omega>))"
  shows "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0 Z"
proof -
  let ?Q' = "pshift_law T x Q"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret MG: martingale Q ?F 0 "\<lambda>u \<omega>. Z u (pshift T x \<omega>)" by (rule mg)
  have FF: "natural_filtration ?Q' 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) = ?F"
    by (rule natural_filtration_pshift_law[OF setsQ])
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space ?Q' = space Q" using spQ by (simp add: space_pshift_law)
  have setsQ': "sets ?Q' = sets ?B" by simp
  have prob': "prob_space ?Q'" by (rule prob_space_pshift_law[OF T prob setsQ])
  have fin': "finite_measure ?Q'" using prob' by (simp add: prob_space_def)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have SP: "Stochastic_Process.stochastic_process ?Q' (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF sets_pshift_law])
  interpret SF: finite_filtered_measure ?Q' ?F 0
    using Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
      [OF SP fin'] unfolding FF .
  have ZB: "Z w \<in> borel_measurable ?B" if w: "0 \<le> w" for w
  proof -
    have "Z w \<in> borel_measurable ?Q'"
      by (rule measurable_from_subalg[OF SF.subalgebras[OF w] Zm[OF w]])
    then show ?thesis using measurable_cong_sets[OF setsQ' refl] by blast
  qed
  show ?thesis
    unfolding FF
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?Q' ?F 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?F u)" by (rule Zm[OF u])
    qed
    show "integrable ?Q' (Z u)" if u: "0 \<le> u" for u
    proof -
      have "integrable ?Q' (Z u) \<longleftrightarrow> integrable Q (\<lambda>\<omega>. Z u (pshift T x \<omega>))"
        unfolding pshift_law_def by (rule integrable_distr_eq[OF shm ZB[OF u]])
      then show ?thesis using MG.integrable[OF u] by simp
    qed
    fix A and u v :: real
    assume A: "A \<in> ?F u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have AB: "A \<in> sets ?B"
      using A SF.subalgebras[OF uv(1)] setsQ' by (auto simp: subalgebra_def)
    have pA: "pshift T x -` A \<inter> space Q \<in> ?F u"
      using measurable_sets[OF pshift_filtration_measurable[OF setsQ] A] by simp
    have key: "set_lebesgue_integral ?Q' A (Z w)
        = set_lebesgue_integral Q (pshift T x -` A \<inter> space Q)
            (\<lambda>\<omega>. Z w (pshift T x \<omega>))" if w: "0 \<le> w" for w
    proof -
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable ?B"
        using AB ZB[OF w] by measurable
      have "set_lebesgue_integral ?Q' A (Z w)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>?Q')"
        unfolding set_lebesgue_integral_def ..
      also have "\<dots> = (\<integral>\<omega>. indicat_real A (pshift T x \<omega>)
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        unfolding pshift_law_def by (rule integral_distr[OF shm gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real (pshift T x -` A \<inter> space Q) \<omega>
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    show "set_lebesgue_integral ?Q' A (Z u) = set_lebesgue_integral ?Q' A (Z v)"
      unfolding key[OF uv(1)] key[OF v0]
      by (rule MG.set_integral_eq[OF pA uv(1) uv(2)])
  qed
qed

text \<open>\<open>martingale_add\<close>, \<open>martingale_add_const\<close> and \<open>martingale_cong_ge\<close>
  live in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

subsection \<open>Almost-sure statements transport through the shift\<close>

text \<open>The shift is a bijection of the path space with measurable inverse,
  so a null set for \<open>Q\<close> has a null image --- which is what lets the two
  almost-sure clauses of (1.7) be transported without any measurability
  hypothesis on the property itself.\<close>

definition aglue_law :: "real \<Rightarrow> ('n::finite pairpath \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "aglue_law T \<kappa> Q = distr
      (ksemi Q (path_borel T :: ('n pairpath) measure) \<kappa>)
      (path_borel T :: ('n pairpath) measure)
      (\<lambda>p. padd T (fst p) (snd p))"

lemma sets_aglue_law:
  "sets (aglue_law T \<kappa> Q)
    = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding aglue_law_def by (rule sets_distr)

lemma pshift_law_weak_conv_joint:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes T: "0 \<le> T"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (path_borel T :: ('n pairpath) measure)"
    and prR': "prob_space R"
    and setsR': "sets R = sets (path_borel T :: ('n pairpath) measure)"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "mspace (path_metric T :: ('n pairpath) metric)"
  have prS: "prob_space (pshift_law T z (Rm m))" for z m
    by (rule prob_space_pshift_law[OF T prR setsR])
  have fmS: "finite_measure (pshift_law T z (Rm m))" for z m
    using prS[of z m] by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmS': "finite_measure (pshift_law T y R)"
    using prob_space_pshift_law[OF T prR' setsR']
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have MWfin: "mweak_conv_fin ?S (mdist (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R) sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using fmS fmS' by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin ?S "mdist (path_metric T :: ('n pairpath) metric)"
      "\<lambda>m. pshift_law T (ym m) (Rm m)" "pshift_law T y R" sequentially
    by (rule MWfin)
  show ?thesis
    unfolding mtopology_of_def
  proof (rule MW.mweak_conv_eq1[THEN iffD2], intro allI impI)
    fix f :: "'n pairpath \<Rightarrow> real"
    assume uc: "uniformly_continuous_map MW.Self euclidean_metric f"
    assume bnd: "\<exists>B. \<forall>x \<in> ?S. \<bar>f x\<bar> \<le> B"
    from bnd obtain B where B: "\<And>x. x \<in> ?S \<Longrightarrow> \<bar>f x\<bar> \<le> B" by blast
    have cf: "continuous_map ?X euclideanreal f"
      using uniformly_continuous_imp_continuous_map[OF uc]
      by (simp add: mtopology_of_def)
    have fm: "f \<in> borel_measurable ?B"
      using continuous_map_measurable[OF cf] by (simp add: borel_of_euclidean)
    have shiftm: "pshift T z \<in> Rm m \<rightarrow>\<^sub>M ?B" for z m
      using pshift_measurable[OF T] measurable_cong_sets[OF setsR refl] by blast
    have spRm: "space (Rm m) = ?S" for m by (rule space_of_path_sets[OF setsR])
    have hmeas: "(\<lambda>\<omega>. f (pshift T z \<omega>)) \<in> borel_measurable (Rm m)" for z m
      using fm shiftm by simp
    have hbnd: "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" if "\<omega> \<in> space (Rm m)" for z m \<omega>
    proof -
      have "\<omega> \<in> ?S" using that spRm by simp
      then have "pshift T z \<omega> \<in> ?S" by (rule pshift_in_mspace)
      then show ?thesis by (rule B)
    qed
    have intg: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T z \<omega>))" for z m
    proof -
      interpret PR: prob_space "Rm m" by (rule prR)
      have ae: "AE \<omega> in Rm m. norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>"
      proof (intro AE_I2)
        fix \<omega> assume "\<omega> \<in> space (Rm m)"
        then have "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" by (rule hbnd)
        then show "norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>" by simp
      qed
      from PR.integrable_const_bound[OF ae hmeas] show ?thesis .
    qed
    have distr_int: "(\<integral>\<omega>. f \<omega> \<partial>(pshift_law T z S)) = (\<integral>\<omega>. f (pshift T z \<omega>) \<partial>S)"
      if "sets S = sets ?B" for z and S :: "('n pairpath) measure"
    proof -
      have m: "pshift T z \<in> S \<rightarrow>\<^sub>M ?B"
        using pshift_measurable[OF T] measurable_cong_sets[OF that refl] by blast
      show ?thesis unfolding pshift_law_def by (rule integral_distr[OF m fm])
    qed
    have lim2: "(\<lambda>m. \<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
    proof -
      have cshift: "continuous_map ?X ?X (pshift T y)"
        by (rule Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pshift[OF T]])
      have cg: "continuous_map ?X euclideanreal (\<lambda>\<omega>. f (pshift T y \<omega>))"
        using continuous_map_compose[OF cshift cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>x \<in> topspace ?X. \<bar>f (pshift T y x)\<bar> \<le> B'"
      proof (intro exI[of _ B] ballI)
        fix x assume "x \<in> topspace ?X"
        then have "x \<in> ?S" by simp
        then show "\<bar>f (pshift T y x)\<bar> \<le> B" using B pshift_in_mspace by blast
      qed
      show ?thesis using wc[unfolded weak_conv_on_def] cg bg by blast
    qed
    have lim1: "(\<lambda>m. (\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))) \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_I)
      fix e :: real assume e: "0 < e"
      then have e2: "0 < e/2" by simp
      have ucd: "\<forall>ep>0. \<exists>dl>0. \<forall>u\<in>?S. \<forall>v\<in>?S.
          mdist (path_metric T :: ('n pairpath) metric) v u < dl \<longrightarrow> \<bar>f v - f u\<bar> < ep"
        using uc unfolding uniformly_continuous_map_def by (simp add: dist_real_def)
      from ucd e2 obtain del where d0: "0 < del"
        and dd0: "\<forall>u\<in>?S. \<forall>v\<in>?S.
            mdist (path_metric T :: ('n pairpath) metric) v u < del
              \<longrightarrow> \<bar>f v - f u\<bar> < e/2"
        by blast
      have dd: "\<bar>f v - f u\<bar> < e/2" if "u \<in> ?S" and "v \<in> ?S"
        and "mdist (path_metric T :: ('n pairpath) metric) v u < del" for u v
        using dd0 that by blast
      from LIMSEQ_D[OF yc d0] obtain M0
        where M0: "\<And>m. M0 \<le> m \<Longrightarrow> norm (ym m - y) < del" by blast
      have main: "norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" if mM: "M0 \<le> m" for m
      proof -
        interpret PRm: prob_space "Rm m" by (rule prR)
        have cint: "(\<integral>\<omega>. (c::real) \<partial>(Rm m)) = c" for c
          by (simp add: PRm.prob_space)
        have i1: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T (ym m) \<omega>))" by (rule intg)
        have i2: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T y \<omega>))" by (rule intg)
        have idiff: "integrable (Rm m)
            (\<lambda>\<omega>. f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>))"
          using i1 i2 by (rule Bochner_Integration.integrable_diff)
        have icu: "integrable (Rm m) (\<lambda>\<omega>. e/2 :: real)" by (rule PRm.integrable_const)
        have icl: "integrable (Rm m) (\<lambda>\<omega>. - (e/2) :: real)"
          by (rule PRm.integrable_const)
        have key: "\<bar>f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)\<bar> \<le> e/2"
          if w: "\<omega> \<in> space (Rm m)" for \<omega>
        proof -
          have wm: "\<omega> \<in> ?S" using w spRm by simp
          have m1: "pshift T (ym m) \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have m2: "pshift T y \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) \<le> dist (ym m) y"
            by (rule mdist_pshift_pshift[OF T wm])
          also have "\<dots> < del" using M0[OF mM] by (simp add: dist_norm)
          finally have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) < del" .
          from dd[OF m2 m1 this] show ?thesis by simp
        qed
        have ptu: "f (pshift T (ym m) x) - f (pshift T y x) \<le> e/2"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have ptl: "- (e/2) \<le> f (pshift T (ym m) x) - f (pshift T y x)"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have eq: "(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))
            = (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
          by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
        have up: "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m)) \<le> e/2"
        proof -
          have "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))
              \<le> (\<integral>\<omega>. e/2 \<partial>(Rm m))"
            by (rule integral_mono[OF idiff icu ptu])
          also have "\<dots> = e/2" by (rule cint)
          finally show ?thesis .
        qed
        have lo: "- (e/2) \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
        proof -
          have "- (e/2) = (\<integral>\<omega>. - (e/2) \<partial>(Rm m))" by (rule cint[symmetric])
          also have "\<dots> \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
            by (rule integral_mono[OF icl idiff ptl])
          finally show ?thesis .
        qed
        from up lo have "\<bar>(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))\<bar> \<le> e/2"
          unfolding eq by simp
        then show ?thesis using e by simp
      qed
      then show "\<exists>no. \<forall>m\<ge>no. norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" by blast
    qed
    have "(\<lambda>m. ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        \<longlonglongrightarrow> 0 + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
      by (rule tendsto_add[OF lim1 lim2])
    then have "(\<lambda>m. \<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)" by simp
    then show "(\<lambda>m. \<integral>\<omega>. f \<omega> \<partial>(pshift_law T (ym m) (Rm m)))
        \<longlonglongrightarrow> (\<integral>\<omega>. f \<omega> \<partial>(pshift_law T y R))"
      by (simp add: distr_int[OF setsR] distr_int[OF setsR'])
  qed
qed

text \<open>Joint upper semicontinuity of the payoff, in sequential form.  The
  parameter and the law move together; joint continuity of the shift
  carries the pair to a weakly convergent sequence of laws, and
  @{thm [source] ess_inf_pexit_usc} --- which lives on the vector path
  space --- is reached through @{thm [source] Lipschitz_pfst} exactly as
  in \<open>exit_val_attained\<close>.\<close>

lemma prob_space_aglue_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
  shows "prob_space (aglue_law T \<kappa> Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl]
    by (rule padd_measurable_ksemi[OF T0 setsQ])
  show ?thesis
    unfolding aglue_law_def
    by (rule prob_space.prob_space_distr[OF prob_space_ksemi[OF PQ Kp] pm])
qed

text \<open>The transfer lemma: an almost-sure property of the glued law is an
  almost-sure property of the past, then of the continuation.  This is the
  analogue of \<open>AE_kglue_law'\<close>, and as there the base measure
  is kept a free variable.\<close>

lemma AE_aglue_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and Phi: "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Phi> \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
  shows "(AE \<omega> in aglue_law T \<kappa> Q. \<Phi> \<omega>)
      \<longleftrightarrow> (AE p' in Q. AE w in \<kappa> p'. \<Phi> (padd T p' w))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p)"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm2: "?g \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have pm: "?g \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl] by (rule pm2)
  have meas: "{p \<in> space (Q \<Otimes>\<^sub>M ?B). \<Phi> (?g p)} \<in> sets (Q \<Otimes>\<^sub>M ?B)"
  proof -
    have "{p \<in> space (Q \<Otimes>\<^sub>M ?B). \<Phi> (?g p)}
        = ?g -` {\<omega> \<in> space ?B. \<Phi> \<omega>} \<inter> space (Q \<Otimes>\<^sub>M ?B)"
      using measurable_space[OF pm2] by auto
    then show ?thesis using measurable_sets[OF pm2 Phi] by simp
  qed
  have "(AE \<omega> in aglue_law T \<kappa> Q. \<Phi> \<omega>) \<longleftrightarrow> (AE p in ksemi Q ?B \<kappa>. \<Phi> (?g p))"
    unfolding aglue_law_def by (rule AE_distr_iff[OF pm Phi])
  also have "\<dots> \<longleftrightarrow> (AE p' in Q. AE w in \<kappa> p'. \<Phi> (padd T p' w))"
    unfolding AE_ksemi[OF Kp meas] by simp
  finally show ?thesis .
qed

text \<open>Clause (ii) for the glue: the past starts at \<open>x\<close> and the continuation
  at \<open>0\<close>, and \<^const>\<open>padd\<close> adds them.\<close>

lemma AE_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and ae: "AE \<omega> in Q. P (pshift T x \<omega>)"
  shows "AE \<omega> in pshift_law T x Q. P \<omega>"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space (pshift_law T x Q) = space Q"
    using spQ by (simp add: space_pshift_law)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shmQ: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M Q"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ setsQ] by blast
  obtain N1 where N1: "{\<omega> \<in> space Q. \<not> P (pshift T x \<omega>)} \<subseteq> N1"
    and N1z: "emeasure Q N1 = 0" and N1s: "N1 \<in> sets Q"
    by (rule AE_E[OF ae])
  define B where "B = pshift T (- x) -` N1 \<inter> space Q"
  have Bs: "B \<in> sets Q" unfolding B_def by (rule measurable_sets[OF shmQ N1s])
  have pre: "pshift T x -` B \<inter> space Q = N1 \<inter> space Q"
  proof
    show "pshift T x -` B \<inter> space Q \<subseteq> N1 \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath"
      assume "\<omega> \<in> pshift T x -` B \<inter> space Q"
      then have w: "\<omega> \<in> space Q" and n: "pshift T (- x) (pshift T x \<omega>) \<in> N1"
        unfolding B_def by auto
      have "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      with n w show "\<omega> \<in> N1 \<inter> space Q" by simp
    qed
    show "N1 \<inter> space Q \<subseteq> pshift T x -` B \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> N1 \<inter> space Q"
      then have n: "\<omega> \<in> N1" and w: "\<omega> \<in> space Q" by auto
      have e: "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      have "pshift T x \<omega> \<in> space Q" using w spQ by (simp add: pshift_in_mspace)
      then show "\<omega> \<in> pshift T x -` B \<inter> space Q"
        unfolding B_def using n w e by simp
    qed
  qed
  have "emeasure (pshift_law T x Q) B = emeasure Q (pshift T x -` B \<inter> space Q)"
    unfolding pshift_law_def
    by (rule emeasure_distr[OF shm]) (use Bs setsQ in simp)
  also have "\<dots> = emeasure Q (N1 \<inter> space Q)" using pre by simp
  also have "\<dots> = 0"
    using N1z sets.sets_into_space[OF N1s] by (simp add: Int_absorb2)
  finally have Bnull: "emeasure (pshift_law T x Q) B = 0" .
  have sub: "{\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>} \<subseteq> B"
  proof
    fix \<omega>' :: "'n pairpath"
    assume "\<omega>' \<in> {\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>}"
    then have w': "\<omega>' \<in> space Q" and nP: "\<not> P \<omega>'" using spQ' by auto
    have wm: "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w' spQ by simp
    have e: "pshift T x (pshift T (- x) \<omega>') = \<omega>'"
      using pshift_pshift[of T x "- x" \<omega>'] pshift_zero[OF wm] by simp
    have "pshift T (- x) \<omega>' \<in> space Q"
      using wm spQ by (simp add: pshift_in_mspace)
    then have "pshift T (- x) \<omega>' \<in> N1" using N1 nP e by auto
    then show "\<omega>' \<in> B" unfolding B_def using w' by simp
  qed
  have Bn: "B \<in> null_sets (pshift_law T x Q)"
    using Bs Bnull setsQ by (simp add: null_sets_def)
  show ?thesis
    unfolding eventually_ae_filter using sub Bn by blast
qed

subsection \<open>The class is shift-equivariant\<close>

text \<open>The one algebraic input: translating \<open>X\<close> splits the compensated
  process into itself, a term linear in \<open>X\<close>, and a constant --- so it stays
  a martingale.\<close>

lemma aglue_law_start:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and Q0: "AE p' in Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    and K0: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. w 0 = 0"
  shows "AE \<omega> in aglue_law T \<kappa> Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have ev0: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have Phi: "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis
      using measurable_sets[OF ev0 borel_closed[OF closed_singleton]] by simp
  qed
  have z: "(0 :: real) \<in> {0..T}" using T0 by simp
  have "AE p' in Q. AE w in \<kappa> p'.
      fst (padd T p' w 0) = x \<and> snd (padd T p' w 0) = 0"
    using Q0 AE_space
  proof eventually_elim
    case (elim p')
    then have q: "fst (p' 0) = x \<and> snd (p' 0) = 0" and sp: "p' \<in> space Q"
      by blast+
    show ?case using K0[OF sp]
    proof eventually_elim
      case (elim w)
      have "padd T p' w 0 = p' 0 + w 0" by (rule padd_apply[OF z])
      then show ?case using q elim by simp
    qed
  qed
  then show ?thesis
    unfolding AE_aglue_law[OF T0 PQ setsQ Kp Phi] .
qed

text \<open>Clause (iii) for the glue, pathwise.  Exactly the three-case argument
  of the deterministic pasting: below \<open>r\<close> only the past moves, above \<open>r\<close>
  only the continuation, and a straddling pair is a convex combination of
  the two difference quotients --- which is why \<open>sconstraint\<close> had to
  be convex (\<open>sconstraint_convex\<close>) in the first place.\<close>

definition pglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath) measure
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pglue_law r T Q R
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p)) (Q \<Otimes>\<^sub>M R)"

lemma sets_pglue_law[simp]:
  "sets (pglue_law r T Q R)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding pglue_law_def by (rule sets_pair_law_of)

text \<open>\<open>prob_space_pair_measure\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

lemma prob_space_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "prob_space (pglue_law r T Q R)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M R"
    by (rule prob_space_pair_measure[OF PQ PR])
  show ?thesis
    unfolding pglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr[OF pglue_measurable[OF r rT setsQ setsR]])
qed

text \<open>The transfer principle for almost-sure statements: a property of the
  glued path holds \<open>pglue_law\<close>-a.s. as soon as it follows from one
  \<open>Q\<close>-a.s. property of the first piece and one \<open>R\<close>-a.s. property of the
  second.  Both \<open>AE\<close> clauses of (1.7) are of this shape.\<close>

lemma AE_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE \<omega>' in R. B \<omega>'"
    and imp: "\<And>\<omega> \<omega>' :: 'n pairpath.
        \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in pglue_law r T Q R. P \<omega>"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PR: prob_space R by (rule PR)
  interpret PP: pair_prob_space Q R by unfold_locales
  have phim: "?g \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pglue_measurable[OF r rT setsQ setsR])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in pglue_law r T Q R. P \<omega>) = (AE p in ?M. P (?g p))"
    unfolding pglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (?g p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (?g p)} = ?g -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
  proof -
    have RB: "AE \<omega>' in R. B \<omega>'
        \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      using B AE_space[of R] space_of_path_sets[OF setsR]
      by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
      proof (rule eventually_mono[OF RB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega>'
            \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
        with w show "P (?g (\<omega>, \<omega>'))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (?g p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

lemma ess_inf_pexit_pshift_usc:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
    and K :: "(real^'n) set"
  assumes T: "0 < T" and K: "closed K"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (path_borel T :: ('n pairpath) measure)"
    and prR': "prob_space R"
    and setsR': "sets R = sets (path_borel T :: ('n pairpath) measure)"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "Limsup sequentially (\<lambda>m. ess_inf_time (pshift_law T (ym m) (Rm m))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      \<le> ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  let ?Y = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'n) metric)"
  let ?p = "\<lambda>Q :: ('n pairpath) measure. distr Q (borel_of ?Y) (pfst T)"
  have T0: "0 \<le> T" using T by simp
  have wcs: "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule pshift_law_weak_conv_joint[OF T0 yc prR setsR prR' setsR' wc])
  have prS: "prob_space (pshift_law T (ym m) (Rm m))" for m
    by (rule prob_space_pshift_law[OF T0 prR setsR])
  have prS': "prob_space (pshift_law T y R)"
    by (rule prob_space_pshift_law[OF T0 prR' setsR'])
  have wcY: "weak_conv_on (\<lambda>m. ?p (pshift_law T (ym m) (Rm m)))
      (?p (pshift_law T y R)) sequentially ?Y"
    by (rule weak_conv_on_pushforward
        [OF Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pfst[OF T0]] wcs])
  have lim: "Limsup sequentially
        (\<lambda>m. ess_inf_time (?p (pshift_law T (ym m) (Rm m))) (pexit T K))
      \<le> ess_inf_time (?p (pshift_law T y R)) (pexit T K)"
  proof (rule ess_inf_pexit_usc[OF T K wcY])
    show "prob_space (?p (pshift_law T (ym m) (Rm m)))" for m
      by (rule prob_space.prob_space_distr[OF prS pfst_measurable[OF T0]]) simp
    show "prob_space (?p (pshift_law T y R))"
      by (rule prob_space.prob_space_distr[OF prS' pfst_measurable[OF T0]]) simp
  qed
  have eqS: "ess_inf_time (?p S) (pexit T K)
      = ess_inf_time S (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    if "sets S = sets (path_borel T :: ('n pairpath) measure)"
    for S :: "('n pairpath) measure"
    by (rule ess_inf_time_pfst[OF T0 K that])
  show ?thesis using lim by (simp add: eqS)
qed

text \<open>The class packaged exactly as \<open>Metric_space.usc_measurable_selection\<close> consumes it: a compact metric
  space, the metric being L\'evy--Prokhorov restricted to the class, and
  its topology the subspace topology of weak convergence.\<close>

lemma pshift_law_compose:
  fixes Q :: "('n::finite pairpath) measure" and x y :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "pshift_law T y (pshift_law T x Q) = pshift_law T (y + x) Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have shx: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shy: "pshift T y \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
  have "pshift_law T y (pshift_law T x Q) = distr Q ?B (pshift T y \<circ> pshift T x)"
    unfolding pshift_law_def by (rule distr_distr[OF shy shx])
  also have "\<dots> = distr Q ?B (pshift T (y + x))"
    by (rule distr_cong) (auto simp: pshift_pshift)
  finally show ?thesis unfolding pshift_law_def .
qed

lemma pshift_law_pcut:
  fixes R :: "('n::finite pairpath) measure"
  assumes S0: "0 \<le> S" and ST: "S \<le> T"
    and setsR: "sets R = sets (path_borel T :: ('n pairpath) measure)"
  shows "pshift_law S y (pair_law_of S (pcut S) R)
       = pair_law_of S (pcut S) (pshift_law T y R)"
proof -
  let ?BS = "(path_borel S :: ('n pairpath) measure)"
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  have T0: "0 \<le> T" using S0 ST by simp
  have cutR: "pcut S \<in> R \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsR])
  have cutT: "pcut S \<in> ?BT \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST refl])
  have shS: "pshift S y \<in> ?BS \<rightarrow>\<^sub>M ?BS" by (rule pshift_measurable[OF S0])
  have shR: "pshift T y \<in> R \<rightarrow>\<^sub>M ?BT"
    unfolding measurable_cong_sets[OF setsR refl] by (rule pshift_measurable[OF T0])
  have "pshift_law S y (pair_law_of S (pcut S) R)
      = distr (distr R ?BS (pcut S)) ?BS (pshift S y)"
    unfolding pshift_law_def pair_law_of_def ..
  also have "\<dots> = distr R ?BS (pshift S y \<circ> pcut S)"
    by (rule distr_distr[OF shS cutR])
  also have "pshift S y \<circ> pcut S = pcut S \<circ> pshift T y"
    by (rule ext) (simp add: pshift_pcut_comm[OF S0 ST])
  also have "distr R ?BS (pcut S \<circ> pshift T y)
      = distr (distr R ?BT (pshift T y)) ?BS (pcut S)"
    by (rule distr_distr[OF cutT shR, symmetric])
  also have "\<dots> = pair_law_of S (pcut S) (pshift_law T y R)"
    unfolding pshift_law_def pair_law_of_def ..
  finally show ?thesis .
qed

text \<open>The value of a cut law is the value of the original, capped.  This is
  the law-level form of @{thm [source] pexit_min_horizon}, and it is what
  makes one selector serve every horizon.\<close>

lemma pshift_law_zero:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "pshift_law T 0 Q = Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have "pshift_law T 0 Q = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    unfolding pshift_law_def
    by (rule distr_cong) (use spQ in \<open>auto simp: pshift_zero\<close>)
  also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
  finally show ?thesis .
qed

text \<open>Hence the almost-sure transfer is an equivalence, not just an
  implication: apply it at \<open>-x\<close> to the shifted law.\<close>

lemma AE_pshift_law_iff:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "(AE \<omega> in pshift_law T x Q. P \<omega>)
       \<longleftrightarrow> (AE \<omega> in Q. P (pshift T x \<omega>))"
proof
  assume "AE \<omega> in Q. P (pshift T x \<omega>)"
  then show "AE \<omega> in pshift_law T x Q. P \<omega>"
    by (rule AE_pshift_law[OF T setsQ])
next
  let ?Q' = "pshift_law T x Q"
  assume h: "AE \<omega> in ?Q'. P \<omega>"
  have setsQ': "sets ?Q' = sets (path_borel T :: ('n pairpath) measure)" by simp
  have spQ': "space ?Q' = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pshift_law)
  have id': "AE \<omega> in ?Q'. pshift T x (pshift T (- x) \<omega>) = \<omega>"
  proof (rule AE_I2)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space ?Q'"
    then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spQ' by simp
    show "pshift T x (pshift T (- x) \<omega>) = \<omega>"
      using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
  qed
  have h2: "AE \<omega> in ?Q'. P (pshift T x (pshift T (- x) \<omega>))"
    using h id' by eventually_elim simp
  have step: "AE \<omega> in pshift_law T (- x) ?Q'. P (pshift T x \<omega>)"
    by (rule AE_pshift_law[OF T setsQ' h2])
  \<comment> \<open>the measure INSIDE an \<open>AE\<close> cannot be rewritten by simp; \<open>unfolding\<close>
      acts on the chained fact and does it.\<close>
  have eqQ: "pshift_law T (- x) ?Q' = Q"
    using pshift_law_compose[OF T setsQ, of "- x"] pshift_law_zero[OF setsQ]
    by simp
  show "AE \<omega> in Q. P (pshift T x \<omega>)" using step unfolding eqQ .
qed

lemma ess_inf_pexit_pcut_law:
  fixes R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes S0: "0 \<le> S" and ST: "S \<le> T" and PR: "prob_space R"
    and setsR: "sets R = sets (path_borel T :: ('n pairpath) measure)"
    and K: "closed K"
  shows "ess_inf_time (pshift_law S y (pair_law_of S (pcut S) R))
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
      = min (ess_inf_time (pshift_law T y R)
          (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)"
proof -
  let ?BS = "(path_borel S :: ('n pairpath) measure)"
  let ?P = "pshift_law T y R"
  have T0: "0 \<le> T" using S0 ST by simp
  have setsP: "sets ?P = sets (path_borel T :: ('n pairpath) measure)" by simp
  have PP: "prob_space ?P" by (rule prob_space_pshift_law[OF T0 PR setsR])
  have cutm: "pcut S \<in> ?P \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsP])
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BS"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?BS"
      by (rule measurable_compose[OF pfst_measurable[OF S0 refl]
            pexit_measurable[OF S0 K]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have mset: "{\<omega> \<in> space ?BS. c \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))}
      \<in> sets ?BS" for c :: ennreal using taum by measurable
  have "ess_inf_time (pshift_law S y (pair_law_of S (pcut S) R))
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
      = ess_inf_time (pair_law_of S (pcut S) ?P)
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))"
    unfolding pshift_law_pcut[OF S0 ST setsR] ..
  also have "\<dots> = ess_inf_time ?P (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
    unfolding pair_law_of_def by (rule ess_inf_time_distr[OF cutm mset])
  also have "\<dots> = ess_inf_time ?P (\<lambda>\<omega>. min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
  proof (rule arg_cong[where f = "ess_inf_time ?P"], rule ext)
    fix \<omega> :: "'n pairpath"
    have "pexit S K (\<lambda>t. fst (pcut S \<omega> t)) = pexit S K (\<lambda>t. fst (\<omega> t))"
      by (rule pexit_cong_on) (auto simp: pcut_apply)
    then show "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
        = min (pexit T K (\<lambda>t. fst (\<omega> t))) S"
      using pexit_min_horizon[OF S0 ST, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  also have "\<dots> = min (ess_inf_time ?P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      (ennreal S)" by (rule ess_inf_time_min_const[OF PP])
  finally show ?thesis .
qed

subsection \<open>The selector\<close>

text \<open>One selector, every horizon.  \<open>Sel (s,y)\<close> is the \<^const>\<open>pembed\<close>-image of
  the horizon-\<open>T\<close> optimizer started at \<open>y\<close>, cut back to \<open>T-s\<close>; it lands in
  \<open>pdelclass\<close>, is jointly measurable in \<open>(s,y)\<close> as a Giry kernel, and
  re-basing it attains \<^term>\<open>exit_val k L (T - s) K y\<close>.  This is the
  continuation \<open>exit_class_aglue\<close> consumes for the
  additive glue.\<close>

lemma ess_inf_time_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "ess_inf_time (pshift_law T x Q) g
       = ess_inf_time Q (\<lambda>\<omega>. g (pshift T x \<omega>))"
proof -
  have "{c. AE \<omega> in pshift_law T x Q. c \<le> ennreal (g \<omega>)}
      = {c. AE \<omega> in Q. c \<le> ennreal (g (pshift T x \<omega>))}"
    by (intro Collect_cong) (rule AE_pshift_law_iff[OF T setsQ])
  then show ?thesis unfolding ess_inf_time_def by simp
qed

subsection \<open>The exit functional of (1.6) is the shifted exit time\<close>

text \<open>Both sides are the same infimum: the times range over \<open>{0..T}\<close>, and
  there \<open>fst (pshift T x \<omega> r) = x + fst (\<omega> r) = fst ((x,0) + \<omega> r)\<close>.  No
  path-space membership is needed.\<close>

lemma natural_filtration_pcut:
  fixes P :: "('n::finite pairpath) measure"
  assumes u: "0 \<le> u" and uS: "u \<le> S"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
  shows "{pcut S -` A \<inter> space P | A.
        A \<in> sets (natural_filtration (pair_law_of S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v) u)}
      = sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u)"
proof -
  let ?Q = "pair_law_of S (pcut S) P"
  let ?g = "\<lambda>N. (\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> N | B. B \<in> sets borel})"
  have S0: "0 \<le> S" using u uS by simp
  have spP: "space P = ipath"
    using setsP by (metis sets_eq_imp_space_eq space_ipath_space)
  have spQ: "space ?Q = mspace (path_metric S :: ('n pairpath) metric)"
    by (rule space_pair_law_of)
  have into': "pcut S \<omega> \<in> space ?Q" if "\<omega> \<in> space P" for \<omega>
    using that spP spQ restrict_ipath_mspace[OF S0] by (simp add: pcut_def)
  then have into: "pcut S \<in> space P \<rightarrow> space ?Q" by blast
  have pre: "pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P
      = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space P" if i: "i \<in> {0..u}" for i B
  proof -
    have iS: "i \<in> {0..S}" using i uS by auto
    show ?thesis using into' by (auto simp: pcut_apply[OF iS])
  qed
  have geneq: "{pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)} = ?g (space P)"
  proof (rule set_eqI)
    fix C :: "('n pairpath) set"
    show "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)} \<longleftrightarrow> C \<in> ?g (space P)"
    proof
      assume "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}"
      then obtain i B where i: "i \<in> {0..u}" and B: "B \<in> sets borel"
        and C: "C = pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P"
        by blast
      show "C \<in> ?g (space P)" unfolding C pre[OF i] using i B by blast
    next
      assume "C \<in> ?g (space P)"
      then obtain i B where i: "i \<in> {0..u}" and B: "B \<in> sets borel"
        and C: "C = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space P" by blast
      have "C = pcut S -` ((\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q) \<inter> space P"
        unfolding C by (rule pre[OF i, symmetric])
      moreover have "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` B \<inter> space ?Q \<in> ?g (space ?Q)"
        using i B by blast
      ultimately show "C \<in> {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}" by blast
    qed
  qed
  have "{pcut S -` A \<inter> space P | A. A \<in> sets (natural_filtration ?Q 0 (\<lambda>v \<omega>. \<omega> v) u)}
      = sigma_sets (space P) {pcut S -` A \<inter> space P | A. A \<in> ?g (space ?Q)}"
    unfolding sets_natural_filtration by (rule sigma_sets_vimage_commute[OF into])
  also have "\<dots> = sigma_sets (space P) (?g (space P))" unfolding geneq ..
  finally show ?thesis unfolding sets_natural_filtration .
qed

text \<open>Hence a process whose restrictions are martingales at every horizon is
  a martingale on the half-line: the set-integral identity at \<open>u \<le> v\<close> is the
  one the restriction at \<open>v\<close> already satisfies.\<close>

definition kglue_law' :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "kglue_law' r T Kr Q
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p))
         (ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr)"

theorem kglue_law'_rcd_eq:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
  shows "kglue_law' r T \<kappa> (pair_law_of r (pcut r) P) = P"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). pglue r T (fst p) (snd p)"
  have spP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have gm: "?g \<in> ?X \<Otimes>\<^sub>M ?Y \<rightarrow>\<^sub>M ?B"
    by (rule pglue_measurable[OF r rT refl refl])
  have "kglue_law' r T \<kappa> ?Q = distr (ksemi ?Q ?Y \<kappa>) ?B ?g"
    unfolding kglue_law'_def pair_law_of_def ..
  also have "\<dots> = distr (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) ?B ?g" unfolding eq ..
  also have "\<dots> = distr P ?B (?g \<circ> ?\<phi>)" by (rule distr_distr[OF gm mphi])
  also have "\<dots> = distr P ?B (\<lambda>\<omega>. \<omega>)"
  proof (rule distr_cong[OF refl refl])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
    then have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spP by simp
    show "(?g \<circ> ?\<phi>) \<omega> = \<omega>" by (simp add: pglue_pcut_pfut[OF r rT mw])
  qed
  also have "\<dots> = P" by (rule distr_id2[OF setsP[symmetric]])
  finally show ?thesis .
qed

text \<open>The other branch needs a repair, and the repair needs the class to be
  a measurable set of laws.  It is: the class is compact in the weak
  topology (\<open>exit_class_compactin_weak\<close>), that topology
  is the Levy-Prokhorov metric topology hence Hausdorff, so the class is
  closed, hence Borel; and \<open>prob_algebra\<close> is that Borel algebra
  restricted to the probability measures, which the class already consists
  of.\<close>

lemma sets_kglue_law'[simp]:
  "sets (kglue_law' r T Kr Q)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding kglue_law'_def by (rule sets_pair_law_of)

lemma kglue_law'_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and ne: "space Q \<noteq> {}"
  shows "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr
        \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  have "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    by (rule pglue_measurable[OF r rT setsQ refl])
  then show ?thesis
    using measurable_cong_sets[OF sets_ksemi[OF K ne] refl] by blast
qed

lemma AE_kglue_law_of_kernel:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and ne: "space Q \<noteq> {}"
    and mset: "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Phi> \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
  shows "(AE \<omega> in kglue_law' r T Kr Q. \<Phi> \<omega>)
      = (AE p in ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr.
          \<Phi> (pglue r T (fst p) (snd p)))"
  unfolding kglue_law'_def pair_law_of_def
  by (rule AE_distr_iff[OF kglue_law'_measurable[OF r rT setsQ Kp ne] mset])

lemma martingale_of_cuts:
  fixes P :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes prob: "prob_space P"
    and setsP: "sets P = sets (ipath_space :: ('n pairpath) measure)"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and Zloc: "\<And>u S \<omega>. 0 \<le> u \<Longrightarrow> u \<le> S \<Longrightarrow> Z u (pcut S \<omega>) = Z u \<omega>"
    and mg: "\<And>S. 0 \<le> S \<Longrightarrow> martingale (pair_law_of S (pcut S) P)
        (natural_filtration (pair_law_of S (pcut S) P) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. Z (min u S) \<omega>)"
  shows "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0 Z"
proof -
  let ?G = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "\<lambda>S. (path_borel S :: ('n pairpath) measure)"
  let ?Q = "\<lambda>S. pair_law_of S (pcut S) P"
  let ?H = "\<lambda>S. natural_filtration (?Q S) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  interpret PP: prob_space P by (rule prob)
  have SP: "Stochastic_Process.stochastic_process P (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    show "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF setsP refl]
      by (rule ipath_eval_measurable[OF i])
  qed
  have fin: "finite_measure P" using prob by (simp add: prob_space_def)
  interpret SF: finite_filtered_measure P ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP fin])
  have cutm: "pcut S \<in> P \<rightarrow>\<^sub>M ?B S" if S: "0 \<le> S" for S
    by (rule ipcut_measurable[OF S setsP])
  have ZB: "Z w \<in> borel_measurable (?B S)" if w: "0 \<le> w" and wS: "w \<le> S" for w S
  proof -
    have S0: "0 \<le> S" using w wS by simp
    interpret MS: martingale "?Q S" "?H S" 0 "\<lambda>u \<omega>. Z (min u S) \<omega>"
      by (rule mg[OF S0])
    have "(\<lambda>\<omega>. Z (min w S) \<omega>) \<in> borel_measurable (?H S w)" by (rule MS.adapted[OF w])
    then have "Z w \<in> borel_measurable (?H S w)" using wS by simp
    then have "Z w \<in> borel_measurable (?Q S)"
      by (rule measurable_from_subalg[OF MS.subalgebras[OF w]])
    then show ?thesis using measurable_cong_sets[OF sets_pair_law_of refl] by blast
  qed
  have integ: "integrable P (Z w)" if w: "0 \<le> w" for w
  proof -
    interpret MS: martingale "?Q w" "?H w" 0 "\<lambda>u \<omega>. Z (min u w) \<omega>" by (rule mg[OF w])
    have "integrable (?Q w) (\<lambda>\<omega>. Z (min w w) \<omega>)" by (rule MS.integrable[OF w])
    then have "integrable (?Q w) (Z w)" by simp
    then have "integrable P (\<lambda>\<omega>. Z w (pcut w \<omega>))"
      unfolding pair_law_of_def
      using integrable_distr_eq[OF cutm[OF w] ZB[OF w order.refl]] by simp
    then show ?thesis using Zloc[OF w order.refl] by simp
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process P ?G 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?G u)" by (rule Zm[OF u])
    qed
    show "integrable P (Z u)" if "0 \<le> u" for u by (rule integ[OF that])
    fix A and u v :: real
    assume A: "A \<in> ?G u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    interpret MS: martingale "?Q v" "?H v" 0 "\<lambda>w \<omega>. Z (min w v) \<omega>" by (rule mg[OF v0])
    obtain A' where A': "A' \<in> sets (?H v u)" and AA: "A = pcut v -` A' \<inter> space P"
      using A natural_filtration_pcut[OF uv(1) uv(2) setsP] by blast
    have key: "set_lebesgue_integral P A (Z w)
        = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min w v) \<omega>)"
      if w: "0 \<le> w" and wv: "w \<le> v" for w
    proof -
      have AB: "A' \<in> sets (?B v)"
        using A' MS.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A' \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable (?B v)"
        using AB ZB[OF w wv] by measurable
      have "set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min w v) \<omega>)
          = (\<integral>\<omega>. indicat_real A' \<omega> *\<^sub>R Z w \<omega> \<partial>(?Q v))"
        unfolding set_lebesgue_integral_def using wv by simp
      also have "\<dots> = (\<integral>\<omega>. indicat_real A' (pcut v \<omega>) *\<^sub>R Z w (pcut v \<omega>) \<partial>P)"
        unfolding pair_law_of_def by (rule integral_distr[OF cutm[OF v0] gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>P)"
        using AA Zloc[OF w wv]
        by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def ..
    qed
    have "set_lebesgue_integral P A (Z u)
        = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min u v) \<omega>)"
      by (rule key[OF uv(1) uv(2)])
    also have "\<dots> = set_lebesgue_integral (?Q v) A' (\<lambda>\<omega>. Z (min v v) \<omega>)"
      by (rule MS.set_integral_eq[OF A' uv(1) uv(2)])
    also have "\<dots> = set_lebesgue_integral P A (Z v)"
      by (rule key[OF v0 order.refl, symmetric])
    finally show "set_lebesgue_integral P A (Z u) = set_lebesgue_integral P A (Z v)" .
  qed
qed

subsection \<open>The extension lies in the uncapped class\<close>

theorem exit_class_rcd:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and "\<And>A B. A \<in> sets (path_borel r :: ('n pairpath) measure)
        \<Longrightarrow> B \<in> sets ((path_borel (T - r) :: ('n pairpath) measure))
        \<Longrightarrow> emeasure (distr P
              ((path_borel r :: ('n pairpath) measure)
                \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
              (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))) (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of r (pcut r) P))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
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

lemma prob_space_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "prob_space (kglue_law' r T Kr Q)"
proof -
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  interpret PK: prob_space "ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr"
    by (rule prob_space_ksemi[OF PQ K])
  show ?thesis
    unfolding kglue_law'_def pair_law_of_def
    by (rule PK.prob_space_distr[OF kglue_law'_measurable[OF r rT setsQ K ne]])
qed

text \<open>The almost-sure transfer.  Note that the second-coordinate property
  \<open>B\<close> may depend on the first coordinate --- it has to, since the kernel
  does.  That is the only difference from
  \<open>AE_kglue_law\<close>; the proof is the same, with
  @{thm [source] AE_ksemi} in place of the product space's
  \<open>AE_pair_measure\<close>.\<close>

lemma AE_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>"
    and B: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> AE \<omega>' in Kr \<omega>. B \<omega> \<omega>'"
    and imp: "\<And>\<omega> \<omega>'. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega> \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in kglue_law' r T Kr Q. P \<omega>"
proof -
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?MR Kr"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have phim: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?S \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law' r T Kr Q. P \<omega>)
      = (AE p in ?S. P (pglue r T (fst p) (snd p)))"
    unfolding kglue_law'_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?S. P (pglue r T (fst p) (snd p))} \<in> sets ?S"
  proof -
    have "{p \<in> space ?S. P (pglue r T (fst p) (snd p))}
        = (\<lambda>p. pglue r T (fst p) (snd p)) -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?S"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have evm': "{p \<in> space (Q \<Otimes>\<^sub>M ?MR). P (pglue r T (fst p) (snd p))}
      \<in> sets (Q \<Otimes>\<^sub>M ?MR)"
    using evm sets_ksemi[OF K ne] space_ksemi[OF K ne] by simp
  have inner: "AE \<omega> in Q. AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
  proof -
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<and> \<omega> \<in> space Q"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)
          \<and> \<omega> \<in> space Q"
      then have wQ: "\<omega> \<in> space Q" by blast
      have sk: "sets (Kr \<omega>) = sets ?MR" by (rule ksemi_sets_kernel(1)[OF K wQ])
      have KB: "AE \<omega>' in Kr \<omega>. B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        using B[OF wQ] AE_space[of "Kr \<omega>"] by (auto intro: eventually_conj)
      show "AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
      proof (rule eventually_mono[OF KB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        then have "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
          and "B \<omega> \<omega>'"
          using sk by (auto simp: space_of_path_sets sets_eq_imp_space_eq
              space_borel_of)
        with w show "P (pglue r T \<omega> \<omega>')" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?S. P (pglue r T (fst p) (snd p))"
    using AE_ksemi[OF K evm'] inner by simp
  then show ?thesis unfolding iff .
qed

text \<open>Clause (i) of (1.7) for the kernel glue.\<close>

text \<open>Clause (ii): the covariation difference quotient.  The kernel's
  values have to lie in the class at the origin --- this is the first
  place where that is used, and it is where the almost-sure statement of
  the continuation enters, one \<open>\<omega>\<close> at a time.\<close>

subsection \<open>The glue is continuous, and the product is a Polish product\<close>

text \<open>Proving clauses (iii) and (iv) directly for \<open>ksemi\<close> runs into
  two obstructions: the distribution's \<open>integral_bind\<close> covers only
  bounded real integrands, and the first-factor martingale property is
  false for a semidirect product (the weight \<open>(Kr \<omega>)(A\<^sub>\<omega>)\<close> in the
  disintegrated set integral is only \<open>\<F>\<^sub>r\<close>-measurable).

  Neither has to be faced.  The class is weakly closed
  (\<open>exit_class_weak_closed\<close>), the glue with a countably
  valued index is already in it
  (\<open>exit_class_kglue_law\<close>), and the class at the origin
  is a compact metric space
  (\<open>exit_class_compact_metric_space\<close>), hence separable,
  so any kernel into it is a pointwise limit of countably valued ones.  If
  the semidirect products converge weakly, the glued laws do too, and weak
  closedness finishes --- which needs continuity of the glue and the
  identity of the two \<open>\<sigma>\<close>-algebras on the product.\<close>

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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
  shows "AE p in pair_law_of r (pcut r) P.
      emeasure (\<kappa> p) {w \<in> space ((path_borel (T - r) :: ('n pairpath) measure)).
        fst (w 0) = 0 \<and> snd (w 0) = 0} = 1"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
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
  \<open>exit_class_diffquot_of_pairs\<close>.  The original demands
  the pairwise bound at all real pairs, which an almost-sure argument cannot
  supply, since only countably many conditions survive the passage from "for
  each, almost surely" to "almost surely, for all".  Its proof already uses
  the hypothesis at rational pairs only, so the weakening is free.\<close>

lemma ksemi_weak_conv:
  fixes Krm :: "nat \<Rightarrow> 'a \<Rightarrow> 'b measure" and X :: "'a topology" and Y :: "'b topology"
  assumes PM: "prob_space M"
    and setsM: "sets M = sets (borel_of X)"
    and scX: "second_countable X" and scY: "second_countable Y"
    and Km: "\<And>m. Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and conv: "\<And>\<omega>. \<omega> \<in> space M
        \<Longrightarrow> weak_conv_on (\<lambda>m. Krm m \<omega>) (Kr \<omega>) sequentially Y"
  shows "weak_conv_on (\<lambda>m. ksemi M (borel_of Y) (Krm m))
      (ksemi M (borel_of Y) Kr) sequentially (prod_topology X Y)"
proof -
  let ?N = "borel_of Y"
  let ?Z = "prod_topology X Y"
  interpret PM: prob_space M by (rule PM)
  have ne: "space M \<noteq> {}" by (rule PM.not_empty)
  have spX: "space M = topspace X"
    using setsM by (simp add: sets_eq_imp_space_eq space_borel_of)
  have bprod: "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of ?Z)"
  proof -
    have "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of X \<Otimes>\<^sub>M borel_of Y)"
      by (rule sets_pair_measure_cong[OF setsM refl])
    also have "\<dots> = sets (borel_of ?Z)"
      by (rule arg_cong[where f = sets, OF borel_of_prod[OF scX scY]])
    finally show ?thesis .
  qed
  have setsK: "sets (ksemi M ?N Kr) = sets (borel_of ?Z)"
    using sets_ksemi[OF K ne] bprod by simp
  have setsKm: "sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using sets_ksemi[OF Kmm ne] bprod by simp
  qed
  have fmK: "finite_measure (ksemi M ?N Kr)"
    using prob_space_ksemi[OF PM K]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmKm: "finite_measure (ksemi M ?N (Krm m))" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using prob_space_ksemi[OF PM Kmm]
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
  qed
  show ?thesis
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F m in sequentially. sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)
        \<and> finite_measure (ksemi M ?N (Krm m))"
      by (intro always_eventually allI conjI setsKm fmKm)
    show "sets (ksemi M ?N Kr) = sets (borel_of ?Z)" by (rule setsK)
    show "finite_measure (ksemi M ?N Kr)" by (rule fmK)
    fix f :: "'a \<times> 'b \<Rightarrow> real"
    assume cf: "continuous_map ?Z euclideanreal f"
    assume bf: "\<exists>B. \<forall>p \<in> topspace ?Z. \<bar>f p\<bar> \<le> B"
    from bf obtain B where B: "\<And>p. p \<in> topspace ?Z \<Longrightarrow> \<bar>f p\<bar> \<le> B" by blast
    have fm: "f \<in> borel_measurable (M \<Otimes>\<^sub>M ?N)"
    proof -
      have "f \<in> borel_of ?Z \<rightarrow>\<^sub>M borel_of euclideanreal"
        by (rule continuous_map_measurable[OF cf])
      then have "f \<in> borel_measurable (borel_of ?Z)"
        by (simp add: borel_of_euclidean)
      then show ?thesis unfolding measurable_cong_sets[OF bprod refl] .
    qed
    have spZ: "space (M \<Otimes>\<^sub>M ?N) = topspace ?Z"
    proof -
      have "space (M \<Otimes>\<^sub>M ?N) = space (borel_of ?Z)"
        by (rule sets_eq_imp_space_eq[OF bprod])
      then show ?thesis by (simp add: space_borel_of)
    qed
    have fb: "\<bar>f p\<bar> \<le> B" if "p \<in> space (M \<Otimes>\<^sub>M ?N)" for p
      using that spZ by (simp add: B)
    \<comment> \<open>the two disintegrations\<close>
    have dK: "(\<integral>p. f p \<partial>(ksemi M ?N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
      by (rule integral_ksemi_bounded[OF PM K fm fb])
    have dKm: "(\<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_bounded[OF PM Kmm fm fb])
    qed
    \<comment> \<open>the inner integrals converge pointwise and are uniformly bounded\<close>
    have inner_lim: "(\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have wX: "\<omega> \<in> topspace X" using w spX by simp
      have cpair: "continuous_map Y ?Z (Pair \<omega>)"
        unfolding continuous_map_pairwise using wX by (simp add: o_def)
      have cg: "continuous_map Y euclideanreal (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        using continuous_map_compose[OF cpair cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>y \<in> topspace Y. \<bar>f (\<omega>, y)\<bar> \<le> B'"
        using B wX by (intro exI[of _ B]) auto
      show ?thesis using conv[OF w, unfolded weak_conv_on_def] cg bg by blast
    qed
    have inner_meas: "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<in> borel_measurable M" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_measurable[OF Kmm fm])
    qed
    have inner_meas': "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
      by (rule integral_ksemi_measurable[OF K fm])
    have inner_bnd: "\<bar>\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)\<bar> \<le> \<bar>B\<bar>" if w: "\<omega> \<in> space M" for \<omega> m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      interpret PK: prob_space "Krm m \<omega>" by (rule ksemi_sets_kernel(2)[OF Kmm w])
      have sk: "sets (Krm m \<omega>) = sets ?N" by (rule ksemi_sets_kernel(1)[OF Kmm w])
      have gm: "(\<lambda>\<omega>'. f (\<omega>, \<omega>')) \<in> borel_measurable (Krm m \<omega>)"
      proof -
        have "Pair \<omega> \<in> Krm m \<omega> \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M ?N"
          by (rule ksemi_Pair_measurable[OF Kmm w])
        from measurable_compose[OF this fm] show ?thesis by simp
      qed
      have spk: "space (Krm m \<omega>) = space ?N" by (rule sets_eq_imp_space_eq[OF sk])
      have gb: "\<bar>f (\<omega>, \<omega>')\<bar> \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
      proof -
        have "\<omega>' \<in> space ?N" using that spk by simp
        then have "(\<omega>, \<omega>') \<in> space (M \<Otimes>\<^sub>M ?N)"
          using w by (simp add: space_pair_measure)
        then show ?thesis using fb[of "(\<omega>, \<omega>')"] by simp
      qed
      have gbu: "f (\<omega>, \<omega>') \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have gbl: "- \<bar>B\<bar> \<le> f (\<omega>, \<omega>')" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have cint: "(\<integral>\<omega>'. (c::real) \<partial>(Krm m \<omega>)) = c" for c
        by (simp add: PK.prob_space)
      have ig: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        by (rule PK.integrable_const_bound[of _ "\<bar>B\<bar>"])
          (use gb gm in \<open>auto\<close>)
      have ic: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. \<bar>B\<bar>)" by (rule PK.integrable_const)
      have ic': "integrable (Krm m \<omega>) (\<lambda>\<omega>'. - \<bar>B\<bar>)" by (rule PK.integrable_const)
      have up: "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>"
      proof -
        have "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> (\<integral>\<omega>'. \<bar>B\<bar> \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ig ic gbu])
        also have "\<dots> = \<bar>B\<bar>" by (rule cint)
        finally show ?thesis .
      qed
      have lo: "- \<bar>B\<bar> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
      proof -
        have "- \<bar>B\<bar> = (\<integral>\<omega>'. - \<bar>B\<bar> \<partial>(Krm m \<omega>))" by (rule cint[symmetric])
        also have "\<dots> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ic' ig gbl])
        finally show ?thesis .
      qed
      from up lo show ?thesis by simp
    qed
    have "(\<lambda>m. \<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)
        \<longlonglongrightarrow> (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    proof (rule integral_dominated_convergence
        [where w = "\<lambda>_. \<bar>B\<bar>", OF inner_meas' inner_meas])
      show "integrable M (\<lambda>_. \<bar>B\<bar>)" by simp
      show "AE \<omega> in M. (\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))
          \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
        using inner_lim by (intro AE_I2) blast
      show "AE \<omega> in M. norm (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>" for m
        using inner_bnd by (intro AE_I2) simp
    qed
    then show "(\<lambda>m. \<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        \<longlonglongrightarrow> (\<integral>p. f p \<partial>(ksemi M ?N Kr))"
      by (simp add: dK dKm)
  qed
qed

subsection \<open>Countably valued approximation of a kernel\<close>

text \<open>\<open>countably_valued_approx\<close>, \<open>limitin_of_dist_half\<close> live in @{theory Semicontinuous_Analysis.Semicontinuous_Selection}.\<close>


subsection \<open>The two constructions agree at a countably valued kernel\<close>

text \<open>With a countably valued index the
  product-of-all-candidates construction and the Giry semidirect product
  give the same law, because the second coordinate of the product,
  evaluated at a first-coordinate-measurable index, has exactly the
  kernel's law.  Both sides reduce to
  \<open>\<integral>\<^sup>+\<omega>. (RR (N \<omega>)) {\<omega>'. pglue r T \<omega> \<omega>' \<in> A} \<partial>Q\<close>: on the left by Fubini and
  \<open>distr_PiM_component\<close>, on the right by \<open>emeasure_bind\<close> and \<open>emeasure_distr\<close>.\<close>

lemma ksemi_rect_null_of_AE:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and C: "C \<in> sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and ae: "AE \<omega> in P. pfut r T \<omega> \<in> C"
  shows "emeasure (ksemi (pair_law_of r (pcut r) P)
        ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>)
      (space (path_borel r :: ('n pairpath) measure)
        \<times> (space ((path_borel (T - r) :: ('n pairpath) measure)) - C)) = 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
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
  library's real-valued \<open>prob_space.AE_prob_1\<close> goes through
  \<open>finite_measure.emeasure_eq_measure\<close>.\<close>

text \<open>\<open>AE_mem_of_emeasure_1\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

text \<open>Clause (ii) for the conditional law, at rational pairs only, since an
  almost-sure statement survives only countably many conditions, which is
  what \<open>exit_class_diffquot_of_rational_pairs\<close> supplies.\<close>

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
  positive and negative parts.  \<open>real_lebesgue_integral_def\<close>
  splits both sides into \<open>enn2real\<close> of nonnegative integrals, and on those
  @{thm [source] nn_integral_ksemi} applies with no boundedness hypothesis at
  all.\<close>

lemma pstopped_law_prob:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PS: "prob_space P"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "prob_space (pair_law_of T (pstopped T \<theta>) P)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret PP: prob_space P by (rule PS)
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  show ?thesis unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
qed

lemma pstopped_law_idem:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P. pstopped T \<theta> p' = p'"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have mset: "{p' \<in> space ?B. pstopped T \<theta> p' = p'} \<in> sets ?B"
    by (rule pstopped_fixed_set_measurable[OF T0 st thM])
  have "AE \<omega> in P. pstopped T \<theta> (pstopped T \<theta> \<omega>) = pstopped T \<theta> \<omega>"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
        by (rule path_sets_fst_continuous[OF setsP elim])
      show ?case by (rule pstopped_idem[OF st cw])
    qed
  qed
  then show ?thesis
    unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
qed

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
  fixed-integrand \<open>integral_measurable_subprob_algebra\<close>, and
  the section integral factors as a constant times an integral over the
  kernel.\<close>

lemma integral_aglue_law:
  fixes Q :: "('n::finite pairpath) measure" and h :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hm: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and hi: "integrable (aglue_law T \<kappa> Q) h"
    and msec: "(\<lambda>p'. \<integral>w. h (padd T p' w) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
  shows "(\<integral>\<omega>. h \<omega> \<partial>(aglue_law T \<kappa> Q))
      = (\<integral>p'. (\<integral>w. h (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p)"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm2: "?g \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have pm: "?g \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl] by (rule pm2)
  have hgm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). h (?g p))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pm2 hm])
  have hgi: "integrable (ksemi Q ?B \<kappa>) (\<lambda>p. h (?g p))"
  proof -
    have "integrable (distr (ksemi Q ?B \<kappa>) ?B ?g) h" using hi
      unfolding aglue_law_def .
    then show ?thesis unfolding integrable_distr_eq[OF pm hm] .
  qed
  have "(\<integral>\<omega>. h \<omega> \<partial>(aglue_law T \<kappa> Q)) = (\<integral>p. h (?g p) \<partial>(ksemi Q ?B \<kappa>))"
    unfolding aglue_law_def by (rule integral_distr[OF pm hm])
  also have "\<dots> = (\<integral>p'. (\<integral>w. h (?g (p', w)) \<partial>(\<kappa> p')) \<partial>Q)"
    by (rule integral_ksemi_real[OF Kp hgm hgi neQ]) (use msec in simp)
  finally show ?thesis by simp
qed

subsection \<open>Auxiliaries for clause (iv)\<close>

text \<open>\<open>i \<and> \<theta>\<close> is a stopping time.  Unlike \<open>i \<or> \<theta>\<close> this needs both directions of
  the cut: on \<open>{\<theta> \<le> i}\<close> the value is \<open>\<theta>\<close> and agreement up to \<open>\<theta>\<close> fixes it; on
  \<open>{\<theta> > i}\<close> the value is \<open>i\<close>, and agreement up to \<open>i\<close> still fixes it, because
  a path with \<open>\<theta> < i\<close> would already have been detected by then.\<close>

lemma pstopped_law_start:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P.
      fst (p' 0) = x \<and> snd (p' 0) = 0"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have ev: "(\<lambda>p' :: 'n pairpath. p' 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{p' \<in> space ?B. fst (p' 0) = x \<and> snd (p' 0) = 0} \<in> sets ?B"
  proof -
    have "{p' \<in> space ?B. fst (p' 0) = x \<and> snd (p' 0) = 0}
        = (\<lambda>p' :: 'n pairpath. p' 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have "AE \<omega> in P. fst (pstopped T \<theta> \<omega> 0) = x \<and> snd (pstopped T \<theta> \<omega> 0) = 0"
    using P0
  proof eventually_elim
    case (elim \<omega>)
    have "pstopped T \<theta> \<omega> 0 = \<omega> (min 0 (\<theta> \<omega>))" by (rule pstopped_apply[OF z])
    also have "min 0 (\<theta> \<omega>) = 0" using th0[of \<omega>] by simp
    finally show ?case using elim by simp
  qed
  then show ?thesis unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
qed

lemma pstopped_law_cont:
  fixes P :: "('n::finite pairpath) measure"
  assumes p: "p' \<in> space (pair_law_of T (pstopped T \<theta>) P)"
  shows "continuous_on {0..T} p'"
proof -
  have "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    using p by (simp add: space_pair_law_of)
  then show ?thesis by (rule mspace_path_metricD)
qed

text \<open>\<open>Qcov\<close>.  The stopped law's covariation constraint holds up to the
  random horizon \<open>\<theta> p'\<close>, exactly the shape
  @{thm [source] diffquot_all_of_rational} takes once its horizon
  parameter is instantiated with \<open>\<theta> p'\<close> rather than \<open>T\<close>.  No guarded
  variant is needed: the rationals the lemma picks already satisfy
  \<open>q < t \<le> \<theta> p'\<close>.\<close>

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
  martingale clauses is \<open>martingale.set_integral_eq\<close> applied to
  \<open>P\<close>.\<close>

definition kglue :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath \<times> (nat \<Rightarrow> 'n pairpath)) \<Rightarrow> 'n pairpath"
  where "kglue r T N p = pglue r T (fst p) (snd p (N (fst p)))"

definition kglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> (nat \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure"
  where "kglue_law r T N Q RR
     = pair_law_of T (kglue r T N) (Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR)"

theorem path_rcd:
  fixes P :: "('n::finite pairpath) measure"
  assumes v: "0 \<le> v" and PS: "prob_space P"
    and m1: "\<phi>1 \<in> P \<rightarrow>\<^sub>M (path_borel u :: ('n pairpath) measure)"
    and m2: "\<phi>2 \<in> P \<rightarrow>\<^sub>M (path_borel v :: ('n pairpath) measure)"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel u :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel v :: ('n pairpath) measure)"
    and "\<And>A B. A \<in> sets (path_borel u :: ('n pairpath) measure)
        \<Longrightarrow> B \<in> sets (path_borel v :: ('n pairpath) measure)
        \<Longrightarrow> emeasure (distr P
              ((path_borel u :: ('n pairpath) measure)
                \<Otimes>\<^sub>M (path_borel v :: ('n pairpath) measure))
              (\<lambda>\<omega>. (\<phi>1 \<omega>, \<phi>2 \<omega>))) (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of u \<phi>1 P))"
proof -
  let ?X = "(path_borel u :: ('n pairpath) measure)"
  let ?Y = "(path_borel v :: ('n pairpath) measure)"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (\<phi>1 \<omega>, \<phi>2 \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  interpret PP: prob_space P by (rule PS)
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using m1 m2 by simp
  have setsnu: "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by simp

  have marg: "marginal_measure ?X ?Y ?\<nu> = pair_law_of u \<phi>1 P"
  proof (rule measure_eqI)
    show "sets (marginal_measure ?X ?Y ?\<nu>) = sets (pair_law_of u \<phi>1 P)"
      by (simp add: sets_marginal_measure)
    fix A assume "A \<in> sets (marginal_measure ?X ?Y ?\<nu>)"
    then have AX: "A \<in> sets ?X" by (simp add: sets_marginal_measure)
    have rect: "A \<times> space ?Y \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using AX by simp
    have "emeasure (marginal_measure ?X ?Y ?\<nu>) A = emeasure ?\<nu> (A \<times> space ?Y)"
      by (rule emeasure_marginal_measure[OF setsnu AX])
    also have "\<dots> = emeasure P (?\<phi> -` (A \<times> space ?Y) \<inter> space P)"
      by (rule emeasure_distr[OF mphi rect])
    also have "\<dots> = emeasure P (\<phi>1 -` A \<inter> space P)"
    proof -
      have "?\<phi> -` (A \<times> space ?Y) \<inter> space P = \<phi>1 -` A \<inter> space P"
        using measurable_space[OF m2] by auto
      then show ?thesis by simp
    qed
    also have "\<dots> = emeasure (pair_law_of u \<phi>1 P) A"
      unfolding pair_law_of_def by (rule emeasure_distr[OF m1 AX, symmetric])
    finally show "emeasure (marginal_measure ?X ?Y ?\<nu>) A
        = emeasure (pair_law_of u \<phi>1 P) A" .
  qed

  have PSF: "projection_sigma_finite ?X ?Y ?\<nu>"
    unfolding projection_sigma_finite_def
  proof (intro conjI)
    show "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by (rule setsnu)
    have "prob_space (pair_law_of u \<phi>1 P)"
      unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
    then show "sigma_finite_measure (marginal_measure ?X ?Y ?\<nu>)"
      unfolding marg by (rule prob_space_imp_sigma_finite)
  qed
  have SB: "standard_borel_ne ?Y" by (rule standard_borel_ne_path_metric[OF v])
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
        = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of u \<phi>1 P))"
      if A: "A \<in> sets ?X" and B: "B \<in> sets ?Y" for A B
    proof -
      have "emeasure ?\<nu> (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(marginal_measure ?X ?Y ?\<nu>))"
        using DIS A B unfolding MK.disintegration_def by blast
      then show ?thesis unfolding marg .
    qed
  qed
qed

lemma sets_kglue_law[simp]:
  "sets (kglue_law r T N Q RR)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding kglue_law_def by (rule sets_pair_law_of)

lemma kglue_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "kglue r T N \<in> Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M
      (path_borel T :: ('n pairpath) measure)"
proof -
  let ?M = "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p v)
      \<in> borel_measurable ?M" for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have Nfst: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?M \<rightarrow>\<^sub>M count_space UNIV"
    by (rule measurable_compose[OF measurable_fst Nm])
  have eS: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) v)
      \<in> borel_measurable ?M" for v
  proof (rule measurable_compose_countable[OF _ Nfst])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M RR j"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j) \<in> ?M \<rightarrow>\<^sub>M RR j" .
    from measurable_compose[OF this pair_law_eval_measurable[OF setsR]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j v)
        \<in> borel_measurable ?M" .
  qed
  have Xm: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))
      \<in> borel_measurable ?M" for t
    using eQ eS by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))"
    if p: "p \<in> space ?M" for p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" and sp: "snd p \<in> space (Pi\<^sub>M UNIV RR)"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)"
      using space_of_path_sets[OF setsQ] by (auto intro: mspace_path_metricD)
    have "snd p (N (fst p)) \<in> space (RR (N (fst p)))"
      using sp by (simp add: space_PiM PiE_iff)
    then show "continuous_on {0..T - r} (snd p (N (fst p)))"
      using space_of_path_sets[OF setsR] by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont]
    unfolding kglue_def pglue_def by simp
qed

lemma kglue_law_eq_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and K: "(\<lambda>\<omega>. RR (N \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "kglue_law r T N Q RR = kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q"
proof (rule measure_eqI)
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?P = "Q \<Otimes>\<^sub>M ?S"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have gm: "kglue r T N \<in> ?P \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have pm: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)) \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  show "sets (kglue_law r T N Q RR) = sets (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q)"
    by simp
  fix A :: "('n pairpath) set"
  assume A: "A \<in> sets (kglue_law r T N Q RR)"
  then have AB: "A \<in> sets ?B" by simp
  \<comment> \<open>the section of the pulled-back set, one \<open>\<omega>\<close> at a time\<close>
  have sec: "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
      = emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P))"
    if w: "\<omega> \<in> space Q" for \<omega>
  proof -
    have Pj: "prob_space (RR i)" if "i \<in> (UNIV :: nat set)" for i by (rule PR)
    have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f (N \<omega>)) \<in> ?S \<rightarrow>\<^sub>M RR (N \<omega>)"
      by (rule measurable_component_singleton) simp
    have dj: "distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)) = RR (N \<omega>)"
      by (rule distr_PiM_component[OF Pj UNIV_I])
    have pglm: "pglue r T \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M ?B"
    proof -
      have p1: "Pair \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M Q \<Otimes>\<^sub>M ?MR"
        using measurable_Pair1'[OF w, of ?MR]
          measurable_cong_sets[OF setsR refl] by blast
      have p2: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?MR \<rightarrow>\<^sub>M ?B"
        by (rule pglue_measurable[OF r rT setsQ refl])
      from measurable_compose[OF p1 p2] show ?thesis by (simp add: comp_def)
    qed
    have Am: "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<in> sets (RR (N \<omega>))"
    proof -
      have "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          = pglue r T \<omega> -` A \<inter> space (RR (N \<omega>))" by auto
      then show ?thesis using measurable_sets[OF pglm AB] by simp
    qed
    have "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
        = emeasure (distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)))
            {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
      unfolding dj ..
    also have "\<dots> = emeasure ?S
        ((\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<inter> space ?S)"
      by (rule emeasure_distr[OF mj Am])
    also have "(\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          \<inter> space ?S
        = Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)"
      using w measurable_space[OF mj] by (auto simp: space_pair_measure kglue_def)
    finally show ?thesis .
  qed
  \<comment> \<open>the left-hand side by Fubini\<close>
  have lhs: "emeasure (kglue_law r T N Q RR) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    have "emeasure (kglue_law r T N Q RR) A
        = emeasure ?P (kglue r T N -` A \<inter> space ?P)"
      unfolding kglue_law_def pair_law_of_def by (rule emeasure_distr[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)) \<partial>Q)"
      by (rule PS.emeasure_pair_measure_alt) (rule measurable_sets[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
      by (rule nn_integral_cong) (simp add: sec)
    finally show ?thesis .
  qed
  \<comment> \<open>the right-hand side by the semidirect product's disintegration\<close>
  have rhs: "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    define C where "C = (\<lambda>p. pglue r T (fst p) (snd p)) -` A
        \<inter> space (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
    have Cs: "C \<in> sets (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
      unfolding C_def by (rule measurable_sets[OF pm AB])
    have Csp: "C \<in> sets (Q \<Otimes>\<^sub>M ?MR)" using Cs sets_ksemi[OF K ne] by simp
    have "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
        = emeasure (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>))) C"
      unfolding kglue_law'_def pair_law_of_def C_def
      by (rule emeasure_distr[OF pm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C \<partial>Q)"
      unfolding ksemi_def
      by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] Csp])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
    proof (rule nn_integral_cong)
      fix \<omega> assume w: "\<omega> \<in> space Q"
      have spR: "space (RR (N \<omega>)) = space ?MR"
        by (rule sets_eq_imp_space_eq[OF setsR])
      have "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) (Pair \<omega> -` C \<inter> space (RR (N \<omega>)))"
        by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] Csp])
      also have "Pair \<omega> -` C \<inter> space (RR (N \<omega>))
          = {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
        unfolding C_def
        using w spR space_ksemi[OF K ne] by (auto simp: space_pair_measure)
      finally show "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}" .
    qed
    finally show ?thesis .
  qed
  show "emeasure (kglue_law r T N Q RR) A
      = emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A"
    using lhs rhs by simp
qed

subsection \<open>Kernel pasting: clauses (iii) and (iv), by weak closedness\<close>

text \<open>The class is closed under concatenation with a continuation chosen
  by an arbitrary measurable kernel, not just a countably valued index ---
  and the two martingale clauses never have to be proved for the
  semidirect product.

  Round the kernel to the dense sequence of the compact class
  (\<open>Metric_space.countably_valued_approx\<close>); each rounded
  glue is a legitimate pasting
  (\<open>exit_class_kglue_law\<close>) and, by
  @{thm [source] kglue_law_eq_kglue_law'}, is the kernel glue at the
  rounded kernel; the semidirect products converge weakly
  (@{thm [source] ksemi_weak_conv}), the glue is continuous
  (@{thm [source] Lipschitz_pglue}), so the glued laws converge; and the
  class is weakly closed
  (\<open>exit_class_weak_closed\<close>).\<close>

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

lemma prob_space_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "prob_space (kglue_law r T N Q RR)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
    by (rule prob_space_pair_measure[OF PQ prob_space_PiM]) (rule PR)
  show ?thesis
    unfolding kglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr
        [OF kglue_measurable[OF r rT setsQ setsR Nm]])
qed

lemma pfut_filtration_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
  shows "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))
        \<rightarrow>\<^sub>M natural_filtration
            (pair_law_of (T - r) (pfut r T) P) 0 (\<lambda>v w. w v) u"
proof -
  let ?S = "T - r"
  let ?FF = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)
      (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have phim: "pfut r T \<in> P \<rightarrow>\<^sub>M (path_borel ?S :: ('n pairpath) measure)"
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

lemma AE_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE f in Pi\<^sub>M UNIV RR. B f"
    and imp: "\<And>\<omega> f. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        f \<in> space (Pi\<^sub>M UNIV RR) \<Longrightarrow> A \<omega> \<Longrightarrow> B f \<Longrightarrow> P (kglue r T N (\<omega>, f))"
  shows "AE \<omega> in kglue_law r T N Q RR. P \<omega>"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  interpret PP: pair_prob_space Q ?S by unfold_locales
  have phim: "kglue r T N \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law r T N Q RR. P \<omega>)
      = (AE p in ?M. P (kglue r T N p))"
    unfolding kglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (kglue r T N p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (kglue r T N p)}
        = kglue r T N -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE f in ?S. P (kglue r T N (\<omega>, f))"
  proof -
    have SB: "AE f in ?S. B f \<and> f \<in> space ?S"
      using B AE_space[of ?S] by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE f in ?S. P (kglue r T N (\<omega>, f))"
      proof (rule eventually_mono[OF SB])
        fix f :: "nat \<Rightarrow> 'n pairpath"
        assume "B f \<and> f \<in> space ?S"
        with w show "P (kglue r T N (\<omega>, f))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (kglue r T N p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

theorem path_rcd_ksemi:
  fixes P :: "('n::finite pairpath) measure"
  assumes v: "0 \<le> v" and PS: "prob_space P"
    and m1: "\<phi>1 \<in> P \<rightarrow>\<^sub>M (path_borel u :: ('n pairpath) measure)"
    and m2: "\<phi>2 \<in> P \<rightarrow>\<^sub>M (path_borel v :: ('n pairpath) measure)"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel u :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel v :: ('n pairpath) measure)"
    and "distr P
          ((path_borel u :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel v :: ('n pairpath) measure))
          (\<lambda>\<omega>. (\<phi>1 \<omega>, \<phi>2 \<omega>))
        = ksemi (pair_law_of u \<phi>1 P)
            (path_borel v :: ('n pairpath) measure) \<kappa>"
proof -
  let ?X = "(path_borel u :: ('n pairpath) measure)"
  let ?Y = "(path_borel v :: ('n pairpath) measure)"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (\<phi>1 \<omega>, \<phi>2 \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  let ?Q = "pair_law_of u \<phi>1 P"
  let ?E = "{a \<times> b | a b. a \<in> sets ?X \<and> b \<in> sets ?Y}"
  interpret PP: prob_space P by (rule PS)
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using m1 m2 by simp
  interpret Pnu: prob_space ?\<nu> by (rule PP.prob_space_distr[OF mphi])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and REC: "\<And>A B. A \<in> sets ?X \<Longrightarrow> B \<in> sets ?Y \<Longrightarrow>
        emeasure ?\<nu> (A \<times> B) = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
    by (rule path_rcd[OF v PS m1 m2]) blast
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

text \<open>The conditional law of the increments after \<open>\<theta>\<close> given the path stopped
  at \<open>\<theta>\<close>.  Both factors live on the same \<open>T\<close>-path space, so this is
  @{thm [source] path_rcd_ksemi} at \<open>u = v = T\<close>.\<close>

subsection \<open>Identifying the class the conditional law lives in\<close>

text \<open>\<open>pafter T \<theta> \<omega>\<close> is frozen on \<open>[0,\<theta>]\<close>, so it is not a member of
  \<open>exit_class k L T 0\<close>: the covariation constraint fails while the
  path stands still.  It is instead the delayed embedding of the ordinary
  rebased future \<open>pfut \<theta> T \<omega>\<close>, padded with \<open>0\<close> on \<open>[0,\<theta>]\<close> and running the
  future after that; the class statement for the kernel is thus a statement
  about \<open>prebase \<theta> T \<circ> pafter T \<theta>\<close>, exactly what \<open>exit_class_rcd_member\<close> says about the law of \<open>pfut r T\<close>.  The random
  horizon \<open>T - \<theta>\<close> is harmless: inside an almost-sure statement over the
  past, \<open>\<theta>\<close> is a fixed number, and the kernel's codomain stays a fixed space
  by keeping \<open>pafter\<close> on the \<open>T\<close>-space.\<close>

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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
  shows "pcut r \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration (pair_law_of r (pcut r) P) 0 (\<lambda>v w. w v) u"
proof -
  have phim: "pcut r \<in> P \<rightarrow>\<^sub>M (path_borel r :: ('n pairpath) measure)"
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

lemma kglue_param_martingale:
  fixes RR :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Z :: "nat \<Rightarrow> real \<Rightarrow> ('n pairpath)
        \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes rT: "r \<le> T"
    and mg: "\<And>j. martingale (RR j) (natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v)) 0 (Z j)"
    and PR: "\<And>j. prob_space (RR j)"
  shows "martingale (Pi\<^sub>M UNIV RR)
      (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v) (max (u - r) 0)))
      0 (\<lambda>u f. Z i (max (u - r) 0) (f i))"
proof -
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have FR: "filtered_measure (RR j) (?GR j) (0::real)" for j
  proof -
    interpret MJ: martingale "RR j" "?GR j" "0::real" "Z j" by (rule mg)
    show ?thesis by unfold_locales
  qed
  have s0: "0 \<le> max (u - r) 0" for u :: real by simp
  have smono: "max (u - r) 0 \<le> max (v - r) 0" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have "martingale (Pi\<^sub>M UNIV RR) (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j u)) 0
      (\<lambda>u f. Z i u (f i))"
    by (rule martingale_PiM_component[OF PR FR mg])
  from martingale_time_change[OF this s0 smono] show ?thesis .
qed

text \<open>The uniform first-moment bound the kernel glue's integrability needs:
  the bound depends only on \<open>k\<close>, \<open>L\<close> and the horizon, not on the member ---
  so it holds simultaneously for every candidate continuation in the
  family.  \<open>a \<le> 1 + a\<^sup>2\<close> avoids a square root, so no Cauchy--Schwarz is
  needed.\<close>

lemma pcut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and A: "A \<in> sets (path_borel r :: ('n pairpath) measure)"
  shows "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
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

lemma section_padd_in_filtration:
  fixes p' :: "'n::finite pairpath" and N :: "('n pairpath) measure"
  assumes i0: "0 \<le> i" and iT: "i \<le> T"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and pm: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
  shows "{w \<in> space N. pcut i (padd T p' w) \<in> B}
      \<in> sets (natural_filtration N 0 (\<lambda>v w. w v) i)"
proof -
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  have pc: "pcut i p' \<in> mspace (path_metric i :: ('n pairpath) metric)"
  proof -
    have "continuous_on {0..i} p'"
      by (rule continuous_on_subset[OF mspace_path_metricD[OF pm]])
         (use i0 iT in auto)
    then show ?thesis unfolding pcut_def by (rule mspace_path_metricI)
  qed
  have m1: "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q) \<in> ?Bi \<rightarrow>\<^sub>M ?Bi"
  proof (rule measurable_into_path_metric)
    show "padd i (pcut i p') q \<in> mspace (path_metric i :: ('n pairpath) metric)"
      if "q \<in> space ?Bi" for q
      using that pc by (auto simp: space_borel_of intro: padd_mspace)
  next
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric i :: ('n pairpath) metric)"
    show "(\<lambda>q. mdist (path_metric i :: ('n pairpath) metric)
        (padd i (pcut i p') q) a) \<in> borel_measurable ?Bi"
    proof (rule mdist_measurable_of_eval[OF i0 _ am])
      show "padd i (pcut i p') q \<in> mspace (path_metric i :: ('n pairpath) metric)"
        if "q \<in> space ?Bi" for q
        using that pc by (auto simp: space_borel_of intro: padd_mspace)
      fix s :: real
      show "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q s) \<in> borel_measurable ?Bi"
      proof (cases "s \<in> {0..i}")
        case True
        have "(\<lambda>q :: 'n pairpath. pcut i p' s + q s) \<in> borel_measurable ?Bi"
          by (intro borel_measurable_add borel_measurable_const
              pair_law_eval_measurable[OF refl])
        then show ?thesis by (simp add: padd_apply[OF True])
      next
        case False
        have "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q s) = (\<lambda>q. undefined)"
          by (rule ext) (rule padd_outside[OF False])
        then show ?thesis by simp
      qed
    qed
  qed
  have m2: "(\<lambda>w :: 'n pairpath. pcut i w) \<in> N \<rightarrow>\<^sub>M ?Bi"
    by (rule pcut_measurable[OF i0 iT setsN])
  have eq: "{w \<in> space N. pcut i (padd T p' w) \<in> B}
      = (\<lambda>w :: 'n pairpath. pcut i w) -`
          ((\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi) \<inter> space N"
  proof -
    have "pcut i (padd T p' w) = padd i (pcut i p') (pcut i w)" for w
      by (rule pcut_padd_section[OF i0 iT])
    moreover have "pcut i w \<in> space ?Bi" if "w \<in> space N" for w
      using measurable_space[OF m2 that] .
    ultimately show ?thesis by auto
  qed
  have inner: "(\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi \<in> sets ?Bi"
    by (rule measurable_sets[OF m1 B])
  have "(\<lambda>w :: 'n pairpath. pcut i w) -`
      ((\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi) \<inter> space N
      \<in> sets (natural_filtration N 0 (\<lambda>v w. w v) i)"
    by (rule pcut_vimage_natural_filtration[OF i0 iT setsN inner])
  then show ?thesis unfolding eq .
qed

subsection \<open>The conditioning set on \<open>{\<theta> > i}\<close> lives in \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<and>\<^sub> \<^sub>\<theta>\<^sub>)\<close>\<close>

text \<open>The one set-theoretic step of the four-cell argument.  A \<open>pcut i\<close>-set
  intersected with \<open>{\<theta> > i}\<close> is an \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<and>\<^sub> \<^sub>\<theta>\<^sub>)\<close>-set: below \<open>i\<close> the cut
  \<open>{i \<and> \<theta> \<le> t}\<close> forces \<open>\<theta> \<le> t < i\<close> and so meets \<open>{\<theta> > i}\<close> in nothing, while
  from \<open>i\<close> on the cut is everything and the set is already \<open>\<F>\<^sub>i\<close>-measurable.\<close>

lemma sets_natural_filtration_eq_pcut_vimage:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)
      = {pcut s -` B \<inter> space Q | B. B \<in> sets (path_borel s :: ('n pairpath) measure)}"
proof (rule set_eqI, rule iffI)
  let ?Bs = "(path_borel s :: ('n pairpath) measure)"
  fix A :: "('n pairpath) set"
  assume "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)"
  then obtain Bs where Bs: "Bs \<in> sets ?Bs"
    and Aeq: "A = (\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}) -` Bs \<inter> space Q"
    by (rule natural_filtration_eq_restrict_vimage[OF setsQ s sT]) blast
  have "A = pcut s -` Bs \<inter> space Q" unfolding Aeq pcut_def ..
  with Bs show "A \<in> {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}" by blast
next
  let ?Bs = "(path_borel s :: ('n pairpath) measure)"
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

lemma countable_pi_system_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
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

lemma pafter_vimage_pre_sigma:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u" and uT: "u \<le> T"
    and A': "A' \<in> sets (natural_filtration (path_borel T :: ('n pairpath) measure) 0 (\<lambda>v w. w v) u)"
  shows "pafter T \<theta> -` A' \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
          (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bu = "(path_borel u :: ('n pairpath) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have maxT: "max u (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath" using uT thT by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have mafter: "pafter T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pafter_measurable[OF T0 thM th0 thT])
  obtain B where B: "B \<in> sets ?Bu" and A'eq: "A' = pcut u -` B \<inter> space ?B"
    using A' unfolding sets_natural_filtration_eq_pcut_vimage[OF refl u uT]
    by blast
  have h: "(\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> \<omega>)) \<in> P \<rightarrow>\<^sub>M ?Bu"
    by (rule measurable_compose[OF mafter pcut_measurable[OF u uT refl]])
  have vim: "pafter T \<theta> -` A' \<inter> space P
      = (\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> \<omega>)) -` B \<inter> space P"
    unfolding A'eq using measurable_space[OF mafter] by auto
  have S: "pafter T \<theta> -` A' \<inter> space P \<in> sets P"
    unfolding vim by (rule measurable_sets[OF h B])
  show ?thesis
  proof (rule pre_sigma_ofI_le[OF T0 mono maxT S])
    fix t :: real assume t: "0 \<le> t" and tT: "t \<le> T"
    show "(pafter T \<theta> -` A' \<inter> space P) \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t}
        \<in> sets (?F t)"
    proof (cases "u \<le> t")
      case False
      have e: "(pafter T \<theta> -` A' \<inter> space P)
          \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t} = {}"
        using False by auto
      show ?thesis unfolding e by simp
    next
      case True
      let ?g = "\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>))"
      have mg: "?g \<in> ?F t \<rightarrow>\<^sub>M ?Bu"
        unfolding FB
        by (rule measurable_compose
            [OF pstopped_const_measurable_filtration[OF T0 t tT]
               measurable_compose[OF pafter_measurable[OF T0 thM th0 thT]
                 pcut_measurable[OF u uT refl]]])
      have gm: "?g -` B \<inter> space P \<in> sets (?F t)"
        using measurable_sets[OF mg B] by simp
      have ev: "{\<omega> \<in> space P. \<theta> \<omega> \<le> t} \<in> sets (?F t)"
        unfolding FB spP
        by (rule path_stopping_time_event_filtration[OF T0 st thM t tT])
      have eqset: "(pafter T \<theta> -` A' \<inter> space P)
            \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t}
          = (?g -` B \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}"
      proof -
        have pt: "pcut u (pafter T \<theta> \<omega>) = ?g \<omega>"
          if mx: "max u (\<theta> \<omega>) \<le> t" and wsp: "\<omega> \<in> space P"
          for \<omega> :: "'n pairpath"
        proof -
          have le': "\<theta> \<omega> \<le> t" using mx by simp
          have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
            by (rule path_sets_fst_continuous[OF setsP wsp])
          show ?thesis
            using pcut_pafter_cut_compose[OF st tT u True le' cw] by simp
        qed
        show ?thesis unfolding vim using pt True by auto
      qed
      show ?thesis unfolding eqset using gm ev by (rule sets.Int)
    qed
  qed
qed

text \<open>The rectangle itself --- the stopping-time analogue of
  \<open>rect_vimage_natural_filtration\<close>.\<close>

lemma rect_vimage_pre_sigma_stopping:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u" and uT: "u \<le> T"
    and A: "A \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A': "A' \<in> sets (natural_filtration (path_borel T :: ('n pairpath) measure) 0 (\<lambda>v w. w v) u)"
  shows "(\<lambda>\<omega> :: 'n pairpath. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>)) -` (A \<times> A')
        \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
          (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have maxM: "(\<lambda>\<omega> :: 'n pairpath. max u (\<theta> \<omega>)) \<in> borel_measurable ?B"
    using thM by measurable
  have stmax: "{\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t} \<in> sets (?F t)"
    if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all
        [OF T0 path_stopping_time_max[OF st u uT] maxM t])
  have le: "\<theta> \<omega> \<le> max u (\<theta> \<omega>)" for \<omega> :: "'n pairpath" by simp
  have c1: "pstopped T \<theta> -` A \<inter> space P \<in> pre_sigma_of P ?F \<theta>"
    by (rule pstopped_vimage_pre_sigma[OF T0 setsP st thM A])
  have c1': "pstopped T \<theta> -` A \<inter> space P
      \<in> pre_sigma_of P ?F (\<lambda>\<omega>. max u (\<theta> \<omega>))"
    using pre_sigma_of_mono[OF le stmax] c1 by blast
  have c2: "pafter T \<theta> -` A' \<inter> space P
      \<in> pre_sigma_of P ?F (\<lambda>\<omega>. max u (\<theta> \<omega>))"
    by (rule pafter_vimage_pre_sigma[OF T0 setsP st thM u uT A'])
  have "(\<lambda>\<omega> :: 'n pairpath. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>)) -` (A \<times> A')
        \<inter> space P
      = (pstopped T \<theta> -` A \<inter> space P) \<inter> (pafter T \<theta> -` A' \<inter> space P)"
    by auto
  then show ?thesis using pre_sigma_of_Int[OF c1' c2] by simp
qed

section \<open>Sampling at \<open>u \<or> \<theta>\<close>: the increment identity and its integrand\<close>

text \<open>\<open>stopped_increment_of_horizon_gen\<close> is stated for the offset
  family \<open>(\<theta>+i) \<and> T\<close>; the additive split instead uses the delayed family
  \<open>u \<or> \<theta>\<close>.  Both are instances of one statement about an arbitrary pair of
  ordered bounded path stopping times, proved here and already abstract in
  @{thm [source] set_martingale_sampling_two}.

  Integrability of the sampled process, free in the deterministic
  development from the martingale locale, is reconstructed here from the
  dyadic approximation and the same dominating function.\<close>

lemma pcut_after_in_pre_sigma:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
  shows "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}
      \<in> pre_sigma_of Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>p'. min i (\<theta> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?C = "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}"
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spQ])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that])
  have cutB: "pcut i -` B \<inter> space Q \<in> sets (?F i)"
    by (rule pcut_vimage_natural_filtration[OF i0 iT setsQ B])
  have evi: "{p' \<in> space Q. \<theta> p' \<le> i} \<in> sets (?F i)"
    unfolding FB spQ
    by (rule path_stopping_time_event_filtration[OF T0 st thM i0 iT])
  have QP: "?C \<in> sets Q"
  proof -
    have "sets (?F i) \<subseteq> sets Q"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsQ])
    moreover have "?C = (pcut i -` B \<inter> space Q)
        - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
    ultimately show ?thesis
      using cutB evi sets.Diff sets.Int by (metis (no_types, lifting) subsetD)
  qed
  show ?thesis
  proof (rule pre_sigma_ofI[OF QP])
    fix t :: real assume t: "0 \<le> t"
    show "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} \<in> sets (?F t)"
    proof (cases "i \<le> t")
      case True
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = ?C"
        using True by auto
      moreover have "?C \<in> sets (?F i)"
      proof -
        have "?C = (pcut i -` B \<inter> space Q)
            - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
        then show ?thesis using cutB evi by (simp add: sets.Diff sets.Int)
      qed
      ultimately show ?thesis using mono[OF True] by auto
    next
      case False
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = {}"
        using False by auto
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>Clause (iv): the inner-integral identity\<close>

lemma pstopped_eval_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and r0: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> r)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<le> T")
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (simp add: pstopped_outside)
  then show ?thesis by simp
next
  case True
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?G = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  define u' where "u' = min u T"
  have u'0: "0 \<le> u'" using r0 ru True unfolding u'_def by simp
  have u'T: "u' \<le> T" unfolding u'_def by simp
  have u'u: "u' \<le> u" unfolding u'_def by simp
  have ru': "r \<le> u'" using ru True unfolding u'_def by simp
  have rmem: "r \<in> {0..T}" using r0 True by simp
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have spG: "space (?G v) = space P" for v
    unfolding natural_filtration_def by simp
  have nf: "?G v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  let ?Bu = "(path_borel u' :: ('n pairpath) measure)"

  \<comment> \<open>the truncated stopping time is measurable at level \<open>u'\<close>\<close>
  have gm: "(\<lambda>\<omega> :: 'n pairpath. min r (\<theta> \<omega>)) \<in> borel_measurable (?G u')"
  proof (rule borel_measurableI_le)
    fix t :: real
    show "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} \<in> sets (?G u')"
    proof (cases "r \<le> t")
      case True
      have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = space (?G u')"
        using True by auto
      show ?thesis unfolding e by (rule sets.top)
    next
      case False
      then have lt: "t < r" by simp
      show ?thesis
      proof (cases "0 \<le> t")
        case True
        have eqs: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}
            = {\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}" using lt sp spG by auto
        have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}
            \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t)"
          by (rule path_stopping_time_event_filtration_all[OF T0 st thM True])
        then have inG: "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t} \<in> sets (?G t)" unfolding nf .
        have "sets (?G t) \<subseteq> sets (?G u')"
          using lt ru' by (intro sets_natural_filtration_mono) simp
        with inG show ?thesis unfolding eqs by blast
      next
        case False
        then have tneg: "t < 0" by simp
        have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = {}"
        proof (rule equals0I)
          fix x :: "'n pairpath"
          assume "x \<in> {\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}"
          then have le: "min r (\<theta> x) \<le> t" by blast
          have "0 \<le> min r (\<theta> x)" using r0 th0[of x] by simp
          with le tneg show False by simp
        qed
        show ?thesis unfolding e by simp
      qed
    qed
  qed

  \<comment> \<open>the \<open>u'\<close>-cut is measurable at level \<open>u'\<close>\<close>
  have cutP: "pcut u' \<in> P \<rightarrow>\<^sub>M ?Bu" by (rule pcut_measurable[OF u'0 u'T setsP])
  have cutm: "pcut u' \<in> ?G u' \<rightarrow>\<^sub>M ?Bu"
  proof (rule measurableI)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space (?G u')"
    then have "\<omega> \<in> space P" using spG by simp
    then show "pcut u' \<omega> \<in> space ?Bu" by (rule measurable_space[OF cutP])
  next
    fix A :: "('n pairpath) set" assume A: "A \<in> sets ?Bu"
    have "pcut u' -` A \<inter> space P \<in> sets (?G u')"
      unfolding sets_natural_filtration_eq_pcut_vimage[OF setsP u'0 u'T]
      using A by blast
    then show "pcut u' -` A \<inter> space (?G u') \<in> sets (?G u')"
      unfolding spG .
  qed

  have g0: "0 \<le> min r (\<theta> \<omega>)" for \<omega> :: "'n pairpath" using r0 th0[of \<omega>] by simp
  have gu: "min r (\<theta> \<omega>) \<le> u'" for \<omega> :: "'n pairpath" using ru' by simp
  have ev: "(\<lambda>\<omega> :: 'n pairpath. pcut u' \<omega> (min r (\<theta> \<omega>)))
      \<in> borel_measurable (?G u')"
    by (rule path_eval_at_measurable_time
        [where X = "pcut u'" and g = "\<lambda>\<omega> :: 'n pairpath. min r (\<theta> \<omega>)",
          OF u'0 cutm gm g0 gu])
  have same: "(\<lambda>\<omega> :: 'n pairpath. pcut u' \<omega> (min r (\<theta> \<omega>)))
      = (\<lambda>\<omega>. pstopped T \<theta> \<omega> r)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have m: "min r (\<theta> \<omega>) \<in> {0..u'}" using g0[of \<omega>] gu[of \<omega>] by simp
    have "pcut u' \<omega> (min r (\<theta> \<omega>)) = \<omega> (min r (\<theta> \<omega>))" by (rule pcut_apply[OF m])
    also have "\<dots> = pstopped T \<theta> \<omega> r" by (rule pstopped_apply[OF rmem, symmetric])
    finally show "pcut u' \<omega> (min r (\<theta> \<omega>)) = pstopped T \<theta> \<omega> r" .
  qed
  have sub: "subalgebra (?G u) (?G u')"
    unfolding subalgebra_def using spG sets_natural_filtration_mono[OF u'u] by simp
  show ?thesis
    by (rule measurable_from_subalg[OF sub]) (use ev same in simp)
qed

subsection \<open>Stopping a horizon-capped square-integrable martingale\<close>

text \<open>The engine behind \<open>QH\<close> and \<open>QHC\<close>, abstracted out of
  \<open>exit_class_stopped_coord_martingale\<close>: its proof uses
  the localisation time only through nonnegativity and the stopping
  property, so it generalises to any stopping time verbatim.  Doob's
  envelope \<^term>\<open>Dsup\<close> supplies both the dominating function
  \<open>optional_stopping\<close> needs and the square-integrability of the stopped
  process, which is what promotes the conclusion back to a
  \<^const>\<open>horizon_sq_int_martingale\<close>.\<close>

theorem aglue_inner_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min i T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min j T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Y = "\<lambda>u p' :: 'n pairpath. fst (p' (min u T)) $ c"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the two pointwise halves\<close>
  have after: "?g u p' = indicator B (pcut i p') * ?Y u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have m: "min u T \<in> {0..T}" using u0 uT by simp
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF pair_law_eval_measurable[OF refl]
              pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have icm: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mL: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using icm measurable_compose[OF pdm Xm] by simp
    have mR: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using Xm unfolding measurable_cong_sets[OF setsK refl] by simp
    have cutAE: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mL mR])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c)
          = indicator B (pcut i p') * (?Y u p' + fst (w (min u T)) $ c)"
        using cutAE
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim padd_apply[OF m] by simp
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))" by simp
    also have "(\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))
        = ?Y u p' + (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PKi.integrable_const
        Kint[OF sp u0 uT]] by (simp add: PKi.prob_space)
    finally show ?thesis using Kmean[OF sp u0 uT] by simp
  qed

  have before: "?g j p' = ?g i p'"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
    for p'
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    define C where "C = {w \<in> space (\<kappa> p'). pcut i (padd T p' w) \<in> B}"
    have Cf: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)"
      unfolding C_def
      by (rule section_padd_in_filtration[OF i0 iT setsK pmem B])
    have CK: "C \<in> sets (\<kappa> p')"
    proof -
      have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
          \<subseteq> sets (\<kappa> p')"
        by (rule sets_natural_filtration_subset)
           (rule pair_law_eval_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have same: "?Y j p' = ?Y i p'"
    proof -
      have e1: "p' (min i T) = p' (min (min i T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' i0])
      have e2: "p' (min j T) = p' (min (min j T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' j0])
      have m1: "min (min i T) (\<theta> p') = \<theta> p'" using le iT th0[of p'] by simp
      have m2: "min (min j T) (\<theta> p') = \<theta> p'"
        using le ij jT th0[of p'] by simp
      show ?thesis using e1 e2 m1 m2 by simp
    qed
    have dec: "?g u p' = ?Y u p' * measure (\<kappa> p') C
        + set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have m: "min u T \<in> {0..T}" using u0 uT by simp
      have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
      have i1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Y u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Y u p'"] by simp
      have i2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * (fst (w (min u T)) $ c))"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "?g u p' = (\<integral>w. indicator C w * ?Y u p'
          + indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: C_def padd_apply[OF m] indicator_def)
      also have "\<dots> = (\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p'))
          + (\<integral>w. indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_add[OF i1 i2])
      also have "(\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p')) = ?Y u p' * measure (\<kappa> p') C"
        by (simp add: mult.commute Int_absorb2[OF Csub])
      finally show ?thesis unfolding set_lebesgue_integral_def by simp
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] same
      using Kinc[OF sp Cf i0 ij jT] by simp
  qed

  \<comment> \<open>the outer split: pointwise on the complement, optional sampling on \<open>?E\<close>\<close>
  have si: "set_integrable Q S (?g u)"
    if "S \<in> sets Q" "0 \<le> u" "u \<le> T" for S u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF that(1) gint[OF that(2,3)]])
  have spint: "set_lebesgue_integral Q (space Q) (?g u) = (\<integral>p'. ?g u p' \<partial>Q)"
    if "0 \<le> u" "u \<le> T" for u
    by (rule set_integral_space[OF gint[OF that]])
  have Esplit: "(\<integral>p'. ?g u p' \<partial>Q)
      = set_lebesgue_integral Q ?E (?g u)
        + set_lebesgue_integral Q (space Q - ?E) (?g u)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have dis: "?E \<inter> (space Q - ?E) = {}" by auto
    have cm: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
    have un: "?E \<union> (space Q - ?E) = space Q" by auto
    have "set_lebesgue_integral Q (?E \<union> (space Q - ?E)) (?g u)
        = set_lebesgue_integral Q ?E (?g u)
          + set_lebesgue_integral Q (space Q - ?E) (?g u)"
      by (rule set_integral_Un[OF dis si[OF Emeas u0 uT] si[OF cm u0 uT]])
    then show ?thesis unfolding un spint[OF u0 uT] .
  qed
  have cmQ: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
  have compl: "set_lebesgue_integral Q (space Q - ?E) (?g j)
      = set_lebesgue_integral Q (space Q - ?E) (?g i)"
  proof (rule set_lebesgue_integral_cong_AE[OF cmQ])
    show "?g j \<in> borel_measurable Q"
      using gint[OF j0 jT] by (simp add: borel_measurable_integrable)
    show "?g i \<in> borel_measurable Q"
      using gint[OF i0 iT] by (simp add: borel_measurable_integrable)
    show "AE x \<in> (space Q - ?E) in Q. ?g j x = ?g i x"
      using Qst AE_space
    proof eventually_elim
      case (elim x)
      then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
      show "x \<in> space Q - ?E \<longrightarrow> ?g j x = ?g i x"
      proof
        assume "x \<in> space Q - ?E"
        then have le: "\<theta> x \<le> i" using sp by simp
        show "?g j x = ?g i x" by (rule before[OF sp idem le])
      qed
    qed
  qed
  have Epart: "set_lebesgue_integral Q ?E (?g j)
      = set_lebesgue_integral Q ?E (?g i)"
  proof -
    have rew: "set_lebesgue_integral Q ?E (?g u)
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Y u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Y u x"
          by (rule after[OF x lt u0 uT])
        have iv: "indicator (?D \<inter> ?E) x = (indicator B (pcut i x) :: real)"
          using True x by (simp add: indicator_def)
        show ?thesis unfolding gv iv using True by simp
      next
        case False
        then have e1: "indicator ?E x = (0::real)" by simp
        have e2: "indicator (?D \<inter> ?E) x = (0::real)" using False by simp
        show ?thesis unfolding e1 e2 by simp
      qed
    qed
    have sti: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min i (\<theta> p'))"
      by (rule path_stopping_time_min[OF st i0 iT])
    have stj: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min j (\<theta> p'))"
      by (rule path_stopping_time_min[OF st j0 jT])
    have sMi: "(\<lambda>p' :: 'n pairpath. min i (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have sMj: "(\<lambda>p' :: 'n pairpath. min j (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have lemin: "min i (\<theta> p') \<le> min j (\<theta> p')" for p' :: "'n pairpath"
      using ij by simp
    have Cpre: "?D \<inter> ?E \<in> pre_sigma_of Q ?F (\<lambda>p'. min i (\<theta> p'))"
      by (rule pcut_after_in_pre_sigma[OF T0' setsQ st thM i0 iT B])
    have Ycont: "continuous_on {0..T} (\<lambda>s. ?Y s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have "continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. fst (p' (min s T)) $ c)
          = continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QH Ycont sti sMi stj sMj lemin Cpre])
    have valE: "?Y (min u (\<theta> p')) p' = ?Y u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
        and ui: "i \<le> u" for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
        \<in> borel_measurable borel"
    proof -
      have s: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis by (rule measurable_compose[OF s borel_measurable_nth])
    qed
    have Yfix: "?Y v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Ym: "(\<lambda>p' :: 'n pairpath. ?Y (min v (\<theta> p')) p') \<in> borel_measurable Q"
      if v0: "0 \<le> v" for v
    proof -
      have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
        by (rule measurable_ident_sets[OF setsQ])
      have thQ: "\<theta> \<in> borel_measurable Q"
        using thM measurable_cong_sets[OF setsQ refl] by blast
      have gm: "(\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T) \<in> borel_measurable Q"
        using thQ by measurable
      have g0: "0 \<le> min (min v (\<theta> p')) T"
        if "p' \<in> space Q" for p' :: "'n pairpath"
        using v0 th0[of p'] T0' by simp
      have gT: "min (min v (\<theta> p')) T \<le> T"
        if "p' \<in> space Q" for p' :: "'n pairpath" by simp
      have ev: "(\<lambda>p' :: 'n pairpath. p' (min (min v (\<theta> p')) T))
          \<in> borel_measurable Q"
        by (rule path_eval_at_measurable_time
            [where X = "\<lambda>p' :: 'n pairpath. p'"
              and g = "\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T",
              OF T0' idm gm g0 gT])
      show ?thesis by (rule measurable_compose[OF ev fcB])
    qed
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF i0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min i (\<theta> x)) x = ?Y i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min i (\<theta> x)) x = ?Y i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min i (\<theta> x)) x = ?Y i x"
            by (rule valE[OF sp idem lt i0 iT order.refl])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF j0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min j (\<theta> x)) x = ?Y j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min j (\<theta> x)) x = ?Y j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min j (\<theta> x)) x = ?Y j x"
            by (rule valE[OF sp idem lt j0 jT ij])
        qed
      qed
    qed
    show ?thesis
      unfolding rew[OF i0 iT] rew[OF j0 jT]
      using samp e1 e2 by simp
  qed
  show ?thesis
    unfolding Esplit[OF i0 iT] Esplit[OF j0 jT]
    using compl Epart by simp
qed

subsection \<open>Clause (iv): the increment identity for the glued law\<close>

text \<open>The wrapper.  @{thm [source] sets_natural_filtration_eq_pcut_vimage}
  presents the conditioning set as a \<^const>\<open>pcut\<close>-preimage,
  @{thm [source] integral_aglue_law} carries the set integral to the past
  and the continuation, and there @{thm [source] aglue_inner_increment}
  closes it.\<close>

theorem aglue_law_X_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min i T)) $ c)
       = set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min j T)) $ c)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))
      \<in> borel_measurable ?B" for u
    using AB Xm[of u] by measurable

  \<comment> \<open>transport one side\<close>
  have tr: "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
        = (\<integral>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c) \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w)
              * (fst (padd T p' w (min u T)) $ c)
            = indicator B (pcut i (padd T p' w))
              * (fst (padd T p' w (min u T)) $ c)" by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment
        [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
          i0 ij iT jT B gint[OF _ _ B]])
qed

subsection \<open>Clause (iv) for the glue: the \<open>X\<close> martingale\<close>

text \<open>Assembly.  The componentwise identity is
  @{thm [source] aglue_law_X_increment}; the vector one follows by
  @{thm [source] set_integral_vec_component}, and
  \<open>martingale_of_set_integral_eq\<close> turns it into the martingale property.
  Past the horizon the process is constant, so an index above \<open>T\<close> is pulled
  back to \<open>T\<close> before the identity is applied.\<close>

theorem aglue_law_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "\<And>c. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v c. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and RXint: "\<And>u. 0 \<le> u
      \<Longrightarrow> integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
    and msec: "\<And>A u c. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB c i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    then show ?thesis by (rule measurable_compose) (rule pair_fst_borel)
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RXint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c)" for c
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega> * (fst (\<omega> (min s T)) $ c))"
        if s: "0 \<le> s" for s
      proof -
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min s T)) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RXint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
          = set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min (min v T) T)) $ c)"
        by (rule aglue_law_X_increment
            [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
              uv(1) uvT uT vT C hiA msec[OF CR] gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c
          = set_lebesgue_integral ?R C (?X v) $ c" for c
        using comp[of c]
        unfolding set_integral_vec_component[OF CR RXint[OF uv(1)]]
          set_integral_vec_component[OF CR RXint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

subsection \<open>Clause (iv): the compensated inner-integral identity\<close>

text \<open>\<^const>\<open>outerp\<close> is quadratic, so on the product

  \<open>(outerp (fst (padd p' w s)) - snd (padd p' w s)) $ c $ d
     = Zp s p' + Zw s w + (fst (p' s) $ c * fst (w s) $ d
                           + fst (w s) $ c * fst (p' s) $ d)\<close>

  --- a past compensated entry, a continuation compensated entry, and two
  cross terms.  Inside the inner integral the past factor
  \<^term>\<open>fst (p' s)\<close> is constant, so it pulls out and what remains is a
  continuation increment: on \<open>{\<theta> > i}\<close> the vanishing of the continuation's
  mean, on \<open>{\<theta> \<le> i}\<close> its own increment identity against the section.  The
  four-cell shape is thus unchanged from the \<open>X\<close> clause, with no extra
  cross-term machinery needed.\<close>

theorem aglue_inner_increment_comp:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min i T)))
                - snd (padd T p' w (min i T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min j T)))
                - snd (padd T p' w (min j T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * ?Z u (padd T p' w) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the pathwise expansion of the compensated entry along the glue\<close>
  have expand: "?Z u (padd T p' w)
      = ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
    if "0 \<le> u" and "u \<le> T" for u p' w
  proof -
    have m: "min u T \<in> {0..T}" using that by simp
    show ?thesis
      unfolding padd_apply[OF m] by (simp add: outerp_def algebra_simps)
  qed

  have after: "?g u p' = indicator B (pcut i p') * ?Z u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have cut: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have evB: "(\<lambda>w :: 'n pairpath. w s) \<in> borel_measurable ?B" for s
      by (rule pair_law_eval_measurable[OF refl])
    have femB: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B"
      for s e
    proof -
      have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have semB: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
      for s e f
    proof -
      have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_snd_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have ZmB: "?Z v \<in> borel_measurable ?B" for v
    proof -
      have e: "?Z v = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min v T)) $ c
          * fst (\<omega> (min v T)) $ d - snd (\<omega> (min v T)) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      show ?thesis unfolding e
        by (intro borel_measurable_diff borel_measurable_times femB semB)
    qed
    have icmc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mLc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w)) \<in> borel_measurable (\<kappa> p')"
      using icmc measurable_compose[OF pdm ZmB] by simp
    have mRc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))))
        \<in> borel_measurable (\<kappa> p')"
      using ZmB[of u] femB
      unfolding measurable_cong_sets[OF setsK refl] by simp
    have i1: "integrable (\<kappa> p') (\<lambda>w. ?Z u w)" by (rule KintC[OF sp u0 uT])
    have i2: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d)"
      by (rule integrable_mult_right) (rule Kint[OF sp u0 uT])
    have i3: "integrable (\<kappa> p')
        (\<lambda>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      using integrable_mult_right[OF Kint[OF sp u0 uT],
        of "fst (p' (min u T)) $ d"] by (simp add: mult.commute)
    have z2: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have z3: "(\<integral>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have i23: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      by (rule Bochner_Integration.integrable_add[OF i2 i3])
    have z23: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i2 i3] z2 z3 by simp
    have i123: "integrable (\<kappa> p') (\<lambda>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
      by (rule Bochner_Integration.integrable_add[OF i1 i23])
    have z123: "(\<integral>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d) \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i1 i23]
        KmeanC[OF sp u0 uT] z23 by simp
    have inner: "(\<integral>w. ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))
        = ?Z u p'"
      unfolding Bochner_Integration.integral_add[OF PKi.integrable_const i123]
        z123 by (simp add: PKi.prob_space)
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mLc mRc])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w)
          = indicator B (pcut i p')
            * (?Z u p' + (?Z u w
              + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
                 + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)))"
        using cut
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim expand[OF u0 uT] ..
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))"
      by simp
    finally show ?thesis unfolding inner .
  qed

  have before: "?g j p' = ?g i p'"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
    for p'
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    define C where "C = {w \<in> space (\<kappa> p'). pcut i (padd T p' w) \<in> B}"
    have Cf: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)"
      unfolding C_def
      by (rule section_padd_in_filtration[OF i0 iT setsK pmem B])
    have CK: "C \<in> sets (\<kappa> p')"
    proof -
      have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
          \<subseteq> sets (\<kappa> p')"
        by (rule sets_natural_filtration_subset)
           (rule pair_law_eval_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
    have samev: "p' (min u T) = p' (\<theta> p')" if u: "0 \<le> u" and ui: "i \<le> u" for u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u])
      moreover have "min (min u T) (\<theta> p') = \<theta> p'"
        using le ui th0[of p'] thT[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have dec: "?g u p' = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
        + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
           + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
              + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have j1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Z u p'"] by simp
      have j2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u w)"
        using integrable_mult_indicator[OF CK KintC[OF sp u0 uT]] by simp
      have j3: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (p' (min u T)) $ c * fst (w (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT]]] by simp
      have j4: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT],
            of "fst (p' (min u T)) $ d"]] by (simp add: mult.commute)
      have "?g u p' = (\<integral>w. indicator C w * ?Z u p'
          + (indicator C w * ?Z u w
             + (indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d)
                + indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have ic: "indicator B (pcut i (padd T p' w)) = (indicator C w :: real)"
          unfolding C_def using sw by (simp add: indicator_def)
        show "indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)
            = indicator C w * ?Z u p'
              + (indicator C w * ?Z u w
                 + (indicator C w * (fst (p' (min u T)) $ c
                      * fst (w (min u T)) $ d)
                    + indicator C w * (fst (w (min u T)) $ c
                      * fst (p' (min u T)) $ d)))"
          unfolding ic expand[OF u0 uT] by (simp add: field_simps)
      qed
      also have "\<dots> = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
          + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
             + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
                + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
        using Bochner_Integration.integral_add[OF j1
            Bochner_Integration.integrable_add[OF j2
              Bochner_Integration.integrable_add[OF j3 j4]]]
          Bochner_Integration.integral_add[OF j2
            Bochner_Integration.integrable_add[OF j3 j4]]
          Bochner_Integration.integral_add[OF j3 j4]
        by simp
      finally show ?thesis .
    qed
    have zZ: "?Z j p' = ?Z i p'" using samev[OF i0 order_refl] samev[OF j0 ij]
      by simp
    have xc: "fst (p' (min j T)) $ c = fst (p' (min i T)) $ c"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have xd: "fst (p' (min j T)) $ d = fst (p' (min i T)) $ d"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have s1: "(\<integral>w. indicator C w * ?Z j p' \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i p' \<partial>(\<kappa> p'))" unfolding zZ ..
    have s2: "(\<integral>w. indicator C w * ?Z j w \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i w \<partial>(\<kappa> p'))"
      using KincC[OF sp Cf i0 ij jT]
      unfolding set_lebesgue_integral_def by simp
    have pull: "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
        = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u a e
    proof -
      have ii: "integrable (\<kappa> p') (\<lambda>w. indicator C w * fst (w (min u T)) $ e)"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
          = (\<integral>w. a * (indicator C w * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: field_simps)
      also have "\<dots> = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
        using ii by simp
      finally show ?thesis .
    qed
    have ke: "(\<integral>w. indicator C w * fst (w (min j T)) $ e \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * fst (w (min i T)) $ e \<partial>(\<kappa> p'))" for e
      using Kinc[OF sp Cf i0 ij jT, of e]
      unfolding set_lebesgue_integral_def by simp
    have s3: "(\<integral>w. indicator C w
          * (fst (p' (min j T)) $ c * fst (w (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (p' (min i T)) $ c * fst (w (min i T)) $ d) \<partial>(\<kappa> p'))"
      unfolding pull[OF j0 jT] pull[OF i0 iT] xc ke ..
    have s4: "(\<integral>w. indicator C w
          * (fst (w (min j T)) $ c * fst (p' (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (w (min i T)) $ c * fst (p' (min i T)) $ d) \<partial>(\<kappa> p'))"
    proof -
      have r: "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
          = a * (\<integral>w. indicator C w * fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
        if "0 \<le> u" and "u \<le> T" for u a
      proof -
        have "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
            = (\<integral>w. indicator C w * (a * fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
          by (rule Bochner_Integration.integral_cong[OF refl])
             (simp add: mult.commute)
        then show ?thesis unfolding pull[OF that] .
      qed
      show ?thesis unfolding r[OF j0 jT] r[OF i0 iT] xd ke ..
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] s1 s2 s3 s4 ..
  qed

  \<comment> \<open>the outer split, exactly as in the \<open>X\<close> clause\<close>
  have si: "set_integrable Q S (?g u)"
    if "S \<in> sets Q" "0 \<le> u" "u \<le> T" for S u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF that(1) gint[OF that(2,3)]])
  have spint: "set_lebesgue_integral Q (space Q) (?g u) = (\<integral>p'. ?g u p' \<partial>Q)"
    if "0 \<le> u" "u \<le> T" for u
    by (rule set_integral_space[OF gint[OF that]])
  have Esplit: "(\<integral>p'. ?g u p' \<partial>Q)
      = set_lebesgue_integral Q ?E (?g u)
        + set_lebesgue_integral Q (space Q - ?E) (?g u)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have dis: "?E \<inter> (space Q - ?E) = {}" by auto
    have cm: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
    have un: "?E \<union> (space Q - ?E) = space Q" by auto
    have "set_lebesgue_integral Q (?E \<union> (space Q - ?E)) (?g u)
        = set_lebesgue_integral Q ?E (?g u)
          + set_lebesgue_integral Q (space Q - ?E) (?g u)"
      by (rule set_integral_Un[OF dis si[OF Emeas u0 uT] si[OF cm u0 uT]])
    then show ?thesis unfolding un spint[OF u0 uT] .
  qed
  have cmQ: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
  have compl: "set_lebesgue_integral Q (space Q - ?E) (?g j)
      = set_lebesgue_integral Q (space Q - ?E) (?g i)"
  proof (rule set_lebesgue_integral_cong_AE[OF cmQ])
    show "?g j \<in> borel_measurable Q"
      using gint[OF j0 jT] by (simp add: borel_measurable_integrable)
    show "?g i \<in> borel_measurable Q"
      using gint[OF i0 iT] by (simp add: borel_measurable_integrable)
    show "AE x \<in> (space Q - ?E) in Q. ?g j x = ?g i x"
      using Qst AE_space
    proof eventually_elim
      case (elim x)
      then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
      show "x \<in> space Q - ?E \<longrightarrow> ?g j x = ?g i x"
      proof
        assume "x \<in> space Q - ?E"
        then have le: "\<theta> x \<le> i" using sp by simp
        show "?g j x = ?g i x" by (rule before[OF sp idem le])
      qed
    qed
  qed
  have Epart: "set_lebesgue_integral Q ?E (?g j)
      = set_lebesgue_integral Q ?E (?g i)"
  proof -
    have rew: "set_lebesgue_integral Q ?E (?g u)
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Z u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Z u x"
          by (rule after[OF x lt u0 uT])
        have iv: "indicator (?D \<inter> ?E) x = (indicator B (pcut i x) :: real)"
          using True x by (simp add: indicator_def)
        show ?thesis unfolding gv iv using True by simp
      next
        case False
        then have e1: "indicator ?E x = (0::real)" by simp
        have e2: "indicator (?D \<inter> ?E) x = (0::real)" using False by simp
        show ?thesis unfolding e1 e2 by simp
      qed
    qed
    have sti: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min i (\<theta> p'))"
      by (rule path_stopping_time_min[OF st i0 iT])
    have stj: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min j (\<theta> p'))"
      by (rule path_stopping_time_min[OF st j0 jT])
    have sMi: "(\<lambda>p' :: 'n pairpath. min i (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have sMj: "(\<lambda>p' :: 'n pairpath. min j (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have lemin: "min i (\<theta> p') \<le> min j (\<theta> p')" for p' :: "'n pairpath"
      using ij by simp
    have Cpre: "?D \<inter> ?E \<in> pre_sigma_of Q ?F (\<lambda>p'. min i (\<theta> p'))"
      by (rule pcut_after_in_pre_sigma[OF T0' setsQ st thM i0 iT B])
    have Zcont: "continuous_on {0..T} (\<lambda>s. ?Z s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have e: "(\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)
          = (\<lambda>s. fst (p' s) $ c * fst (p' s) $ d - snd (p' s) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      have "continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        unfolding e using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. ?Z s p')
          = continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QHC Zcont sti sMi stj sMj lemin Cpre])
    have valE: "?Z (min u (\<theta> p')) p' = ?Z u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
      for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n).
        (outerp (fst z) - snd z) $ c $ d) \<in> borel_measurable borel"
    proof -
      have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
          \<in> borel_measurable borel"
        unfolding outerp_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have n1: "(\<lambda>v :: real^'n^'n. v $ c) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI)
          (rule linear_continuous_on[OF bounded_linear_vec_nth])
      have n2: "(\<lambda>v :: real^'n. v $ d) \<in> borel_measurable borel"
        by (rule borel_measurable_nth)
      show ?thesis
        by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
    qed
    have Zfix: "?Z v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Zm: "(\<lambda>p' :: 'n pairpath. ?Z (min v (\<theta> p')) p') \<in> borel_measurable Q"
      if v0: "0 \<le> v" for v
    proof -
      have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
        by (rule measurable_ident_sets[OF setsQ])
      have thQ: "\<theta> \<in> borel_measurable Q"
        using thM measurable_cong_sets[OF setsQ refl] by blast
      have gm: "(\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T) \<in> borel_measurable Q"
        using thQ by measurable
      have g0: "0 \<le> min (min v (\<theta> p')) T"
        if "p' \<in> space Q" for p' :: "'n pairpath"
        using v0 th0[of p'] T0' by simp
      have gT: "min (min v (\<theta> p')) T \<le> T"
        if "p' \<in> space Q" for p' :: "'n pairpath" by simp
      have ev: "(\<lambda>p' :: 'n pairpath. p' (min (min v (\<theta> p')) T))
          \<in> borel_measurable Q"
        by (rule path_eval_at_measurable_time
            [where X = "\<lambda>p' :: 'n pairpath. p'"
              and g = "\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T",
              OF T0' idm gm g0 gT])
      show ?thesis by (rule measurable_compose[OF ev fcB])
    qed
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF i0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min i (\<theta> x)) x = ?Z i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min i (\<theta> x)) x = ?Z i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min i (\<theta> x)) x = ?Z i x"
            by (rule valE[OF sp idem lt i0 iT])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF j0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min j (\<theta> x)) x = ?Z j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min j (\<theta> x)) x = ?Z j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min j (\<theta> x)) x = ?Z j x"
            by (rule valE[OF sp idem lt j0 jT])
        qed
      qed
    qed
    show ?thesis
      unfolding rew[OF i0 iT] rew[OF j0 jT]
      using samp e1 e2 by simp
  qed
  show ?thesis
    unfolding Esplit[OF i0 iT] Esplit[OF j0 jT]
    using compl Epart by simp
qed

subsection \<open>Clause (iv): the compensated martingale for the glued law\<close>

lemma pfut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
  shows "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A: "A \<in> sets (path_borel r :: ('n pairpath) measure)"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
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
  \<open>martingale.set_integral_eq\<close> closes it, with integrability
  from @{thm [source] integrable_ksemi_of_distr_rect} and
  @{thm [source] integrable_kernel_integral}.  The statement is componentwise,
  since the workhorse @{thm [source] AE_zero_of_set_integral_zero} is
  real-valued and \<open>'n\<close> is finite.\<close>

theorem aglue_law_comp_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega>
          * ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min i T))) - snd (\<omega> (min i T))) $ c $ d)
      = set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min j T))) - snd (\<omega> (min j T))) $ c $ d)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have fem: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B" for s e
  proof -
    have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have sem: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
    for s e f
  proof -
    have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_snd_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have Zm: "?Z u \<in> borel_measurable ?B" for u
  proof -
    have e: "?Z u = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c
        * fst (\<omega> (min u T)) $ d - snd (\<omega> (min u T)) $ c $ d)"
      by (rule ext) (rule comp_entry_eq)
    show ?thesis unfolding e
      by (intro borel_measurable_diff borel_measurable_times fem sem)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * ?Z u \<omega>) \<in> borel_measurable ?B"
    for u using AB Zm[of u] by measurable
  have tr: "set_lebesgue_integral ?R A (?Z u)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (?Z u)
        = (\<integral>\<omega>. indicator A \<omega> * ?Z u \<omega> \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w) * ?Z u (padd T p' w) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w) * ?Z u (padd T p' w)
            = indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)"
          by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment_comp
        [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint KintC
          Kinc KincC i0 ij iT jT B gint[OF _ _ B]])
qed

lemma pfut_rcd_X_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w * ((fst (w j) - fst (w i)) $ c) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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
  \<open>sigma_finite_filtered_measure.martingale_of_set_integral_eq\<close>
  wants: the coordinate process is \<open>\<kappa> p'\<close>-integrable at almost every \<open>p'\<close>.
  This needs no filtration at all --- only that the section of a
  \<open>ksemi\<close>-integrable function is almost surely integrable, which is
  @{thm [source] AE_integrable_ksemi_section} (generalised above from real
  to Banach values).\<close>

theorem aglue_law_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "\<And>c d. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v c d. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and RCint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    and msec: "\<And>A u c d. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB c d i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu measurable_compose
            [OF pair_fst_borel outerp_borel]])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (min u T)))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu pair_snd_borel])
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RCint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c $ d)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c $ d)" for c d
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega>
          * ((outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d))"
        if s: "0 \<le> s" for s
      proof -
        have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
          by (rule bounded_linear_compose[OF bounded_linear_vec_nth
              bounded_linear_vec_nth])
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath.
            (outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RCint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
          = set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min (min v T) T)))
                  - snd (\<omega> (min (min v T) T))) $ c $ d)"
        by (rule aglue_law_comp_increment
            [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint
              KintC Kinc KincC uv(1) uvT uT vT C hiA msec[OF CR]
              gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c $ d
          = set_lebesgue_integral ?R C (?X v) $ c $ d" for c d
        using comp[of c d]
        unfolding set_integral_mat_component[OF CR RCint[OF uv(1)]]
          set_integral_mat_component[OF CR RCint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

section \<open>The additive glue lands in the class\<close>

text \<open>All four clauses hold, with no martingale hypothesis left over.
  Clauses (i)--(iii) come from \<open>exit_class_aglue_law\<close>;
  the two martingale clauses are @{thm [source] aglue_law_X_martingale} and
  @{thm [source] aglue_law_comp_martingale}.  The remaining hypotheses
  concern only the two factors --- the stopped past \<open>Q\<close> and the
  continuation kernel \<open>\<kappa>\<close> --- read off the class and the r.c.d. by a caller.\<close>

lemma aglue_law_X_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
  shows "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> ?t)) \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      fst (padd T (fst p) (snd p) ?t)) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  interpret PQ': prob_space Q by (rule PQ)
  have hint: "integrable Q (\<lambda>p'. norm (fst (p' ?t)) + CX)"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QXint]
        PQ'.integrable_const)
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T (fst (p', w)) (snd (p', w)) ?t)))
        \<partial>(\<kappa> p')) \<le> ennreal (norm (fst (p' ?t)) + CX)"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have iN: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have dom: "norm (fst (padd T p' w ?t)) \<le> norm (fst (p' ?t)) + norm (fst (w ?t))"
      for w :: "'n pairpath"
      unfolding padd_eval_split(1)[OF tm] by (rule norm_triangle_ineq)
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (fst (padd T p' w ?t)))"
    proof (rule Bochner_Integration.integrable_bound
        [OF Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
      show "(\<lambda>w. norm (fst (padd T p' w ?t))) \<in> borel_measurable (\<kappa> p')"
      proof -
        have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
        have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
          by (rule padd_measurable_left[OF T0])
             (use sp space_of_path_sets[OF setsQ] in simp)
        from measurable_compose[OF this hb]
        have mm: "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t)) \<in> borel_measurable ?B" .
        then have "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t))
            \<in> borel_measurable (\<kappa> p')"
          using measurable_cong_sets[OF sK refl] by blast
        then show ?thesis by measurable
      qed
      show "AE w in \<kappa> p'. norm (norm (fst (padd T p' w ?t)))
          \<le> norm (norm (fst (p' ?t)) + norm (fst (w ?t)))"
        using dom by (intro AE_I2) simp
    qed
    have "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (fst (p' ?t)) + norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono
          [OF iP Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
         (use dom in simp)
    also have "\<dots> = norm (fst (p' ?t)) + (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PK.integrable_const iN]
      by (simp add: PK.prob_space)
    also have "\<dots> \<le> norm (fst (p' ?t)) + CX" using KXbnd[OF sp] by simp
    finally have le: "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> norm (fst (p' ?t)) + CX" .
    have "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T p' w ?t))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (fst (p' ?t)) + CX)"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> ?t))
      = integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

text \<open>\<open>RCint\<close>.  \<^const>\<open>outerp\<close> is quadratic, so the glued compensated entry
  is not the sum of the two factors': @{thm [source] outerp_add} produces
  two cross terms, whose norms @{thm [source] norm_outer_prod} evaluates
  exactly.  The inner bound has the third shape
  @{thm [source] integrable_ksemi_of_past_bound} was written for.\<close>

lemma pfut_rcd_X_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w u))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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
  \<open>prob_space.unif_integrable_of_averaging\<close> applies verbatim
  and \<open>finite_measure.vitali_convergence\<close> finishes, both from
  @{theory Continuous_Path_Spaces.Conditional_UI}.

  Larsson--Ruf's argument instead uses a regular conditional distribution
  citing Stroock--Varadhan, Thm 1.3.4; their classical conditioning theorem
  needs none of this because the martingale problem there is stated with
  test functions in \<open>C\<^sub>c\<^sup>\<infinity>\<close>, whose martingales are bounded, while the
  paper's class (1.7) makes \<open>X\<close> itself and \<open>outerp X - Y\<close> the martingales,
  and those are not.\<close>

lemma aglue_law_comp_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and QCint: "integrable Q
      (\<lambda>p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KCint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. outerp (fst (w (min u T))) - snd (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
    and KCbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
      norm (outerp (fst (w (min u T))) - snd (w (min u T))) \<partial>(\<kappa> p')) \<le> CC"
  shows "integrable (aglue_law T \<kappa> Q)
      (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  let ?C = "\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> ?t)) - snd (\<omega> ?t)"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  interpret PQ': prob_space Q by (rule PQ)
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "?C \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      ?C (padd T (fst p) (snd p))) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  have hint: "integrable Q
      (\<lambda>p'. norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QCint]
        PQ'.integrable_const Bochner_Integration.integrable_mult_right
        integrable_mult_left integrable_norm[OF QXint])
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T (fst (p', w)) (snd (p', w)))))
        \<partial>(\<kappa> p'))
      \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have iNC: "integrable (\<kappa> p') (\<lambda>w. norm (?C w))"
      by (rule integrable_norm[OF KCint[OF sp]])
    have iNX: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have iB: "integrable (\<kappa> p') (\<lambda>w. norm (?C p') + norm (?C w)
        + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iNC
          Bochner_Integration.integrable_mult_right integrable_mult_left iNX)
    have dom: "norm (?C (padd T p' w))
        \<le> norm (?C p') + norm (?C w) + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))"
      for w :: "'n pairpath" by (rule padd_comp_norm_le[OF tm])
    have mP: "(\<lambda>w :: 'n pairpath. norm (?C (padd T p' w)))
        \<in> borel_measurable (\<kappa> p')"
    proof -
      have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
        by (rule padd_measurable_left[OF T0])
           (use sp space_of_path_sets[OF setsQ] in simp)
      from measurable_compose[OF this hb]
      have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w)) \<in> borel_measurable ?B" .
      then have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w))
          \<in> borel_measurable (\<kappa> p')"
        using measurable_cong_sets[OF sK refl] by blast
      then show ?thesis by measurable
    qed
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (?C (padd T p' w)))"
      by (rule Bochner_Integration.integrable_bound[OF iB mP])
         (use dom in \<open>intro AE_I2, simp\<close>)
    have "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (?C p') + norm (?C w)
            + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iB]) (use dom in simp)
    also have "\<dots> = norm (?C p') + (\<integral>w. norm (?C w) \<partial>(\<kappa> p'))
        + 2 * (norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p')))"
      using iNC iNX PK.integrable_const
      by (simp add: PK.prob_space algebra_simps)
    also have "\<dots> \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))"
    proof -
      have b1: "(\<integral>w. norm (?C w) \<partial>(\<kappa> p')) \<le> CC" by (rule KCbnd[OF sp])
      have b2: "norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))
          \<le> norm (fst (p' ?t)) * CX"
        by (rule mult_left_mono[OF KXbnd[OF sp] norm_ge_zero])
      from b1 b2 show ?thesis by linarith
    qed
    finally have le: "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))" .
    have "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T p' w))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) ?C
      = integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

subsection \<open>\<open>msecX\<close> and \<open>msecC\<close>\<close>

text \<open>One generic lemma covers both, and \<open>gintX\<close>/\<open>gintC\<close> too: the
  conditioning factor enters only through being measurable and bounded by
  \<open>1\<close> --- an \<open>indicator\<close> for \<open>msec\<close>, an indicator composed with
  \<^const>\<open>pcut\<close> for \<open>gint\<close>.\<close>

lemma aglue_section_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
  shows "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      cc (padd T (fst p) (snd p)) * h (padd T (fst p) (snd p)))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    using measurable_compose[OF pmP cb] measurable_compose[OF pmP hb] by simp
  have gi: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
    if sp: "p' \<in> space Q" for p'
  proof (rule Bochner_Integration.integrable_bound[OF Kint[OF sp]])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
      by (rule padd_measurable_left[OF T0])
         (use sp space_of_path_sets[OF setsQ] in simp)
    have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable ?B"
      using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
    then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable (\<kappa> p')"
      using measurable_cong_sets[OF sK refl] by blast
  next
    show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))"
    proof (intro AE_I2)
      fix w :: "'n pairpath"
      have "norm (cc (padd T p' w) * h (padd T p' w))
          = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
        by (rule mult_right_mono[OF c1]) simp
      finally show "norm (cc (padd T p' w) * h (padd T p' w))
          \<le> norm (h (padd T p' w))" by simp
    qed
  qed
  show ?thesis
    by (rule integral_kernel_measurable
        [where g = "\<lambda>p' w. cc (padd T p' w) * h (padd T p' w)", OF Kp gm gi])
qed

corollary aglue_msec_X:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

text \<open>\<open>gintX\<close>/\<open>gintC\<close>: the same section integral, now integrable in the
  past.  Bounded by \<open>1\<close>, the conditioning factor cannot enlarge the inner
  integral, so the past bound that already served \<open>RXint\<close>/\<open>RCint\<close> serves
  here too.\<close>

lemma aglue_section_int_at:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and sp: "p' \<in> space Q"
  shows "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
proof (rule Bochner_Integration.integrable_bound[OF Kint])
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
  have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule padd_measurable_left[OF T0])
       (use sp space_of_path_sets[OF setsQ] in simp)
  have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
  then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable (\<kappa> p')"
    using measurable_cong_sets[OF sK refl] by blast
next
  show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
      \<le> norm (h (padd T p' w))"
  proof (intro AE_I2)
    fix w :: "'n pairpath"
    have "norm (cc (padd T p' w) * h (padd T p' w))
        = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
      by (rule mult_right_mono[OF c1]) simp
    finally show "norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))" by simp
  qed
qed

lemma aglue_section_integrable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))"
proof -
  have m: "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF HBi m])
    show "AE p' in Q. norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
        \<le> norm (HB p')"
    proof (rule eventually_mono[OF AE_space])
      fix p' :: "'n pairpath" assume sp: "p' \<in> space Q"
      have iH: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))" by (rule Kint[OF sp])
      have iA: "integrable (\<kappa> p') (\<lambda>w. \<bar>h (padd T p' w)\<bar>)"
        using iH by simp
      have iCH: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
        by (rule aglue_section_int_at[OF T0 setsQ Kp hb cb c1 iH sp])
      have "\<bar>\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p')\<bar>
          \<le> (\<integral>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_mono[OF _ iA])
        show "integrable (\<kappa> p') (\<lambda>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar>)"
          using iCH by simp
        show "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
            \<le> \<bar>h (padd T p' w)\<bar>" for w :: "'n pairpath"
        proof -
          have "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
              = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>"
            by (simp add: abs_mult)
          also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
            by (rule mult_right_mono[OF c1]) simp
          finally show ?thesis by simp
        qed
      qed
      also have "\<dots> \<le> HB p'" by (rule Kbnd[OF sp])
      finally show "norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
          \<le> norm (HB p')" by simp
    qed
  qed
qed

corollary aglue_msec_C:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

subsection \<open>\<open>gintX\<close> and \<open>gintC\<close>\<close>

corollary aglue_gint_X:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (path_borel i :: ('n pairpath) measure)"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>fst (padd T p' w (min u T)) $ e\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e) \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed

corollary aglue_gint_C:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (path_borel i :: ('n pairpath) measure)"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
        \<bar>(outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed


(*<*)

theorem pfut_rcd_X_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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
    show "sets ?Y = sets (path_borel ?S :: ('n pairpath) measure)" ..
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
  \<open>exit_class_pfut_comp_martingale\<close>, which lives in the
  shifted filtration and is therefore read at times \<open>i, j\<close> rather than
  \<open>r+i, r+j\<close> (the two agree, since \<open>?FP i = \<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> for \<open>i \<le> T-r\<close>); and
  the component is a matrix entry, so the bounded-linear map is
  \<open>bounded_linear_vec_nth\<close> composed with itself.\<close>

lemma pfut_rcd_comp_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w
        * ((outerp (fst (w j)) - snd (w j)
            - (outerp (fst (w i)) - snd (w i))) $ c $ d) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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

theorem pfut_rcd_comp_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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
    show "sets ?Y = sets (path_borel ?S :: ('n pairpath) measure)" ..
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
  \<open>pfut_rcd_diffquot\<close>, (iii)
  @{thm [source] pfut_rcd_X_martingale}, (iv)
  @{thm [source] pfut_rcd_comp_martingale}.  Under \<open>\<kappa> p'\<close> the starting point
  is a constant, so the shifted law lies in the class at that point and its
  essential infimum is bounded by \<open>exit_val\<close> by definition, with no
  localization and no \<open>K\<^sub>\<epsilon>\<close>.\<close>

(*<*)
end
(*>*)
