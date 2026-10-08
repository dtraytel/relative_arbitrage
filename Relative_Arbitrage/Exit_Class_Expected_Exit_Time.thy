section \<open>Application: the expected exit time of the class \<open>P\<^sub>x\<close>\<close>

(*<*)
theory Exit_Class_Expected_Exit_Time
  imports
    "Continuous_Time_Martingales.Expected_Exit_Times" Exit_Class_Marginals
begin
(*>*)

text \<open>Pointwise consequences of the covariation constraint for a member of the
  uncapped pair class, from the difference quotients at time \<open>0\<close>.\<close>

lemma iexit_class_trace_lb:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and k: "k < CARD('n)"
  shows "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow> real (CARD('n) - k) * t \<le> trace (snd (\<omega> t))"
  using iexit_class_start[OF P] iexit_class_diffquot[OF P]
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix t :: real assume t: "0 \<le> t"
    show "real (CARD('n) - k) * t \<le> trace (snd (\<omega> t))"
    proof (cases "t = 0")
      case True
      then show ?thesis using elim by (simp add: trace_def)
    next
      case False
      with t have tp: "0 < t" by simp
      have "(1 / (t - 0)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> 0)) \<in> sconstraint k L"
        using elim tp by blast
      then have mem: "(1 / t) *\<^sub>R snd (\<omega> t) \<in> sconstraint k L"
        using elim by simp
      have "real (CARD('n) - k) \<le> trace ((1 / t) *\<^sub>R snd (\<omega> t))"
        by (rule sconstraint_trace_ge[OF k mem])
      with tp show ?thesis by (simp add: trace_scaleR pos_le_divide_eq)
    qed
  qed
qed

lemma iexit_class_entry_bound:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x"
  shows "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow> \<bar>snd (\<omega> t) $ i $ j\<bar> \<le> L * t"
  using iexit_class_start[OF P] iexit_class_diffquot[OF P]
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix t :: real assume t: "0 \<le> t"
    have "\<bar>snd (\<omega> t) $ i $ j - snd (\<omega> 0) $ i $ j\<bar> \<le> L * (t - 0)"
      by (rule diffquot_entry[where A = "\<lambda>s. snd (\<omega> s)" and k = k and L = L]) (use elim t in auto)
    then show "\<bar>snd (\<omega> t) $ i $ j\<bar> \<le> L * t" using elim by simp
  qed
qed

lemma iexit_class_coord_sq_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and s: "0 \<le> s"
  shows "integrable P (\<lambda>\<omega>. (fst (\<omega> s) $ i)\<^sup>2)"
proof -
  interpret PP: prob_space P by (rule iexit_class_prob[OF P])
  have evP: "(\<lambda>\<omega> :: 'n pairpath. \<omega> s) \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF iexit_class_sets[OF P] refl]
    by (rule ipath_eval_measurable[OF s])
  have g: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). snd p $ i $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have Aint: "integrable P (\<lambda>\<omega>. snd (\<omega> s) $ i $ i)"
  proof (rule PP.integrable_const_bound[of _ "\<bar>L\<bar> * s"])
    show "AE \<omega> in P. norm (snd (\<omega> s) $ i $ i) \<le> \<bar>L\<bar> * s"
      using iexit_class_entry_bound[OF P, of i i]
    proof eventually_elim
      case (elim \<omega>)
      then have "\<bar>snd (\<omega> s) $ i $ i\<bar> \<le> L * s" using s by blast
      also have "\<dots> \<le> \<bar>L\<bar> * s" using s by (intro mult_right_mono) auto
      finally show ?case by simp
    qed
    show "(\<lambda>\<omega>. snd (\<omega> s) $ i $ i) \<in> borel_measurable P"
      by (rule measurable_compose[OF evP g])
  qed
  have Cint: "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> s)) - snd (\<omega> s)) $ i $ i)"
    by (rule martingale.integrable[OF martingale_mat_nth[OF iexit_class_comp_martingale[OF P]] s])
  have "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> s)) - snd (\<omega> s)) $ i $ i + snd (\<omega> s) $ i $ i)"
    by (rule Bochner_Integration.integrable_add[OF Cint Aint])
  then show ?thesis by (simp add: outerp_def power2_eq_square)
qed

text \<open>The estimate on the pair class.  \<open>Z = |X|\<^sup>2 - tr A\<close> is the trace of the
  compensated martingale, \<open>|X|\<^sup>2 \<le> r'\<^sup>2\<close> up to the hitting time of
  \<open>{|y| \<ge> r'}\<close> (a stopping time, the hitting time of a closed set), and
  \<open>tr A\<close> grows at rate \<open>n - k\<close>.  The exit time from the closed \<open>K\<close> is below
  that hitting time for every \<open>r' > r\<close>; letting \<open>r' \<down> r\<close> and the horizon
  \<open>T \<up> \<infinity>\<close> gives the bound.\<close>

theorem iexit_class_expected_exit_time:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes P: "P \<in> iexit_class k L x" and k: "k < CARD('n)"
    and K: "closed K" and KB: "K \<subseteq> cball 0 r"
  shows "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P)
      \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
proof -
  interpret PP: prob_space P by (rule iexit_class_prob[OF P])
  let ?F = "natural_filtration P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
  let ?X = "\<lambda>t \<omega> :: 'n pairpath. fst (\<omega> t)"
  define c where "c = real (CARD('n) - k)"
  have c: "0 < c" using k by (simp add: c_def)
  define Z where "Z = (\<lambda>t \<omega> :: 'n pairpath. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
  have spP: "space P = ipath" using iexit_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
  have contw: "continuous_on {0..} \<omega>" if "\<omega> \<in> space P" for \<omega>
    using that spP by (intro ipath_continuous_on) auto
  have g1: "continuous_on UNIV (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)"
    by (intro continuous_intros)
  have g2: "continuous_on UNIV (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i)" for i
    by (intro continuous_intros)
  have g3: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). \<Sum>i\<in>UNIV. (fst p $ i)\<^sup>2 - snd p $ i $ i)"
    by (intro continuous_intros)
  have contX: "continuous_on {0..} (\<lambda>s. fst (\<omega> s))" if "\<omega> \<in> space P" for \<omega>
    by (rule continuous_on_compose2[OF g1 contw[OF that]]) auto
  have contXi: "continuous_on {0..} (\<lambda>s. fst (\<omega> s) $ i)" if "\<omega> \<in> space P" for \<omega> i
    by (rule continuous_on_compose2[OF g2 contw[OF that]]) auto
  have mgX: "martingale P ?F 0 ?X" by (rule iexit_class_X_martingale[OF P])
  have mgZ: "martingale P ?F 0 Z"
    unfolding Z_def
    by (rule martingale_bounded_linear_image[OF bounded_linear_trace iexit_class_comp_martingale[OF P]])
  have Zsum: "Z t \<omega> = (\<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2 - snd (\<omega> t) $ i $ i)" for t \<omega>
    by (simp add: Z_def trace_def outerp_def power2_eq_square sum_subtractf)
  have Zdot: "Z t \<omega> = fst (\<omega> t) \<bullet> fst (\<omega> t) - trace (snd (\<omega> t))" for t \<omega>
    by (simp add: Z_def trace_diff_matrix trace_outerp)
  have contZ: "continuous_on {0..} (\<lambda>s. Z s \<omega>)" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have "continuous_on {0..} (\<lambda>s. \<Sum>i\<in>UNIV. (fst (\<omega> s) $ i)\<^sup>2 - snd (\<omega> s) $ i $ i)"
      by (rule continuous_on_compose2[OF g3 contw[OF w]]) auto
    then show ?thesis by (simp add: Zsum)
  qed

  text \<open>Domination of \<open>Z\<close> on bounded intervals, by Doob's inequality for the
    coordinates and the Lipschitz bound on the compensator.\<close>
  have env: "\<exists>D. (AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> (fst (\<omega> s) $ i)\<^sup>2 \<le> D \<omega>)
      \<and> integrable P D" if u: "0 < u" for u i
    by (rule sq_martingale_envelope[OF PP.prob_space_axioms martingale_vec_nth[OF mgX]
          iexit_class_coord_sq_integrable[OF P] contXi u])
  define Dd where "Dd u i = (SOME D. (AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
      (fst (\<omega> s) $ i)\<^sup>2 \<le> D \<omega>) \<and> integrable P D)" for u i
  have DdP: "(AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> (fst (\<omega> s) $ i)\<^sup>2 \<le> Dd u i \<omega>)
      \<and> integrable P (Dd u i)" if u: "0 < u" for u i
    unfolding Dd_def by (rule someI_ex[OF env[OF u]])
  define D where "D u \<omega> = (\<Sum>i\<in>UNIV. Dd u i \<omega> + \<bar>L\<bar> * u)" for u \<omega>
  have Dint: "integrable P (D u)" if u: "0 < u" for u
    unfolding D_def using DdP[OF u]
    by (intro Bochner_Integration.integrable_sum Bochner_Integration.integrable_add
        PP.integrable_const) auto
  have dom: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>" if u: "0 < u" for u
  proof -
    have e1: "AE \<omega> in P. \<forall>i s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> (fst (\<omega> s) $ i)\<^sup>2 \<le> Dd u i \<omega>"
      by (intro eventually_all_finite) (use DdP[OF u] in blast)
    have e2: "AE \<omega> in P. \<forall>i t. 0 \<le> t \<longrightarrow> \<bar>snd (\<omega> t) $ i $ i\<bar> \<le> L * t"
      by (intro eventually_all_finite iexit_class_entry_bound[OF P])
    show ?thesis
      using e1 e2
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix s :: real assume s: "0 \<le> s" "s \<le> u"
        have tm: "\<bar>(fst (\<omega> s) $ i)\<^sup>2 - snd (\<omega> s) $ i $ i\<bar> \<le> Dd u i \<omega> + \<bar>L\<bar> * u" for i
        proof -
          have a: "(fst (\<omega> s) $ i)\<^sup>2 \<le> Dd u i \<omega>" using elim(1) s by blast
          have "\<bar>snd (\<omega> s) $ i $ i\<bar> \<le> L * s" using elim(2) s by blast
          also have "\<dots> \<le> \<bar>L\<bar> * u"
            using s by (intro mult_mono) auto
          finally have b: "\<bar>snd (\<omega> s) $ i $ i\<bar> \<le> \<bar>L\<bar> * u" .
          have "\<bar>(fst (\<omega> s) $ i)\<^sup>2 - snd (\<omega> s) $ i $ i\<bar>
              \<le> (fst (\<omega> s) $ i)\<^sup>2 + \<bar>snd (\<omega> s) $ i $ i\<bar>"
            using abs_triangle_ineq4[of "(fst (\<omega> s) $ i)\<^sup>2" "snd (\<omega> s) $ i $ i"] by simp
          with a b show ?thesis by linarith
        qed
        have "\<bar>Z s \<omega>\<bar> \<le> (\<Sum>i\<in>UNIV. \<bar>(fst (\<omega> s) $ i)\<^sup>2 - snd (\<omega> s) $ i $ i\<bar>)"
          unfolding Zsum by (rule sum_abs)
        also have "\<dots> \<le> D u \<omega>"
          unfolding D_def by (intro sum_mono tm)
        finally show "\<bar>Z s \<omega>\<bar> \<le> D u \<omega>" .
      qed
    qed
  qed
  have EZ0: "(\<integral>\<omega>. Z 0 \<omega> \<partial>P) = x \<bullet> x"
  proof -
    have m: "Z 0 \<in> borel_measurable P"
      using martingale.integrable[OF mgZ order_refl] by (rule borel_measurable_integrable)
    have ae: "AE \<omega> in P. Z 0 \<omega> = x \<bullet> x"
      using iexit_class_start[OF P] by eventually_elim (simp add: Zdot trace_def)
    have "(\<integral>\<omega>. Z 0 \<omega> \<partial>P) = (\<integral>\<omega>. x \<bullet> x \<partial>P)"
      by (rule integral_cong_AE[OF m _ ae]) simp
    then show ?thesis by (simp add: PP.prob_space)
  qed

  text \<open>One horizon, one radius.\<close>
  have step: "(\<integral>\<^sup>+\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))) \<partial>P)
      \<le> ennreal ((r' * r' - x \<bullet> x) / c)"
    if T: "0 \<le> T" and rr: "r < r'" and xK: "x \<in> K" for T r'
  proof -
    let ?A = "{y :: real^'n. r' \<le> norm y}"
    define tau where "tau \<omega> = etime T ?A ?X \<omega>" for \<omega>
    have xr: "norm x < r'" using xK KB rr by (auto simp: dist_norm)
    have r'0: "0 < r'" using xr norm_ge_zero[of x] by linarith
    interpret CA: cont_adapted_process P ?F ?X T
      by (intro cont_adapted_process.intro[OF martingale.axioms(2)[OF mgX]]
          cont_adapted_process_axioms.intro T continuous_on_subset[OF contX]) auto
    have Aclosed: "closed ?A" by (intro closed_Collect_le continuous_intros)
    have Ane: "?A \<noteq> {}"
    proof -
      obtain y :: "real^'n" where "norm y = r'"
        by (rule vector_choose_size[of r']) (use r'0 in auto)
      then show ?thesis by auto
    qed
    have stop: "{\<omega> \<in> space P. tau \<omega> \<le> s} \<in> sets (?F s)" if "0 \<le> s" for s
      unfolding tau_def by (rule CA.etime_stopping_time[OF Aclosed Ane that])
    have tau_nonneg: "0 \<le> tau \<omega>" for \<omega>
      unfolding tau_def by (rule etime_nonneg[OF T])
    have bound: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> Z s \<omega> + c * s \<le> r' * r'"
      using iexit_class_start[OF P] iexit_class_trace_lb[OF P k] AE_space
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix s :: real assume s: "0 \<le> s" "s \<le> tau \<omega>"
        have "fst (\<omega> s) \<in> cball 0 r'"
          using etime_stays_in_cball[OF T r'0, where X = ?X and \<omega> = \<omega> and s = s] elim xr
            continuous_on_subset[OF contX[OF elim(3)], of "{0..T}"] s
          unfolding tau_def by auto
        then have nx: "norm (fst (\<omega> s)) \<le> r'" by simp
        have "(norm (fst (\<omega> s)))\<^sup>2 \<le> r'\<^sup>2" by (rule power_mono[OF nx norm_ge_zero])
        then have "fst (\<omega> s) \<bullet> fst (\<omega> s) \<le> r' * r'"
          by (simp add: dot_square_norm power2_eq_square)
        moreover have "c * s \<le> trace (snd (\<omega> s))" using elim(2) s unfolding c_def by blast
        ultimately show "Z s \<omega> + c * s \<le> r' * r'" unfolding Zdot by linarith
      qed
    qed
    have tau_bnd: "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>P) \<le> ennreal ((r' * r' - x \<bullet> x) / c)"
      using stopping_time_integrable_bound(1)[where tau = tau, OF PP.prob_space_axioms mgZ
          contZ dom Dint tau_nonneg stop bound c]
      by (simp add: EZ0)
    have le: "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> tau \<omega>" for \<omega>
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have lt: "tau \<omega> < pexit T K (\<lambda>t. fst (\<omega> t))" by simp
      have pT: "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> T" by (rule pexit_le_T[OF T])
      from lt pT obtain s where s: "0 \<le> s" "s \<le> T" "r' \<le> norm (fst (\<omega> s))"
        "s < pexit T K (\<lambda>t. fst (\<omega> t))"
        unfolding tau_def etime_less_iff[OF T] by auto
      have notK: "fst (\<omega> s) \<notin> K" using s(3) rr KB by (auto simp: dist_norm)
      have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> s"
        by (rule pexit_le_of_mem[OF T s(1) s(2)]) (use notK in simp)
      with s(4) show False by simp
    qed
    have "(\<integral>\<^sup>+\<omega>. ennreal (pexit T K (\<lambda>t. fst (\<omega> t))) \<partial>P) \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>P)"
      by (intro nn_integral_mono ennreal_leI le)
    then show ?thesis using tau_bnd by (rule order_trans)
  qed

  show ?thesis
  proof (cases "x \<in> K")
    case False
    have "AE \<omega> in P. iexit K (\<lambda>t. fst (\<omega> t)) = 0"
      using iexit_class_start[OF P]
    proof eventually_elim
      case (elim \<omega>)
      have pe: "pexit T K (\<lambda>t. fst (\<omega> t)) = 0" if T: "0 \<le> T" for T
      proof -
        have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> 0"
          by (rule pexit_le_of_mem[OF T order_refl T]) (use elim False in simp)
        then show ?thesis
          using pexit_nonneg[OF T, where K = K and f = "\<lambda>t. fst (\<omega> t)"] by linarith
      qed
      have "iexit K (\<lambda>t. fst (\<omega> t)) \<le> 0"
        unfolding iexit_def by (rule SUP_least) (simp add: pe)
      then show ?case by simp
    qed
    then have "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P) = (\<integral>\<^sup>+\<omega>. 0 \<partial>P)"
      by (rule nn_integral_cong_AE)
    then show ?thesis by simp
  next
    case xK: True
    have xr: "norm x \<le> r" using xK KB by (auto simp: dist_norm)
    have r0: "0 \<le> r" using xr norm_ge_zero[of x] by linarith
    have meas_i: "(\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable P"
      using iexit_fst_measurable_ipath[OF K]
      by (simp add: measurable_cong_sets[OF iexit_class_sets[OF P] refl])
    have meas_n: "(\<lambda>\<omega>. ennreal (pexit (real n) K (\<lambda>t. fst (\<omega> t)))) \<in> borel_measurable P"
      for n :: nat
    proof -
      have "(\<lambda>\<omega>. min (iexit K (\<lambda>t. fst (\<omega> t))) (ennreal (real n))) \<in> borel_measurable P"
        by (intro borel_measurable_min meas_i measurable_const) simp
      then show ?thesis by (simp add: iexit_cap)
    qed
    have incseq: "incseq (\<lambda>n \<omega>. ennreal (pexit (real n) K (\<lambda>t. fst (\<omega> t))))"
      by (intro incseq_SucI le_funI ennreal_leI pexit_mono_T) auto
    have radius: "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P) \<le> ennreal ((r' * r' - x \<bullet> x) / c)"
      if rr: "r < r'" for r'
    proof -
      have "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P)
          = (\<integral>\<^sup>+\<omega>. (SUP n. ennreal (pexit (real n) K (\<lambda>t. fst (\<omega> t)))) \<partial>P)"
        by (simp add: iexit_nat_sup)
      also have "\<dots> = (SUP n. \<integral>\<^sup>+\<omega>. ennreal (pexit (real n) K (\<lambda>t. fst (\<omega> t))) \<partial>P)"
        by (rule nn_integral_monotone_convergence_SUP[OF incseq meas_n])
      also have "\<dots> \<le> ennreal ((r' * r' - x \<bullet> x) / c)"
        by (rule SUP_least) (rule step[OF _ rr xK], simp)
      finally show ?thesis .
    qed
    define B where "B = (r * r - x \<bullet> x) / c"
    have B0: "0 \<le> B"
    proof -
      have "(norm x)\<^sup>2 \<le> r\<^sup>2" by (rule power_mono[OF xr norm_ge_zero])
      then have "x \<bullet> x \<le> r * r" by (simp add: dot_square_norm power2_eq_square)
      then show ?thesis unfolding B_def by (intro divide_nonneg_pos) (use c in simp_all)
    qed
    have "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P) \<le> ennreal B"
    proof (rule ennreal_le_epsilon)
      fix e :: real assume "ennreal B < top" and e: "0 < e"
      define r' where "r' = sqrt (r * r + c * e)"
      have ce: "0 < c * e" using c e by simp
      have rr: "r < r'"
      proof -
        have "sqrt (r * r) < r'" unfolding r'_def using ce by (intro real_sqrt_less_mono) simp
        then show ?thesis using r0 by simp
      qed
      have nn: "0 \<le> r * r + c * e" using ce zero_le_square[of r] by linarith
      have r'sq: "r' * r' = r * r + c * e"
        unfolding r'_def using nn by simp
      have "(r' * r' - x \<bullet> x) / c = B + e"
        unfolding r'sq B_def using c by (simp add: field_simps)
      then have "ennreal ((r' * r' - x \<bullet> x) / c) = ennreal B + ennreal e"
        using B0 less_imp_le[OF e] by simp
      with radius[OF rr] show "(\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t)) \<partial>P) \<le> ennreal B + ennreal e"
        by simp
    qed
    then show ?thesis unfolding B_def c_def .
  qed
qed

text \<open>The paper's class \<open>P\<^sub>x\<close> (laws of \<open>X\<close> alone): lift to the pair class
  along the adapted quadratic-variation functional and transport the
  integral.\<close>

theorem xclass_expected_exit_time:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)" and K :: "(real^'n) set"
  assumes Q: "Q \<in> xclass k L x" and k: "k < CARD('n)" and L: "0 \<le> L"
    and K: "closed K" and KB: "K \<subseteq> cball 0 r"
  shows "(\<integral>\<^sup>+w. iexit K w \<partial>Q) \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
proof -
  let ?\<psi> = "\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata (4 * L) w t)) {0..}"
  have L4: "0 \<le> 4 * L" using L by simp
  have "(\<integral>\<^sup>+w. iexit K w \<partial>Q) = (\<integral>\<^sup>+w. iexit K (\<lambda>t. fst (?\<psi> w t)) \<partial>Q)"
    by (intro nn_integral_cong iexit_cong_nonneg) simp
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. iexit K (\<lambda>t. fst (\<omega> t))
      \<partial>ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t)))"
    unfolding ipath_law_def
    by (rule nn_integral_distr[symmetric, OF xclass_liftify_measurable[OF Q L4]])
      (simp add: iexit_fst_measurable_ipath[OF K])
  also have "\<dots> \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
    by (rule iexit_class_expected_exit_time[OF xclass_lift_in_iexit_class[OF Q L] k K KB])
  finally show ?thesis .
qed

(*<*)
end
(*>*)
