section \<open>Shift equivariance, and upper semicontinuity of the value function\<close>

(*<*)
theory Exit_Class_Shift
  imports Exit_Class_Tightness
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Path_Spaces.Path_Exit_Times"
    Path_Law_Pasting
begin

(*>*)

section \<open>The shift structure of the class (Larsson--Ruf Prop. 2.2(ii))\<close>























theorem exit_class_pshift:
  fixes Q :: "('n::finite pairpath) measure" and x x0 :: "real^'n"
  assumes T: "0 \<le> T" and Q: "Q \<in> exit_class k L T x0"
  shows "pshift_law T x Q \<in> exit_class k L T (x + x0)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?cross = "\<lambda>v :: real^'n. (\<chi> i j. x $ i * v $ j + v $ i * x $ j) :: real^'n^'n"
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  have ffm: "finite_filtered_measure Q ?F 0"
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP finQ])
  have minI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have mX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule exit_class_X_martingale[OF Q])
  interpret MX: martingale Q ?F 0 "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
    by (rule mX)
  \<comment> \<open>the two almost-sure clauses\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have st': "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. fst (pshift T x \<omega> 0) = x + x0
        \<and> snd (pshift T x \<omega> 0) = 0"
    proof (rule eventually_mono[OF st])
      fix \<omega> :: "'n pairpath"
      assume "fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
      then show "fst (pshift T x \<omega> 0) = x + x0 \<and> snd (pshift T x \<omega> 0) = 0"
        using T by (simp add: pshift_fst pshift_snd)
    qed
  qed
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  have dq': "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
          \<in> sconstraint k L"
    proof (rule eventually_mono[OF dq])
      fix \<omega> :: "'n pairpath"
      assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
      proof (intro allI impI)
        fix s t :: real
        assume s: "0 \<le> s" and stt: "s < t" and tT: "t \<le> T"
        have sI: "s \<in> {0..T}" using s stt tT by simp
        have tI: "t \<in> {0..T}" using s stt tT by simp
        show "(1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
          using q s stt tT by (simp add: pshift_snd[OF sI] pshift_snd[OF tI])
      qed
    qed
  qed
  \<comment> \<open>the two martingale clauses\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MX.adapted[OF u])
  have mgX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_add_const[OF ffm mX, of x]])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. x + fst (\<omega> (min u T)))
        = (\<lambda>\<omega>. fst (pshift T x \<omega> (min u T)))"
      by (rule ext) (simp add: pshift_fst[OF minI[OF u]])
  qed
  have Xshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ Zm mgX])
  have mC: "martingale Q ?F 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule exit_class_compensated_martingale[OF Q])
  interpret MC: martingale Q ?F 0
      "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule mC)
  have mCross: "martingale Q ?F 0 (\<lambda>u \<omega>. ?cross (fst (\<omega> (min u T))))"
    by (rule martingale_bounded_linear_image[OF bounded_linear_cross mX])
  have sum2: "martingale Q ?F 0 (\<lambda>u \<omega>. outerp x
      + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
         + ?cross (fst (\<omega> (min u T)))))"
    by (rule martingale_add_const[OF ffm martingale_add[OF mC mCross]])
  have ZmC: "(\<lambda>\<omega> :: 'n pairpath.
      outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
        \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MC.adapted[OF u])
  have mgC: "martingale Q ?F 0 (\<lambda>u \<omega>.
      outerp (fst (pshift T x \<omega> (min u T))) - snd (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF sum2])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp x
        + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
           + ?cross (fst (\<omega> (min u T)))))
        = (\<lambda>\<omega>. outerp (fst (pshift T x \<omega> (min u T)))
           - snd (pshift T x \<omega> (min u T)))"
      by (rule ext)
        (simp add: pshift_fst[OF minI[OF u]] pshift_snd[OF minI[OF u]]
          comp_shift_split)
  qed
  have Cshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ ZmC mgC])
  show ?thesis
    unfolding exit_class_def
  proof (intro CollectI conjI)
    show "prob_space (pshift_law T x Q)"
      by (rule prob_space_pshift_law[OF T prob setsQ])
    show "sets (pshift_law T x Q) = sets (path_borel T :: ('n pairpath) measure)" by simp
    show "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
      by (rule st')
    show "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule dq')
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))" by (rule Xshift)
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule Cshift)
  qed
qed

text \<open>Larsson--Ruf Prop. 2.2(ii) for the paper's class, in the form the
  value function needs: the class at \<open>x\<close> is the \<open>x\<close>-translate of the class
  at \<open>0\<close>.  The reverse inclusion is the same theorem at \<open>-x\<close>, plus the fact
  that the two push-forwards compose to the identity.\<close>

corollary exit_class_shift_image:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "exit_class k L T x = pshift_law T x ` exit_class k L T 0"
proof
  show "pshift_law T x ` exit_class k L T 0 \<subseteq> exit_class k L T x"
  proof
    fix R :: "('n pairpath) measure"
    assume "R \<in> pshift_law T x ` exit_class k L T 0"
    then obtain Q0 where Q0: "Q0 \<in> exit_class k L T 0"
      and R: "R = pshift_law T x Q0" by blast
    have "pshift_law T x Q0 \<in> exit_class k L T (x + 0)"
      by (rule exit_class_pshift[OF T Q0])
    then show "R \<in> exit_class k L T x" using R by simp
  qed
  show "exit_class k L T x \<subseteq> pshift_law T x ` exit_class k L T 0"
  proof
    fix Q :: "('n pairpath) measure"
    assume Q: "Q \<in> exit_class k L T x"
    let ?B = "(path_borel T :: ('n pairpath) measure)"
    have setsQ: "sets Q = sets ?B" by (rule exit_class_sets[OF Q])
    have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF setsQ])
    have mem0: "pshift_law T (- x) Q \<in> exit_class k L T 0"
      using exit_class_pshift[OF T Q, of "- x"] by simp
    have shm: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M ?B"
      using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
    have shm2: "pshift T x \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
    have "pshift_law T x (pshift_law T (- x) Q)
        = distr Q ?B (pshift T x \<circ> pshift T (- x))"
      unfolding pshift_law_def by (rule distr_distr[OF shm2 shm])
    also have "\<dots> = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    proof (rule distr_cong)
      show "Q = Q" ..
      show "sets ?B = sets ?B" ..
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
      then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using spQ by simp
      show "(pshift T x \<circ> pshift T (- x)) \<omega> = \<omega>"
        using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
    qed
    also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
    finally have "pshift_law T x (pshift_law T (- x) Q) = Q" .
    with mem0 show "Q \<in> pshift_law T x ` exit_class k L T 0" by force
  qed
qed

section \<open>The value function of Eq. (1.6) is upper semicontinuous\<close>

subsection \<open>The shift is an involution on laws\<close>






theorem exit_val_eq_vshift_sup:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  \<comment> \<open>the \<open>0\<close> MUST be annotated: without it the class in the assumption
      elaborates at a fresh type variable and \<open>rule ne\<close> silently fails.\<close>
  assumes T: "0 \<le> T" and ne: "exit_class k L T (0 :: real^'n) \<noteq> {}"
  shows "exit_val k L T K x
      = ennreal (Sup (vshift T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K} (x, 0)
          ` exit_class k L T 0))"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "exit_class k L T 0"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))"
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)" if "Q \<in> ?C" for Q
    by (rule exit_class_sets[OF that])
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule exit_class_prob[OF that])
  have key: "ess_inf_time (pshift_law T x Q) ?g = ennreal (vshift T ?A (x, 0) Q)"
    if Q: "Q \<in> ?C" for Q
  proof -
    have "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (\<lambda>\<omega>. ?g (pshift T x \<omega>))"
      by (rule ess_inf_time_pshift_law[OF T setsQ[OF Q]])
    also have "\<dots> = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))"
      by (rule arg_cong[where f = "ess_inf_time Q"])
        (rule ext, rule pexit_pshift_eq_etime)
    finally have e: "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))" .
    have le: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) \<le> ennreal T"
      by (rule ess_inf_time_le_const[OF probQ[OF Q]]) (rule etime_le_T[OF T])
    have fin: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) < \<top>"
      using le ennreal_less_top by (rule order_le_less_trans)
    show ?thesis unfolding e vshift_def using fin by simp
  qed
  have img: "exit_class k L T x = pshift_law T x ` ?C"
    by (rule exit_class_shift_image[OF T])
  have "exit_val k L T K x
      = Sup ((\<lambda>Q. ess_inf_time Q ?g) ` (pshift_law T x ` ?C))"
    unfolding exit_val_def img ..
  also have "\<dots> = Sup ((\<lambda>Q. ess_inf_time (pshift_law T x Q) ?g) ` ?C)"
    by (simp add: image_image)
  also have "\<dots> = Sup ((\<lambda>Q. ennreal (vshift T ?A (x, 0) Q)) ` ?C)"
    using key by (intro arg_cong[where f = Sup] image_cong refl)
  also have "\<dots> = Sup (ennreal ` (vshift T ?A (x, 0) ` ?C))"
    by (simp add: image_image)
  also have "\<dots> = ennreal (Sup (vshift T ?A (x, 0) ` ?C))"
  proof (rule ennreal_Sup_image[where B = T])
    show "vshift T ?A (x, 0) ` ?C \<noteq> {}"
      unfolding image_is_empty by (rule ne)
    fix s :: real assume "s \<in> vshift T ?A (x, 0) ` ?C"
    then obtain Q where Q: "Q \<in> ?C" and s: "s = vshift T ?A (x, 0) Q" by blast
    have "0 \<le> s" unfolding s vshift_def by simp
    moreover have "s \<le> T" unfolding s by (rule vshift_le[OF T probQ[OF Q]])
    ultimately show "0 \<le> s \<and> s \<le> T" by blast
  qed
  finally show ?thesis .
qed

subsection \<open>Clause (1) of Theorem 1.1, for the paper's own value function\<close>

text \<open>\<open>exit_val\<close> is Eq. (1.6): the supremum, over the class (1.7) started at
  \<open>x\<close>, of the essential infimum of the exit time from \<open>K\<close>.  Upper
  semicontinuity in \<open>x\<close> is exactly clause (1).  The class is sequentially
  compact and shift-equivariant (Prop. 2.2(ii)), so Berge applies through
  \<open>Exit_Time_Semicontinuity.vshift_sup_usc_of_seq_compact\<close>, whose remaining
  hypothesis, nonemptiness of the class at \<open>0\<close>, is supplied by a separate
  construction.\<close>

theorem exit_val_usc:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "0 \<le> L" and K: "closed K"
    and ne: "exit_class k L T (0 :: real^'n) \<noteq> {}"
    and lt: "exit_val k L T K x < b"
  shows "eventually (\<lambda>y. exit_val k L T K y < b) (nhds x)"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "exit_class k L T (0 :: real^'n)"
  let ?S = "\<lambda>y :: real^'n. Sup (vshift T ?A (y, 0) ` ?C)"
  let ?e = "\<lambda>y :: real^'n. (y, 0 :: real^'n^'n)"
  have T0: "0 \<le> T" using T by simp
  have Aopen: "open ?A"
  proof -
    have e: "?A = (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) -` (- K)" by auto
    show ?thesis unfolding e by (rule open_vimage_fst[OF open_Compl[OF K]])
  qed
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule exit_class_prob[OF that])
  have eqv: "exit_val k L T K y = ennreal (?S y)" for y :: "real^'n"
    by (rule exit_val_eq_vshift_sup[OF T0 ne])
  have bdd: "bdd_above (vshift T ?A (y, 0) ` ?C)" for y :: "real^'n"
    by (rule bdd_aboveI[of _ T]) (auto intro: vshift_le[OF T0] probQ)
  have S0: "0 \<le> ?S y" for y :: "real^'n"
  proof -
    from ne obtain Q0 :: "('n pairpath) measure" where Q0: "Q0 \<in> ?C" by auto
    have "0 \<le> vshift T ?A (y, 0) Q0" unfolding vshift_def by simp
    also have "\<dots> \<le> ?S y" using Q0 bdd by (intro cSup_upper) auto
    finally show ?thesis .
  qed
  have usc: "eventually (\<lambda>z. Sup (vshift T ?A z ` ?C) < c) (nhds (?e x))"
    if c: "?S x < c" for c :: real
  proof (rule vshift_sup_usc_of_seq_compact[OF T0 Aopen])
    show "?C \<noteq> {}" by (rule ne)
    show "sets Q = sets (path_borel T :: ('n pairpath) measure)" if "Q \<in> ?C" for Q
      by (rule exit_class_sets[OF that])
    show "prob_space Q" if "Q \<in> ?C" for Q by (rule probQ[OF that])
    show "\<exists>Lm r. Lm \<in> ?C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) Lm sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
      if "range \<sigma> \<subseteq> ?C" for \<sigma> :: "nat \<Rightarrow> ('n pairpath) measure"
    proof -
      have mem: "\<sigma> m \<in> ?C" for m using that by auto
      have ex: "\<exists>a Q. strict_mono a \<and> Q \<in> ?C \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
        by (rule exit_class_convergent_subsequence[OF T L mem])
      obtain a where ea: "\<exists>Q. strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ex by (rule exE)
      obtain Q where h: "strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ea by (rule exE)
      show ?thesis
        by (rule exI[of _ Q], rule exI[of _ a]) (use h in simp)
    qed
    show "?S x < c" by (rule c)
  qed
  obtain c :: real where cS: "?S x < c" and cb: "ennreal c \<le> b"
  proof (cases "b = \<top>")
    case True
    show thesis by (rule that[of "?S x + 1"]) (simp_all add: True)
  next
    case False
    then have blt: "b < \<top>" by (simp add: less_top)
    have bb: "b = ennreal (enn2real b)" using blt by simp
    have "ennreal (?S x) < b" using lt eqv by simp
    then have "ennreal (?S x) < ennreal (enn2real b)" using bb by simp
    \<comment> \<open>\<open>ennreal_less_iff\<close> carries its nonnegativity on the LEFT argument.\<close>
    then have "?S x < enn2real b"
      using S0[of x] by (simp add: ennreal_less_iff)
    then show thesis by (rule that) (use bb in simp)
  qed
  from usc[OF cS] obtain U where U: "open U" and xU: "?e x \<in> U"
    and UP: "\<And>z. z \<in> U \<Longrightarrow> Sup (vshift T ?A z ` ?C) < c"
    unfolding eventually_nhds by blast
  show ?thesis
    unfolding eventually_nhds
  proof (intro exI[of _ "?e -` U"] conjI ballI)
    show "open (?e -` U)"
      by (rule open_vimage[OF U]) (intro continuous_intros)
    show "x \<in> ?e -` U" using xU by simp
    fix y :: "real^'n" assume y: "y \<in> ?e -` U"
    have "?S y < c" using UP[of "?e y"] y by simp
    then have "ennreal (?S y) < ennreal c"
      using S0[of y] by (simp add: ennreal_less_iff)
    also have "\<dots> \<le> b" by (rule cb)
    finally show "exit_val k L T K y < b" using eqv[of y] by simp
  qed
qed


(*<*)
end
(*>*)
