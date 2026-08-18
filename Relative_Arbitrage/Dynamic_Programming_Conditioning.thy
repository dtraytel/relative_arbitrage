section \<open>Conditioning on the past, and the conditional law\<close>

(*<*)
theory Dynamic_Programming_Conditioning
  imports Dynamic_Programming_Pasting
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Path_Spaces.Path_Exit_Times"
    Path_Law_Sampling
begin

(*>*)

section \<open>Conditioning on the past for the \<open>\<le>\<close> half\<close>











lemma pfut_law_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and AM: "A \<in> sets P"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof (rule exit_class_diffquot_of_pairs[OF sets_pair_law_of])
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "(path_borel ?S :: ('n pairpath) measure)"
  fix p q :: real
  assume pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q"
  have setsM: "sets ?M = sets (path_borel T :: ('n pairpath) measure)" using setsP by simp
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
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF P])
  interpret PP: prob_space P by (rule exit_class_prob[OF P])
  interpret MGX: martingale P
      "natural_filtration P 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T))"
    by (rule exit_class_X_martingale[OF P])
  have AM: "A \<in> sets P" using A MGX.sets_F_subset[OF r] by blast
  have setsM: "sets ?M = sets (path_borel T :: ('n pairpath) measure)"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M (path_borel ?S :: ('n pairpath) measure)"
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
    show "sets ?Q = sets (path_borel ?S :: ('n pairpath) measure)"
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









lemma exit_class_diffquot_of_rational_pairs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
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


lemma pfut_rcd_diffquot:
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
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of r (pcut r) P.
      AE w in \<kappa> p'. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
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



































theorem exit_class_rcd_member:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> exit_class k L T x"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
  shows "AE p' in pair_law_of r (pcut r) P.
      \<kappa> p' \<in> exit_class k L (T - r) 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsR: "sets R = sets (path_borel S :: ('n pairpath) measure)"
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




theorem exit_val_cond:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
      \<longrightarrow> c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?Surv = "\<lambda>p' :: 'n pairpath. pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K"
  let ?\<Phi> = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?Surv (fst p)
      \<longrightarrow> c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
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
