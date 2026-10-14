section \<open>The \<open>X\<close>-marginals of the class on the half-line\<close>

(*<*)
theory Covariation_Class_Marginals
  imports
    Covariation_Density Covariation_Class_Infinite
begin
(*>*)

text \<open>
  \<open>icovariation_class S x\<close> is a set of laws of the PAIR \<open>(X, \<langle>X\<rangle>)\<close>; the class
  of \<^cite>\<open>LaiShkolnikovSoner\<close>, Eq. (1.7), is a set of laws of \<open>X\<close> alone, constrained
  through \<open>d\<langle>X\<rangle>(t)/dt\<close>.  This theory states that class for any constraint set \<open>S\<close>
  and identifies the two for every closed, convex, bounded \<open>S\<close> of
  positive semidefinite matrices.

  The covariation is phrased EXISTENTIALLY: a law belongs to the class when
  SOME continuous adapted \<open>A\<close> compensates \<open>X X\<^sup>T\<close> and has the required rate.
  That is faithful --- \<open>d\<langle>X\<rangle>/dt \<in> S\<close> says exactly that \<open>\<langle>X\<rangle>\<close> is such
  an \<open>A\<close>, and the compensator is unique up to indistinguishability --- and it is
  what makes both inclusions fall out of \<open>qvmat_eq_A_sym\<close>: such an \<open>A\<close> is forced
  to agree with \<open>qvmat\<close>, which is a functional of the path alone.
\<close>

text \<open>The adapted continuous version of the quadratic-variation functional
  --- \<open>qvp_good\<close>, \<open>qvp_goodupto\<close>, \<open>qvpc\<close>, \<open>qvsa\<close> and \<open>qvmata\<close> ---
  lives in @{theory Continuous_Path_Spaces.Adapted_Quadratic_Variation}.\<close>

subsection \<open>The class of laws of \<open>X\<close>\<close>

definition xcovariation_class ::
  "(real^'n::finite^'n) set \<Rightarrow> real^'n \<Rightarrow> ((real \<Rightarrow> real^'n) measure) set"
  where
  "xcovariation_class S x = {Q.
     prob_space Q \<and>
     sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure)) \<and>
     (AE w in Q. w 0 = x) \<and>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t) \<and>
     (\<exists>A. (AE w in Q. A 0 w = 0) \<and>
          martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
            (\<lambda>t w. outerp (w t) - A t w) \<and>
          (AE w in Q. density_cond (\<lambda>t. A t w) S))}"

definition xcovariation_val ::
  "(real^'n::finite^'n) set \<Rightarrow> (real^'n) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "xcovariation_val S K x = Sup ((\<lambda>Q. ess_inf Q (iexit K)) ` xcovariation_class S x)"

text \<open>The difference-quotient reading, which the development below works
  with.  For a closed, convex, bounded \<open>S\<close> it is the same condition: see
  \<open>dq_iff_density\<close>.\<close>

lemma xcovariation_class_eq_dq:
  fixes S :: "(real^'n::finite^'n) set"
  assumes Sc: "closed S" and Sv: "convex S" and Sb: "bounded S"
  shows "xcovariation_class S x = {Q.
     prob_space Q \<and>
     sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure)) \<and>
     (AE w in Q. w 0 = x) \<and>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t) \<and>
     (\<exists>A. (AE w in Q. A 0 w = 0) \<and>
          martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
            (\<lambda>t w. outerp (w t) - A t w) \<and>
          (AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
             (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S))}"
proof -
  have iff: "density_cond g S
      \<longleftrightarrow> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
             (1 / (t - s)) *\<^sub>R (g t - g s) \<in> S)"
    for g :: "real \<Rightarrow> real^'n^'n"
    using dq_iff_density[OF Sv Sc Sb, of g]
    unfolding dq_cond_def by blast
  show ?thesis unfolding xcovariation_class_def by (simp add: iff)
qed

lemma xcovariation_class_prob: "Q \<in> xcovariation_class S x \<Longrightarrow> prob_space Q"
  unfolding xcovariation_class_def by blast

lemma xcovariation_class_sets:
  "Q \<in> xcovariation_class S x \<Longrightarrow> sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n::finite) measure))"
  unfolding xcovariation_class_def by blast

lemma xcovariation_class_start: "Q \<in> xcovariation_class S x \<Longrightarrow> AE w in Q. w 0 = x"
  unfolding xcovariation_class_def by blast

lemma xcovariation_class_martingale:
  "Q \<in> xcovariation_class S x \<Longrightarrow>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t)"
  unfolding xcovariation_class_def by blast

text \<open>An entrywise bound makes a set of matrices bounded.\<close>

lemma bounded_of_entry_bound:
  fixes S :: "(real^'n::finite^'n) set"
  assumes D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
  shows "bounded S"
proof (rule boundedI)
  fix a assume a: "a \<in> S"
  have "norm a \<le> (\<Sum>i\<in>UNIV. norm (a $ i))"
    unfolding norm_vec_def by (rule L2_set_le_sum) simp
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>a $ i $ j\<bar>)"
    by (intro sum_mono norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). D)"
    by (intro sum_mono D[OF a])
  finally show "norm a \<le> real CARD('n) * (real CARD('n) * D)" by simp
qed

text \<open>The constraint set supplies exactly the two hypotheses the matrix locale
  of @{theory Continuous_Path_Spaces.Pathwise_Quadratic_Variation} needs: the
  increments of \<open>A\<close> are positive semidefinite, and their entries are
  Lipschitz in time.  So \<open>S\<close> is taken to consist of positive semidefinite
  matrices whose entries are bounded by some \<open>D\<close>.\<close>

text \<open>\<open>natural_filtration_pull\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}: the \<open>pull\<close>
  hypothesis of \<open>martingale_distr\<close> in the case that matters here, since the
  target filtration is the natural one of the coordinate process.\<close>

subsection \<open>What the constraint set gives the matrix hypotheses\<close>

text \<open>Positive semidefiniteness of the difference quotients is the
  monotonicity hypothesis, the entry bound is the Lipschitz one, and
  symmetry --- part of \<open>psd\<close> --- is what turns the symmetric part delivered by
  polarisation back into \<open>A\<close> itself.\<close>

lemma diffquot_psd:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> S"
    and p: "0 \<le> p" and pq: "p \<le> q"
  shows "0 \<le> y \<bullet> ((A q - A p) *v y)"
proof (cases "p < q")
  case True
  then have "(1 / (q - p)) *\<^sub>R (A q - A p) \<in> S" using dq p by blast
  then have "psd ((1 / (q - p)) *\<^sub>R (A q - A p))" by (rule psd)
  then have nn: "0 \<le> y \<bullet> (((1 / (q - p)) *\<^sub>R (A q - A p)) *v y)" by (simp add: psd_def)
  have eq: "y \<bullet> (((1 / (q - p)) *\<^sub>R (A q - A p)) *v y)
      = (y \<bullet> ((A q - A p) *v y)) / (q - p)"
    by (simp add: scaleR_matrix_vector_assoc[symmetric])
  from nn have "0 \<le> (y \<bullet> ((A q - A p) *v y)) / (q - p)" unfolding eq .
  then show ?thesis using True by (simp add: zero_le_divide_iff)
next
  case False
  then have "p = q" using pq by simp
  then show ?thesis by simp
qed

lemma diffquot_entry:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> S"
    and p: "0 \<le> p" and pq: "p \<le> q"
  shows "\<bar>A q $ i $ j - A p $ i $ j\<bar> \<le> D * (q - p)"
proof (cases "p < q")
  case True
  then have mem: "(1 / (q - p)) *\<^sub>R (A q - A p) \<in> S" using dq p by blast
  have "\<bar>(1 / (q - p)) * (A q $ i $ j - A p $ i $ j)\<bar> \<le> D"
    using D[OF mem, of i j] by simp
  then have "(1 / (q - p)) * \<bar>A q $ i $ j - A p $ i $ j\<bar> \<le> D"
    using True by (simp add: abs_mult)
  then show ?thesis using True by (simp add: field_simps)
next
  case False
  then have "p = q" using pq by simp
  then show ?thesis by simp
qed

lemma diffquot_sym:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> S"
    and A0: "A 0 = 0" and t: "0 \<le> t"
  shows "A t $ i $ j = A t $ j $ i"
proof (cases "0 < t")
  case True
  then have "(1 / (t - 0)) *\<^sub>R (A t - A 0) \<in> S" using dq by blast
  then have "(1 / t) *\<^sub>R A t \<in> S" using A0 by simp
  then have "psd ((1 / t) *\<^sub>R A t)" by (rule psd)
  then have tr: "transpose ((1 / t) *\<^sub>R A t) = (1 / t) *\<^sub>R A t" by (simp add: psd_def)
  have "transpose ((1 / t) *\<^sub>R A t) $ i $ j = ((1 / t) *\<^sub>R A t) $ i $ j"
    by (simp add: tr)
  then have "(1 / t) * (A t $ j $ i) = (1 / t) * (A t $ i $ j)"
    by (simp add: transpose_def)
  then show ?thesis using True by simp
next
  case False
  then have "t = 0" using t by simp
  then show ?thesis using A0 by simp
qed

subsection \<open>The second coordinate of a class member IS the quadratic variation\<close>

text \<open>Obligation (b) of the bridge, for an arbitrary filtered process: a
  continuous martingale \<open>X\<close> whose outer square is compensated by \<open>A\<close>, with
  \<open>A\<close> starting at \<open>0\<close> and difference quotients in the constraint set, has
  \<open>A\<close> as its adapted quadratic variation.  The side conditions are stated
  almost everywhere, while the localised identification wants them pointwise;
  the two are reconciled by restricting to a full-measure event, which is what
  the \<open>restrict_full\<close> package of
  @{theory Continuous_Time_Martingales.Stopped_Localization} is for.  The event is
  built from a null set rather than from the conditions themselves, so nothing
  has to be shown measurable --- in particular not the difference-quotient
  condition, which quantifies over all real pairs.  Both the pair class and
  the \<open>X\<close>-marginal class below are instances.\<close>

lemma qvmata_eq_compensator_AE:
  fixes Q :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" and A :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
  assumes PQ: "prob_space Q" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and mgX: "martingale Q F 0 X"
    and mgA: "martingale Q F 0 (\<lambda>t w. outerp (X t w) - A t w)"
    and contX: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s w)"
    and good: "AE w in Q. X 0 w = x \<and> A 0 w = 0 \<and> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
                (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S)"
  shows "AE w in Q. \<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * D) (\<lambda>s. X s w) t = A t w"
proof -
  interpret PQ: prob_space Q by (rule PQ)
  from good obtain N where
    N: "{w \<in> space Q. \<not> (X 0 w = x \<and> A 0 w = 0 \<and> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S))} \<subseteq> N"
    and Ne: "emeasure Q N = 0" and Ns: "N \<in> sets Q" by (rule AE_E)
  define G where "G = space Q - N"
  have Gsets: "G \<in> sets Q" unfolding G_def using Ns by simp
  have Gfull: "AE w in Q. w \<in> G"
    by (rule AE_I[where N = N]) (use Ne Ns in \<open>auto simp: G_def\<close>)
  have Gspace: "G \<subseteq> space Q" unfolding G_def by blast
  have Gstart: "X 0 w = x" and GA0: "A 0 w = 0"
    and Gdq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S" if "w \<in> G" for w
    using N that unfolding G_def by blast+

  text \<open>On the restricted space every hypothesis of the localised matrix
    identification holds pointwise.\<close>
  let ?M = "restrict_space Q G"
  let ?FF = "\<lambda>t. restrict_space (F t) G"
  have spM: "space ?M = G"
    by (rule space_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
  have Xc: "martingale ?M ?FF 0 (\<lambda>v w. X v w $ i)" for i
    by (rule martingale_restrict_full[OF PQ.prob_space_axioms Gsets Gfull
          martingale_vec_nth[OF mgX]])
  have XAc: "martingale ?M ?FF 0 (\<lambda>v w. X v w $ i * X v w $ j - A v w $ i $ j)" for i j
  proof -
    have "martingale Q F 0 (\<lambda>v w. (outerp (X v w) - A v w) $ i $ j)"
      by (rule martingale_mat_nth[OF mgA])
    then have "martingale Q F 0 (\<lambda>v w. X v w $ i * X v w $ j - A v w $ i $ j)"
      by (simp add: outerp_def)
    then show ?thesis
      by (rule martingale_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
  qed
  have contc: "continuous_on {0..} (\<lambda>s. X s w $ i)" if w: "w \<in> space ?M" for w i
  proof -
    have c: "continuous_on {0..} (\<lambda>s. X s w)" using w Gspace spM by (intro contX) auto
    have g: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)" by (intro continuous_intros)
    show ?thesis by (rule continuous_on_compose2[OF g c]) auto
  qed
  have psdc: "\<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> (\<forall>y. 0 \<le> y \<bullet> ((A q w - A p w) *v y))"
    if w: "w \<in> space ?M" for w
  proof (intro allI impI)
    fix p q :: real and y :: "real^'n"
    assume pq: "0 \<le> p" "p \<le> q"
    have wG: "w \<in> G" using w spM by simp
    show "0 \<le> y \<bullet> ((A q w - A p w) *v y)"
      by (rule diffquot_psd[where A = "\<lambda>t. A t w", OF psd Gdq[OF wG] pq])
  qed
  have ratec: "\<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
      \<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> D * (q - p)" if w: "w \<in> space ?M" for w
  proof (intro allI impI)
    fix p q :: real and i j assume pq: "0 \<le> p" "p \<le> q"
    have wG: "w \<in> G" using w spM by simp
    show "\<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> D * (q - p)"
      by (rule diffquot_entry[where A = "\<lambda>t. A t w", OF D Gdq[OF wG] pq])
  qed

  have key: "AE w in ?M.
      (\<forall>i j. qvp_good (4 * D) (\<lambda>s. X s w $ i + X s w $ j)
           \<and> qvp_good (4 * D) (\<lambda>s. X s w $ i - X s w $ j))
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. X s w) t
           = (\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2))"
  proof (rule qvmat_eq_A_localised[where M = ?M and F = ?FF and X = X and A = A
           and C = D and B = "norm x"])
    show "prob_space ?M"
      by (rule prob_space_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
    show "\<And>i. martingale ?M ?FF 0 (\<lambda>v w. X v w $ i)" by (rule Xc)
    show "\<And>i j. martingale ?M ?FF 0
        (\<lambda>v w. X v w $ i * X v w $ j - A v w $ i $ j)" by (rule XAc)
    show "\<And>w i. w \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s w $ i)" by (rule contc)
    show "\<And>w. w \<in> space ?M \<Longrightarrow> A 0 w = 0" using GA0 spM by simp
    show "\<And>w. w \<in> space ?M \<Longrightarrow> \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        (\<forall>y. 0 \<le> y \<bullet> ((A q w - A p w) *v y))" by (rule psdc)
    show "\<And>w. w \<in> space ?M \<Longrightarrow> \<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        \<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> D * (q - p)" by (rule ratec)
    show "0 \<le> D" by (rule D0)
    show "0 \<le> norm x" by simp
    show "\<And>w i. w \<in> space ?M \<Longrightarrow> \<bar>X 0 w $ i\<bar> \<le> norm x"
      using Gstart spM by (simp add: component_le_norm_cart)
  qed

  text \<open>Symmetry collapses the symmetric part back to \<open>A\<close> itself.\<close>
  have L4: "0 \<le> 4 * D" using D0 by simp
  have spAE: "AE w in ?M. w \<in> space ?M" by (rule AE_I2) simp
  have sym: "AE w in ?M. \<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * D) (\<lambda>s. X s w) t = A t w"
    using key spAE
  proof eventually_elim
    case (elim w)
    then have gp: "\<And>i j. qvp_good (4 * D) (\<lambda>s. X s w $ i + X s w $ j)"
      and gm: "\<And>i j. qvp_good (4 * D) (\<lambda>s. X s w $ i - X s w $ j)"
      and ke: "\<And>t. 0 \<le> t \<Longrightarrow> qvmat (\<lambda>s. X s w) t
          = (\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2)" by blast+
    from elim have wG: "w \<in> G" using spM by simp
    have s: "A t w $ i $ j = A t w $ j $ i" if "0 \<le> t" for t i j
      by (rule diffquot_sym[where A = "\<lambda>u. A u w", OF psd Gdq[OF wG] GA0[OF wG] that])
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
      have "(\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2) = A t w"
        by (simp add: vec_eq_iff s[OF t])
      then have "qvmat (\<lambda>s. X s w) t = A t w" using ke[OF t] by simp
      then show "qvmata (4 * D) (\<lambda>s. X s w) t = A t w"
        using qvmata_eq_qvmat[OF gp gm L4] by simp
    qed
  qed
  have "AE w in Q. w \<in> G \<longrightarrow> (\<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * D) (\<lambda>s. X s w) t = A t w)"
    using sym Gsets Gspace
    by (subst (asm) AE_restrict_space_iff) (auto simp: Int_absorb2)
  with Gfull show ?thesis by eventually_elim blast
qed

theorem icovariation_class_qvmat:
  fixes P :: "('n::finite pairpath) measure"
  assumes psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and P: "P \<in> icovariation_class S x"
  shows "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow>
      qvmata (4 * D) (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
proof (rule qvmata_eq_compensator_AE[where X = "\<lambda>t \<omega>. fst (\<omega> t)"
      and A = "\<lambda>t \<omega>. snd (\<omega> t)" and x = x, OF icovariation_class_prob[OF P] psd D0 D
      icovariation_class_X_martingale[OF P]])
  show "martingale P (natural_filtration P 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule icovariation_class_comp_martingale[OF P])
  show "continuous_on {0..} (\<lambda>s. fst (\<omega> s))" if "\<omega> \<in> space P" for \<omega>
  proof -
    have "\<omega> \<in> ipath"
      using that icovariation_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
    then have "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
    then show ?thesis by (rule continuous_on_fst)
  qed
  show "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0 \<and> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S)"
    using icovariation_class_start[OF P] icovariation_class_diffquot[OF P] by eventually_elim blast
qed

subsection \<open>The two pushforwards are measurable\<close>

text \<open>Both inclusions, and the identification of the value functions, push a
  law forward along one of two maps: the \<open>X\<close>-marginal of a pair path, and
  the lift of a path by its adapted quadratic-variation functional.\<close>

lemma icovariation_class_fstify_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> icovariation_class S x"
  shows "(\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..})
      \<in> P \<rightarrow>\<^sub>M (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
proof (rule ipathify_measurable)
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable P" if "0 \<le> t" for t
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF icovariation_class_sets[OF P] refl]
      by (rule ipath_eval_measurable[OF that])
    then show ?thesis by (rule measurable_compose[OF _ pair_fst_borel])
  qed
next
  fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
  then have "\<omega> \<in> ipath"
    using icovariation_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
  then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
  have g: "continuous_on UNIV (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)"
    by (intro continuous_intros)
  show "continuous_on {0..} (\<lambda>t. fst (\<omega> t))"
    by (rule continuous_on_compose2[OF g c]) auto
qed

lemma xcovariation_class_liftify_measurable:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Q: "Q \<in> xcovariation_class S x" and C: "0 \<le> C"
  shows "(\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..})
      \<in> Q \<rightarrow>\<^sub>M (ipath_space :: (('n pairpath) measure))"
proof (rule ipathify_measurable)
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have evQ: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable Q" if "0 \<le> v" for v
    by (rule ipath_eval_measurable_sets[OF xcovariation_class_sets[OF Q] that])
  show "(\<lambda>w :: real \<Rightarrow> real^'n. (w t, qvmata C w t)) \<in> borel_measurable Q"
    if t: "0 \<le> t" for t
  proof (rule borel_measurable_Pair[OF evQ[OF t]])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w t) \<in> borel_measurable Q"
      by (rule qvmata_measurable[OF _ C])
         (use evQ measurable_compose[OF _ projB] in blast)
  qed
next
  fix w :: "real \<Rightarrow> real^'n" assume "w \<in> space Q"
  then have "w \<in> ipath" using xcovariation_class_sets[OF Q] by (simp add: sets_eq_imp_space_eq)
  then have c: "continuous_on {0..} w" by (rule ipath_continuous_on) simp
  show "continuous_on {0..} (\<lambda>t. (w t, qvmata C w t))"
    by (intro continuous_on_Pair c qvmata_continuous[OF C])
qed

subsection \<open>First inclusion: the \<open>X\<close>-marginal of a pair law is in the class of laws of \<open>X\<close>\<close>

text \<open>
  Push a member of the pair class forward along \<open>\<omega> \<mapsto> fst \<circ> \<omega>\<close>.  The compensator
  witnessing membership of the class of laws of \<open>X\<close> cannot be the second coordinate ---
  that is not a functional of the \<open>X\<close>-path --- so it has to be \<^const>\<open>qvmata\<close>,
  which the identification says agrees with it almost surely.  This is where
  being ADAPTED earns its keep: \<open>martingale_distr\<close> pulls the natural filtration
  of the image back along the map, and the second component of the map is
  \<^const>\<open>qvmata\<close>.
\<close>

text \<open>\<open>outerp_borel\<close> lives in @{theory Path_Space_Operations.Pair_Path_Laws}.\<close>

text \<open>\<open>natural_filtration_eval\<close>, the evaluations of a natural filtration in
  the two shapes the pushforward needs them, lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>


theorem icovariation_class_marginal_in_xcovariation_class:
  fixes P :: "('n::finite pairpath) measure"
  assumes Sc: "closed S" and Sv: "convex S" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and P: "P \<in> icovariation_class S x"
  shows "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t)) \<in> xcovariation_class S x"
proof -
  interpret PP: prob_space P by (rule icovariation_class_prob[OF P])
  have Sb: "bounded S" by (rule bounded_of_entry_bound[OF D])
  define C where "C = 4 * D"
  have C0: "0 \<le> C" using D0 by (simp add: C_def)
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..}"
  let ?Q = "distr P (ipath_space :: ((real \<Rightarrow> real^'n) measure)) ?\<phi>"
  let ?F = "natural_filtration P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"

  have evP: "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable P" if v: "0 \<le> v" for v
    unfolding measurable_cong_sets[OF icovariation_class_sets[OF P] refl]
    by (rule ipath_eval_measurable[OF v])
  have XmP: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> v)) \<in> borel_measurable P" if v: "0 \<le> v" for v
    by (rule measurable_compose[OF evP[OF v] pair_fst_borel])
  have phim: "?\<phi> \<in> P \<rightarrow>\<^sub>M (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
    by (rule icovariation_class_fstify_measurable[OF P])
  have into: "?\<phi> \<omega> \<in> ipath" if "\<omega> \<in> space P" for \<omega>
    using measurable_space[OF phim that] by simp

  text \<open>The identification, and the two consequences it has for the image.\<close>
  have keyq: "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow> qvmata C (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
    unfolding C_def by (rule icovariation_class_qvmat[OF psd D0 D P])
  have phicong: "qvmata C (?\<phi> \<omega>) t = qvmata C (\<lambda>s. fst (\<omega> s)) t" for \<omega> t
    by (rule qvmata_cong) simp

  text \<open>The two filtration facts that both martingale clauses need.\<close>
  interpret MF: martingale P ?F 0 "\<lambda>t \<omega>. fst (\<omega> t) :: real^'n"
    by (rule icovariation_class_X_martingale[OF P])
  have spF: "space (?F u) = space P" if "0 \<le> u" for u by (rule MF.space_F[OF that])
  have GG: "filtered_measure ?Q ?G (0::real)"
  proof -
    interpret PQ: prob_space ?Q by (rule PP.prob_space_distr[OF phim])
    have SQ: "Stochastic_Process.stochastic_process ?Q (0::real)
        (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
      by (unfold_locales) (rule ipath_eval_measurable_sets[OF sets_distr])
    show ?thesis
      by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SQ])
  qed
  have pull: "?\<phi> \<in> ?F u \<rightarrow>\<^sub>M ?G u" if u: "0 \<le> u" for u
  proof (rule natural_filtration_pull)
    fix \<omega> assume "\<omega> \<in> space (?F u)"
    then have "\<omega> \<in> space P" using spF[OF u] by simp
    then show "?\<phi> \<omega> \<in> space ?Q" using into by (simp add: space_distr)
  next
    fix v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    have e: "(\<lambda>\<omega> :: 'n pairpath. ?\<phi> \<omega> v) = (\<lambda>\<omega>. fst (\<omega> v))" using v by simp
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable (?F u)"
      by (rule natural_filtration_eval[OF v vu])
    then show "(\<lambda>\<omega> :: 'n pairpath. ?\<phi> \<omega> v) \<in> borel_measurable (?F u)"
      unfolding e by (rule measurable_compose[OF _ pair_fst_borel])
  qed
  have SP: "Stochastic_Process.stochastic_process P (0::real)
      (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
    by (unfold_locales) (rule evP)
  have FM: "filtered_measure P ?F (0::real)"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SP])
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have evF: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> v) $ i) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v i
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable (?F u)"
      by (rule natural_filtration_eval[OF v vu])
    from measurable_compose[OF this pair_fst_borel] show ?thesis
      by (rule measurable_compose[OF _ projB])
  qed
  have evG: "(\<lambda>w :: real \<Rightarrow> real^'n. w v $ i) \<in> borel_measurable (?G u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v i
    by (rule measurable_compose[OF natural_filtration_eval[OF v vu] projB])

  text \<open>Clause (i): the initial condition.\<close>
  have predx: "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
      (\<lambda>w. w 0 = x)"
  proof -
    have m: "(\<lambda>w :: real \<Rightarrow> real^'n. w 0) \<in> borel_measurable ipath_space"
      by (rule ipath_eval_measurable) simp
    have "{w \<in> space (ipath_space :: ((real \<Rightarrow> real^'n) measure)). w 0 = x}
        = (\<lambda>w :: real \<Rightarrow> real^'n. w 0) -` {x} \<inter> space ipath_space" by auto
    also have "\<dots> \<in> sets (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
      by (rule measurable_sets[OF m]) simp
    finally show ?thesis unfolding pred_def by simp
  qed
  have startQ: "AE w in ?Q. w 0 = x"
  proof (subst AE_distr_iff[OF phim predx[unfolded pred_def]])
    show "AE \<omega> in P. ?\<phi> \<omega> 0 = x"
      using icovariation_class_start[OF P] by eventually_elim simp
  qed

  text \<open>Clause (ii): the coordinate process is a martingale.\<close>
  have mgX: "martingale P ?F 0 (\<lambda>t \<omega>. fst (\<omega> t) :: real^'n)"
    by (rule icovariation_class_X_martingale[OF P])
  have XmgQ: "martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
  proof (rule martingale_distr[OF PP.prob_space_axioms phim GG pull])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. w u) \<in> borel_measurable (?G u)" if "0 \<le> u" for u
      by (rule natural_filtration_eval[OF that order_refl])
    show "martingale P ?F 0 (\<lambda>u \<omega> :: 'n pairpath. ?\<phi> \<omega> u)"
      by (rule martingale_cong_ge[OF mgX]) simp
  qed

  text \<open>Clause (iii): the compensator vanishes at \<open>0\<close>, for every path.\<close>
  have A0Q: "AE w in ?Q. qvmata C (w :: real \<Rightarrow> real^'n) 0 = 0"
    using C0 by simp

  text \<open>Clause (iv): the compensated process is a martingale.  The composite is
    a modification of the class's own compensated process, and it is adapted
    because \<^const>\<open>qvmata\<close> is.\<close>
  have mgXA: "martingale P ?F 0 (\<lambda>t \<omega>. outerp (fst (\<omega> t) :: real^'n) - snd (\<omega> t))"
    by (rule icovariation_class_comp_martingale[OF P])
  have qmF: "(\<lambda>\<omega> :: 'n pairpath. qvmata C (\<lambda>s. fst (\<omega> s)) u) \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u
    by (rule qvmata_measurable[OF _ C0]) (use evF in auto)
  have mgcomp: "martingale P ?F 0
      (\<lambda>u \<omega> :: 'n pairpath. outerp (?\<phi> \<omega> u) - qvmata C (?\<phi> \<omega>) u)"
  proof -
    have tgt: "martingale P ?F 0
        (\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u)"
    proof (rule martingale_cong_AE[OF mgXA])
      have ad: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u)
          \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
      proof -
        have "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> borel_measurable (?F u)"
          by (rule natural_filtration_eval[OF u order_refl])
        then have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) :: real^'n) \<in> borel_measurable (?F u)"
          by (rule measurable_compose[OF _ pair_fst_borel])
        then have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u)) :: real^'n^'n)
            \<in> borel_measurable (?F u)"
          by (rule measurable_compose[OF _ outerp_borel])
        then show ?thesis using qmF[OF u] by simp
      qed
      show "adapted_process P ?F 0 (\<lambda>u \<omega> :: 'n pairpath.
          outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u)"
        unfolding adapted_process_def adapted_process_axioms_def using FM ad by blast
    next
      fix u :: real assume u: "0 \<le> u"
      show "AE \<omega> in P. outerp (fst (\<omega> u)) - snd (\<omega> u)
          = outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u"
        using keyq by eventually_elim (use u in simp)
    qed
    show ?thesis by (rule martingale_cong_ge[OF tgt]) (simp add: phicong)
  qed
  have CmgQ: "martingale ?Q ?G 0
      (\<lambda>t w :: real \<Rightarrow> real^'n. outerp (w t) - qvmata C w t)"
  proof (rule martingale_distr[OF PP.prob_space_axioms phim GG pull])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)
        \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
    proof -
      have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) :: real^'n^'n)
          \<in> borel_measurable (?G u)"
        by (rule measurable_compose
              [OF natural_filtration_eval[OF u order_refl] outerp_borel])
      moreover have "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w u) \<in> borel_measurable (?G u)"
        by (rule qvmata_measurable[OF _ C0]) (use evG in auto)
      ultimately show ?thesis by simp
    qed
    show "martingale P ?F 0
        (\<lambda>u \<omega> :: 'n pairpath. outerp (?\<phi> \<omega> u) - qvmata C (?\<phi> \<omega>) u)"
      by (rule mgcomp)
  qed

  text \<open>Clause (v): the difference quotients.  The cut-down functional is
    continuous for EVERY path, so the condition over all real pairs is the
    condition over the rational ones, which is countable, hence measurable ---
    and that is what lets it be transferred along the pushforward.\<close>
  have predD: "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
      (\<lambda>w. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> S)"
  proof (rule diffquot_all_pred[OF Sc])
    show "continuous_on {0..} (qvmata C w)" for w :: "real \<Rightarrow> real^'n"
      by (rule qvmata_continuous[OF C0])
    fix r :: real
    show "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w r)
        \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
    proof (rule qvmata_measurable[OF _ C0])
      fix s :: real and i assume s: "0 \<le> s"
      show "(\<lambda>w :: real \<Rightarrow> real^'n. w s $ i)
          \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
        by (rule measurable_compose[OF ipath_eval_measurable[OF s] projB])
    qed
  qed
  have dqP: "AE \<omega> in P. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (qvmata C (?\<phi> \<omega>) t - qvmata C (?\<phi> \<omega>) s) \<in> S"
    using keyq icovariation_class_diffquot[OF P]
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      have es: "qvmata C (?\<phi> \<omega>) s = snd (\<omega> s)" using phicong elim(1) st by simp
      have et: "qvmata C (?\<phi> \<omega>) t = snd (\<omega> t)" using phicong elim(1) st by simp
      show "(1 / (t - s)) *\<^sub>R (qvmata C (?\<phi> \<omega>) t - qvmata C (?\<phi> \<omega>) s)
          \<in> S" unfolding es et using elim(2) st by blast
    qed
  qed
  have dqQ: "AE w in ?Q. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> S"
    by (subst AE_distr_iff[OF phim predD[unfolded pred_def]]) (rule dqP)

  text \<open>Assembling the five clauses.\<close>
  have "?Q \<in> xcovariation_class S x"
    unfolding xcovariation_class_eq_dq[OF Sc Sv Sb] mem_Collect_eq
  proof (intro conjI)
    show "prob_space ?Q" by (rule PP.prob_space_distr[OF phim])
    show "sets ?Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure))" by simp
    show "AE w in ?Q. w 0 = x" by (rule startQ)
    show "martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)" by (rule XmgQ)
    show "\<exists>A. (AE w in ?Q. A 0 w = 0)
        \<and> martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. outerp (w t) - A t w)
        \<and> (AE w in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
             (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S)"
      by (intro exI[of _ "\<lambda>t w :: real \<Rightarrow> real^'n. qvmata C w t"] conjI)
         (rule A0Q, rule CmgQ, rule dqQ)
  qed
  then show ?thesis unfolding ipath_law_def .
qed

subsection \<open>Second inclusion: a law of \<open>X\<close> lifts to a pair law\<close>

text \<open>
  The converse pushforward, along \<open>w \<mapsto> (w, qvmata w)\<close>.  The pair space is a
  space of CONTINUOUS paths, so the second component must be continuous for
  every path, not merely almost every one --- which is what \<^const>\<open>qvmata\<close> is,
  and what a cut at the global good event would not have given while staying
  adapted.
\<close>

lemma xcovariation_class_qvmata:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and Q: "Q \<in> xcovariation_class S x"
    and A0: "AE w in Q. A 0 w = 0"
    and mgA: "martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
                (\<lambda>t w. outerp (w t) - A t w)"
    and dqA: "AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
                (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S"
  shows "AE w in Q. \<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * D) w t = A t w"
proof (rule qvmata_eq_compensator_AE[where X = "\<lambda>t w. w t" and A = A and x = x,
      OF xcovariation_class_prob[OF Q] psd D0 D
      xcovariation_class_martingale[OF Q] mgA])
  show "continuous_on {0..} (\<lambda>s. w s)" if "w \<in> space Q" for w
  proof -
    have "w \<in> ipath" using that xcovariation_class_sets[OF Q] by (simp add: sets_eq_imp_space_eq)
    then show ?thesis by (rule ipath_continuous_on) simp
  qed
  show "AE w in Q. w 0 = x \<and> A 0 w = 0 \<and> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S)"
    using xcovariation_class_start[OF Q] A0 dqA by eventually_elim blast
qed

text \<open>The two events of the pair path space that the lift has to hit: the
  initial condition, and the constraint on the difference quotients.  Both are
  measurable, the second because every point of the path space IS a continuous
  path, so the condition over all real pairs is the countable condition over the
  rational ones.\<close>


lemma pairpath_diffquot_sets:
  assumes Sc: "closed S"
  shows "{\<omega> \<in> space (ipath_space :: (('n::finite pairpath) measure)).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}
    \<in> sets ipath_space"
proof -
  have "Measurable.pred (ipath_space :: (('n pairpath) measure))
      (\<lambda>\<omega>. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S)"
  proof (rule diffquot_all_pred[OF Sc])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space ipath_space"
    then have "continuous_on {0..} \<omega>" by (intro ipath_continuous_on) simp_all
    then show "continuous_on {0..} (\<lambda>t. snd (\<omega> t))" by (intro continuous_intros)
  next
    fix t :: real assume "0 \<le> t"
    then show "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> t)) \<in> borel_measurable ipath_space"
      by (rule measurable_compose[OF ipath_eval_measurable pair_snd_borel])
  qed
  then show ?thesis unfolding pred_def .
qed

theorem xcovariation_class_lift_in_icovariation_class:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Sc: "closed S" and Sv: "convex S" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and Q: "Q \<in> xcovariation_class S x"
  shows "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * D) w t)) \<in> icovariation_class S x"
proof -
  interpret PQ: prob_space Q by (rule xcovariation_class_prob[OF Q])
  have Sb: "bounded S" by (rule bounded_of_entry_bound[OF D])
  define C where "C = 4 * D"
  have C0: "0 \<le> C" using D0 by (simp add: C_def)
  let ?\<psi> = "\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..}"
  let ?P = "distr Q (ipath_space :: (('n pairpath) measure)) ?\<psi>"
  let ?F = "natural_filtration Q 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
  let ?G = "natural_filtration ?P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"

  from Q obtain A where A0: "AE w in Q. A 0 w = 0"
    and mgA: "martingale Q ?F 0 (\<lambda>t w. outerp (w t) - A t w)"
    and dqA: "AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
                (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> S"
    unfolding xcovariation_class_eq_dq[OF Sc Sv Sb] by blast
  have keyq: "AE w in Q. \<forall>t. 0 \<le> t \<longrightarrow> qvmata C w t = A t w"
    unfolding C_def by (rule xcovariation_class_qvmata[OF psd D0 D Q A0 mgA dqA])

  have mgX: "martingale Q ?F 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
    by (rule xcovariation_class_martingale[OF Q])
  have evQ: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable Q" if v: "0 \<le> v" for v
    by (rule ipath_eval_measurable_sets[OF xcovariation_class_sets[OF Q] v])
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have qmQ: "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w v) \<in> borel_measurable Q"
    if v: "0 \<le> v" for v
    by (rule qvmata_measurable[OF _ C0])
       (use evQ measurable_compose[OF _ projB] in blast)
  have psim: "?\<psi> \<in> Q \<rightarrow>\<^sub>M (ipath_space :: (('n pairpath) measure))"
    by (rule xcovariation_class_liftify_measurable[OF Q C0])
  have into: "?\<psi> w \<in> (ipath :: (('n pairpath) set))" if "w \<in> space Q" for w
    using measurable_space[OF psim that] by simp
  have probP: "prob_space ?P" by (rule PQ.prob_space_distr[OF psim])

  text \<open>The filtration facts, as in the first inclusion.\<close>
  interpret MX: martingale Q ?F 0 "\<lambda>t w :: real \<Rightarrow> real^'n. w t" by (rule mgX)
  have spF: "space (?F u) = space Q" if "0 \<le> u" for u by (rule MX.space_F[OF that])
  have GG: "filtered_measure ?P ?G (0::real)"
  proof -
    interpret PP: prob_space ?P by (rule probP)
    have SP: "Stochastic_Process.stochastic_process ?P (0::real)
        (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
      by (unfold_locales) (rule ipath_eval_measurable_sets[OF sets_distr])
    show ?thesis
      by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SP])
  qed
  have evF: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
    by (rule natural_filtration_eval[OF v vu])
  have qmF: "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w v) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (rule qvmata_measurable[OF _ C0])
    fix s :: real and i assume s: "0 \<le> s" and sv: "s < v"
    show "(\<lambda>w :: real \<Rightarrow> real^'n. w s $ i) \<in> borel_measurable (?F u)"
      by (rule measurable_compose[OF evF[OF s] projB]) (use sv vu in simp)
  qed
  have pull: "?\<psi> \<in> ?F u \<rightarrow>\<^sub>M ?G u" if u: "0 \<le> u" for u
  proof (rule natural_filtration_pull)
    fix w assume "w \<in> space (?F u)"
    then have "w \<in> space Q" using spF[OF u] by simp
    then show "?\<psi> w \<in> space ?P" using into by (simp add: space_distr)
  next
    fix v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    have e: "(\<lambda>w :: real \<Rightarrow> real^'n. ?\<psi> w v) = (\<lambda>w. (w v, qvmata C w v))"
      using v by simp
    show "(\<lambda>w :: real \<Rightarrow> real^'n. ?\<psi> w v) \<in> borel_measurable (?F u)"
      unfolding e by (rule borel_measurable_Pair[OF evF[OF v vu] qmF[OF v vu]])
  qed

  text \<open>Clause (i): the initial condition.  The second coordinate vanishes at
    \<open>0\<close> for EVERY path.\<close>
  have start: "AE \<omega> in ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof (subst AE_distr_iff[OF psim pairpath_start_sets])
    show "AE w in Q. fst (?\<psi> w 0) = x \<and> snd (?\<psi> w 0) = 0"
      using xcovariation_class_start[OF Q] by eventually_elim (simp add: C0)
  qed

  text \<open>Clause (ii): the difference quotients.\<close>
  have dqQ: "AE w in Q. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (?\<psi> w t) - snd (?\<psi> w s)) \<in> S"
    using keyq dqA
  proof eventually_elim
    case (elim w)
    show ?case
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      have es: "snd (?\<psi> w s) = A s w" using elim(1) st by simp
      have et: "snd (?\<psi> w t) = A t w" using elim(1) st by simp
      show "(1 / (t - s)) *\<^sub>R (snd (?\<psi> w t) - snd (?\<psi> w s)) \<in> S"
        unfolding es et using elim(2) st by blast
    qed
  qed
  have dq: "AE \<omega> in ?P. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
    by (subst AE_distr_iff[OF psim pairpath_diffquot_sets[OF Sc]]) (rule dqQ)

  text \<open>Clause (iii): the first coordinate is a martingale.\<close>
  have Xmg: "martingale ?P ?G 0 (\<lambda>t \<omega> :: 'n pairpath. fst (\<omega> t) :: real^'n)"
  proof (rule martingale_distr[OF PQ.prob_space_axioms psim GG pull])
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) :: real^'n) \<in> borel_measurable (?G u)"
      if u: "0 \<le> u" for u
      by (rule measurable_compose[OF natural_filtration_eval[OF u order_refl] pair_fst_borel])
    show "martingale Q ?F 0 (\<lambda>u w :: real \<Rightarrow> real^'n. fst (?\<psi> w u) :: real^'n)"
      by (rule martingale_cong_ge[OF mgX]) simp
  qed

  text \<open>Clause (iv): the compensated process is a martingale, again a
    modification of the one the class of laws of \<open>X\<close> supplies.\<close>
  have SQ: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
    by (unfold_locales) (rule evQ)
  have FM: "filtered_measure Q ?F (0::real)"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SQ])
  have mgcomp: "martingale Q ?F 0
      (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (fst (?\<psi> w u)) - snd (?\<psi> w u))"
  proof -
    have tgt: "martingale Q ?F 0
        (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)"
    proof (rule martingale_cong_AE[OF mgA])
      have ad: "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)
          \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
        using measurable_compose[OF evF[OF u order_refl] outerp_borel] qmF[OF u order_refl]
        by simp
      show "adapted_process Q ?F 0
          (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)"
        unfolding adapted_process_def adapted_process_axioms_def using FM ad by blast
    next
      fix u :: real assume u: "0 \<le> u"
      show "AE w in Q. outerp (w u) - A u w = outerp (w u) - qvmata C w u"
        using keyq by eventually_elim (use u in simp)
    qed
    show ?thesis by (rule martingale_cong_ge[OF tgt]) simp
  qed
  have Cmg: "martingale ?P ?G 0
      (\<lambda>t \<omega> :: 'n pairpath. outerp (fst (\<omega> t) :: real^'n) - snd (\<omega> t))"
  proof (rule martingale_distr[OF PQ.prob_space_axioms psim GG pull])
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u) :: real^'n) - snd (\<omega> u))
        \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
      by (rule measurable_compose[OF natural_filtration_eval[OF u order_refl]
            compensated_map_borel])
    show "martingale Q ?F 0
        (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (fst (?\<psi> w u) :: real^'n) - snd (?\<psi> w u))"
      by (rule mgcomp)
  qed

  have "?P \<in> icovariation_class S x"
    unfolding icovariation_class_def mem_Collect_eq
    using probP sets_distr start dq Xmg Cmg by blast
  then show ?thesis unfolding ipath_law_def C_def .
qed

subsection \<open>The two value functions coincide\<close>

text \<open>
  The exit functional reads the path only on \<open>{0..}\<close> and is measurable there, so
  the essential infimum transports along both pushforwards.  Together with the
  two inclusions this identifies @{const icovariation_val} with
  @{const xcovariation_val}, the value over laws of \<open>X\<close> alone.
\<close>

text \<open>The essential infimum of the exit time is the same on a pair law and on
  its \<open>X\<close>-marginal, and on a law of the \<open>X\<close>-class and on its lift.\<close>

lemma ess_inf_fstify:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes P: "P \<in> icovariation_class S x" and K: "closed K"
  shows "ess_inf (ipath_law P (\<lambda>t \<omega>. fst (\<omega> t))) (iexit K)
       = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
proof -
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..}"
  have m: "\<And>c :: ennreal.
      {w \<in> space (ipath_space :: ((real \<Rightarrow> real^'n) measure)). c \<le> iexit K w}
        \<in> sets ipath_space"
    using iexit_measurable_ipath[OF K] by measurable
  have "ess_inf (distr P (ipath_space :: ((real \<Rightarrow> real^'n) measure)) ?\<phi>) (iexit K)
      = ess_inf P (\<lambda>\<omega>. iexit K (?\<phi> \<omega>))"
    by (rule ess_inf_distr[OF icovariation_class_fstify_measurable[OF P] m])
  also have "\<dots> = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
    by (intro arg_cong[where f = "ess_inf P"] ext iexit_cong_nonneg) simp
  finally show ?thesis unfolding ipath_law_def .
qed

lemma ess_inf_liftify:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)" and K :: "(real^'n) set"
  assumes Q: "Q \<in> xcovariation_class S x" and K: "closed K" and C: "0 \<le> C"
  shows "ess_inf (ipath_law Q (\<lambda>t w. (w t, qvmata C w t)))
           (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))
       = ess_inf Q (iexit K)"
proof -
  let ?\<psi> = "\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..}"
  have m: "\<And>c :: ennreal. {\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      c \<le> iexit K (\<lambda>t. fst (\<omega> t))} \<in> sets ipath_space"
    using iexit_fst_measurable_ipath[OF K] by measurable
  have "ess_inf (distr Q (ipath_space :: (('n pairpath) measure)) ?\<psi>)
        (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))
      = ess_inf Q (\<lambda>w. iexit K (\<lambda>t. fst (?\<psi> w t)))"
    by (rule ess_inf_distr[OF xcovariation_class_liftify_measurable[OF Q C] m])
  also have "\<dots> = ess_inf Q (iexit K)"
    by (intro arg_cong[where f = "ess_inf Q"] ext iexit_cong_nonneg) simp
  finally show ?thesis unfolding ipath_law_def .
qed

theorem icovariation_val_eq_xcovariation_val:
  fixes K :: "(real^'n::finite) set"
  assumes Sc: "closed S" and Sv: "convex S" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and D0: "0 \<le> D" and D: "\<And>a i j. a \<in> S \<Longrightarrow> \<bar>a $ i $ j\<bar> \<le> D"
    and K: "closed K"
  shows "icovariation_val S K x = (xcovariation_val S K x :: ennreal)"
proof (rule antisym)
  show "icovariation_val S K x \<le> xcovariation_val S K x"
    unfolding icovariation_val_def
  proof (rule Sup_least)
    fix v assume "v \<in> (\<lambda>Q. ess_inf Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t))))
        ` icovariation_class S x"
    then obtain P :: "('n pairpath) measure"
      where P: "P \<in> icovariation_class S x"
        and v: "v = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))" by blast
    let ?Q = "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t))"
    have Qx: "?Q \<in> xcovariation_class S x"
      by (rule icovariation_class_marginal_in_xcovariation_class[OF Sc Sv psd D0 D P])
    have "v = ess_inf ?Q (iexit K)" using v ess_inf_fstify[OF P K] by simp
    also have "\<dots> \<le> xcovariation_val S K x"
      unfolding xcovariation_val_def using Qx by (intro Sup_upper) blast
    finally show "v \<le> xcovariation_val S K x" .
  qed
next
  show "xcovariation_val S K x \<le> icovariation_val S K x"
    unfolding xcovariation_val_def
  proof (rule Sup_least)
    fix v assume "v \<in> (\<lambda>Q. ess_inf Q (iexit K)) ` xcovariation_class S x"
    then obtain Q :: "((real \<Rightarrow> real^'n) measure)"
      where Q: "Q \<in> xcovariation_class S x" and v: "v = ess_inf Q (iexit K)" by blast
    have L4: "0 \<le> 4 * D" using D0 by simp
    let ?P = "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * D) w t))"
    have Pi: "?P \<in> icovariation_class S x"
      by (rule xcovariation_class_lift_in_icovariation_class[OF Sc Sv psd D0 D Q])
    have "v = ess_inf ?P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
      using v ess_inf_liftify[OF Q K L4] by simp
    also have "\<dots> \<le> icovariation_val S K x"
      unfolding icovariation_val_def using Pi by (intro Sup_upper) blast
    finally show "v \<le> icovariation_val S K x" .
  qed
qed

(*<*)
end
(*>*)
