
(*<*)
theory Martingale_Transfer
  imports Martingale_Algebra
begin

(*>*)

text \<open>
  Transferring the martingale property across three kinds of structural
  change: to a product of two filtered measures (one factor's own
  martingale, or a product of a first-factor variable with a second-factor
  martingale), to an infinite product's coordinate, along a pushforward, to
  a conditional law on an event of positive measure, and to a restriction
  of the probability space to a full-measure event.
\<close>

section \<open>Martingales on a product of two filtered measures\<close>

text \<open>The pasting theorem needs three transfer results: a first-factor
  martingale, a second-factor martingale, and the product of a
  first-factor variable with a second-factor martingale, are all
  martingales for the product filtration.  All three follow from Fubini
  plus a sectionwise use of the factor's set-integral identity --- a
  section of a set of \<open>F u \<Otimes>\<^sub>M G u\<close> is a set of \<open>F u\<close> (resp. \<open>G u\<close>).  No
  conditional expectation on the product and no \<open>\<pi>\<close>-\<open>\<lambda>\<close> argument is
  needed.\<close>

lemma prob_space_pair_measure:
  assumes M: "prob_space M" and N: "prob_space N"
  shows "prob_space (M \<Otimes>\<^sub>M N)"
proof -
  interpret M: prob_space M by (rule M)
  interpret N: prob_space N by (rule N)
  interpret PP: pair_prob_space M N by unfold_locales
  show ?thesis by (rule PP.P.prob_space_axioms)
qed

lemma sets_pair_measure_mono:
  assumes A: "sets A \<subseteq> sets M" "space A = space M"
    and B: "sets B \<subseteq> sets N" "space B = space N"
  shows "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets (M \<Otimes>\<^sub>M N)"
proof -
  have "{a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<subseteq> sets (M \<Otimes>\<^sub>M N)"
    using A(1) B(1) by auto
  then have "sigma_sets (space (M \<Otimes>\<^sub>M N))
      {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<subseteq> sets (M \<Otimes>\<^sub>M N)"
    by (rule sets.sigma_sets_subset)
  then show ?thesis
    using A(2) B(2) by (simp add: sets_pair_measure space_pair_measure)
qed

lemma filtered_measure_pair:
  fixes F :: "real \<Rightarrow> 'a measure" and G :: "real \<Rightarrow> 'b measure"
  assumes MF: "filtered_measure M F (0::real)"
    and NG: "filtered_measure N G (0::real)"
  shows "filtered_measure (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) (0::real)"
proof -
  interpret MF: filtered_measure M F "0::real" by (rule MF)
  interpret NG: filtered_measure N G "0::real" by (rule NG)
  show ?thesis
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    have "sets (F i \<Otimes>\<^sub>M G i) \<subseteq> sets (M \<Otimes>\<^sub>M N)"
      using MF.sets_F_subset[OF i] NG.sets_F_subset[OF i]
        MF.space_F[OF i] NG.space_F[OF i]
      by (intro sets_pair_measure_mono)
    moreover have "space (F i \<Otimes>\<^sub>M G i) = space (M \<Otimes>\<^sub>M N)"
      using MF.space_F[OF i] NG.space_F[OF i] by (simp add: space_pair_measure)
    ultimately show "subalgebra (M \<Otimes>\<^sub>M N) (F i \<Otimes>\<^sub>M G i)"
      by (simp add: subalgebra_def)
  next
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    then have j: "0 \<le> j" by simp
    show "sets (F i \<Otimes>\<^sub>M G i) \<le> sets (F j \<Otimes>\<^sub>M G j)"
      using MF.sets_F_mono[OF ij] NG.sets_F_mono[OF ij]
        MF.space_F[OF ij(1)] MF.space_F[OF j]
        NG.space_F[OF ij(1)] NG.space_F[OF j]
      by (intro sets_pair_measure_mono) simp_all
  qed
qed

theorem martingale_pair_fst:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and mg: "martingale M F (0::real) X"
    and NG: "filtered_measure N G (0::real)"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. X u (fst p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MG: martingale M F "0::real" X by (rule mg)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  have FMF: "filtered_measure M F (0::real)" by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF FMF NG] PP.finite_measure_axioms by blast
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MG.subalgebras[OF u] MG.adapted[OF u]])
  have int: "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X u (fst p))" if u: "0 \<le> u" for u
  proof -
    have e: "integrable (distr (M \<Otimes>\<^sub>M N) M fst) (X u)
        = integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X u (fst p))"
      by (rule integrable_distr_eq[OF measurable_fst Xm[OF u]])
    have "integrable (distr (M \<Otimes>\<^sub>M N) M fst) (X u)"
      using MG.integrable[OF u] by (simp add: PN.distr_pair_fst)
    then show ?thesis unfolding e .
  qed
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p))
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p))"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have key: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X w (fst p))
        = (\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w) \<partial>N)"
      if w: "0 \<le> w" for w
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R X w \<omega>))"
        using integrable_mult_indicator[OF AM int[OF w]]
        by (simp add: case_prod_unfold)
      have "(\<integral>\<omega>'. (\<integral>\<omega>. indicator A (\<omega>, \<omega>') *\<^sub>R X w \<omega> \<partial>M) \<partial>N)
          = (\<integral>p. indicator A p *\<^sub>R X w (fst p) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_snd[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        by (simp add: set_lebesgue_integral_def indicator_def)
    qed
    have sec: "(\<lambda>\<omega>. (\<omega>, \<omega>')) -` A \<in> sets (F u)" for \<omega>'
      by (rule sets_Pair2[OF A])
    have "(\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X u) \<partial>N)
        = (\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X v) \<partial>N)"
      using MG.set_integral_eq[OF sec u uv] by simp
    then show ?thesis unfolding key[OF u] key[OF v] .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. X u (fst p))"
    proof (unfold_locales)
      fix i :: real assume i: "0 \<le> i"
      show "(\<lambda>p. X i (fst p)) \<in> borel_measurable (F i \<Otimes>\<^sub>M G i)"
        by (rule measurable_compose[OF measurable_fst MG.adapted[OF i]])
    qed
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X i (fst p))" if "0 \<le> i" for i
      by (rule int[OF that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X i (fst p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X j (fst p))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

lemma distr_pair_snd:
  assumes M: "prob_space M" and N: "sigma_finite_measure N"
  shows "distr (M \<Otimes>\<^sub>M N) N snd = N"
proof (intro measure_eqI)
  interpret PM: prob_space M by (rule M)
  interpret SN: sigma_finite_measure N by (rule N)
  fix A assume "A \<in> sets (distr (M \<Otimes>\<^sub>M N) N snd)"
  then have A: "A \<in> sets N" by simp
  have "emeasure (distr (M \<Otimes>\<^sub>M N) N snd) A = emeasure (M \<Otimes>\<^sub>M N) (space M \<times> A)"
    using A by (auto simp add: emeasure_distr space_pair_measure
        dest: sets.sets_into_space intro!: arg_cong2[where f = emeasure])
  also have "\<dots> = emeasure N A"
    using A by (simp add: SN.emeasure_pair_measure_Times PM.emeasure_space_1)
  finally show "emeasure (distr (M \<Otimes>\<^sub>M N) N snd) A = emeasure N A" .
qed simp

text \<open>The second-factor lift the DPP needs: the process may depend on the
  first coordinate too, as long as it is a second-factor martingale for
  each frozen value --- exactly what an endpoint-dependent continuation
  looks like once the endpoint is frozen.  The section argument is
  unchanged.\<close>

theorem martingale_pair_snd_param:
  fixes Z :: "real \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and MF: "filtered_measure M F (0::real)"
    and NG: "filtered_measure N G (0::real)"
    and adap: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable (F u \<Otimes>\<^sub>M G u)"
    and int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (M \<Otimes>\<^sub>M N) (Z u)"
    and sec: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> martingale N G 0 (\<lambda>u \<omega>'. Z u (\<omega>, \<omega>'))"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 Z"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF MF NG] PP.finite_measure_axioms by blast
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z u)
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z v)"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have ii: "integrable (M \<Otimes>\<^sub>M N)
        (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>')))"
      if w: "0 \<le> w" for w
      using integrable_mult_indicator[OF AM int[OF w]]
      by (simp add: case_prod_unfold)
    have key: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z w)
        = (\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>') \<partial>N) \<partial>M)"
      if w: "0 \<le> w" for w
    proof -
      have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>') \<partial>N) \<partial>M)
          = (\<integral>p. indicator A p *\<^sub>R Z w p \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_fst[OF ii[OF w]] by (simp add: case_prod_unfold)
      then show ?thesis by (simp add: set_lebesgue_integral_def)
    qed
    have inner_eq: "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z u (\<omega>, \<omega>') \<partial>N)
        = (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z v (\<omega>, \<omega>') \<partial>N)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      interpret MW: martingale N G "0::real" "\<lambda>u \<omega>'. Z u (\<omega>, \<omega>')"
        by (rule sec[OF w])
      have "set_lebesgue_integral N (Pair \<omega> -` A) (\<lambda>\<omega>'. Z u (\<omega>, \<omega>'))
          = set_lebesgue_integral N (Pair \<omega> -` A) (\<lambda>\<omega>'. Z v (\<omega>, \<omega>'))"
        by (rule MW.set_integral_eq[OF sets_Pair1[OF A] u uv])
      then show ?thesis
        by (simp add: set_lebesgue_integral_def indicator_def)
    qed
    have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z u (\<omega>, \<omega>') \<partial>N) \<partial>M)
        = (\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z v (\<omega>, \<omega>') \<partial>N) \<partial>M)"
      using AE_space inner_eq
      by (intro Bochner_Integration.integral_cong_AE
          borel_measurable_integrable PS.integrable_fst[OF ii[OF u]]
          PS.integrable_fst[OF ii[OF v]]) auto
    then show ?thesis unfolding key[OF u] key[OF v] .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 Z"
      unfolding adapted_process_def adapted_process_axioms_def
      using filtered_measure_pair[OF MF NG] adap by blast
    show "integrable (M \<Otimes>\<^sub>M N) (Z i)" if "0 \<le> i" for i by (rule int[OF that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z i)
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z j)"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

theorem martingale_pair_snd:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and MF: "filtered_measure M F (0::real)"
    and mg: "martingale N G (0::real) Y"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. Y u (snd p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MG: martingale N G "0::real" Y by (rule mg)
  have FMG: "filtered_measure N G (0::real)" by unfold_locales
  have Ym: "Y u \<in> borel_measurable N" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MG.subalgebras[OF u] MG.adapted[OF u]])
  show ?thesis
  proof (rule martingale_pair_snd_param[OF M N MF FMG])
    show "(\<lambda>p. Y u (snd p)) \<in> borel_measurable (F u \<Otimes>\<^sub>M G u)" if "0 \<le> u" for u
      by (rule measurable_compose[OF measurable_snd MG.adapted[OF that]])
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. Y u (snd p))" if u: "0 \<le> u" for u
    proof -
      have e: "integrable (distr (M \<Otimes>\<^sub>M N) N snd) (Y u)
          = integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. Y u (snd p))"
        by (rule integrable_distr_eq[OF measurable_snd Ym[OF u]])
      have "integrable (distr (M \<Otimes>\<^sub>M N) N snd) (Y u)"
        using MG.integrable[OF u]
        by (simp add: distr_pair_snd[OF M PN.sigma_finite_measure_axioms])
      then show ?thesis unfolding e .
    qed
    show "martingale N G 0 (\<lambda>u \<omega>'. Y u (snd (\<omega>, \<omega>')))"
      if "\<omega> \<in> space M" for \<omega> by (simp add: mg)
  qed
qed

text \<open>The third transfer result, needed for the compensated clause: the
  product of a first-factor martingale with a second-factor martingale is
  a martingale for the product filtration.  Independence of the two pieces
  is genuinely used here.  The proof is Fubini twice, once per variable.\<close>

theorem martingale_pair_mult:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and Y :: "real \<Rightarrow> 'b \<Rightarrow> real"
  assumes M: "prob_space M" and N: "prob_space N"
    and mgX: "martingale M F (0::real) X"
    and mgY: "martingale N G (0::real) Y"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0
      (\<lambda>u p. X u (fst p) * Y u (snd p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  interpret MY: martingale N G "0::real" Y by (rule mgY)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  have FMF: "filtered_measure M F (0::real)" by unfold_locales
  have FMG: "filtered_measure N G (0::real)" by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF FMF FMG] PP.finite_measure_axioms by blast
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MX.subalgebras[OF u] MX.adapted[OF u]])
  have Ym: "Y u \<in> borel_measurable N" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MY.subalgebras[OF u] MY.adapted[OF u]])
  have prodm: "(\<lambda>p. X w (fst p) * Y z (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    if w: "0 \<le> w" and z: "0 \<le> z" for w z
    by (rule borel_measurable_times
        [OF measurable_compose[OF measurable_fst Xm[OF w]]
            measurable_compose[OF measurable_snd Ym[OF z]]])
  have pint: "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X w (fst p) * Y z (snd p))"
    if w: "0 \<le> w" and z: "0 \<le> z" for w z
  proof (rule PS.Fubini_integrable[OF prodm[OF w z]])
    have "integrable M (\<lambda>\<omega>. \<bar>X w \<omega>\<bar> * (\<integral>\<omega>'. \<bar>Y z \<omega>'\<bar> \<partial>N))"
      using MX.integrable[OF w] by simp
    then show "integrable M
        (\<lambda>\<omega>. \<integral>\<omega>'. norm (X w (fst (\<omega>, \<omega>')) * Y z (snd (\<omega>, \<omega>'))) \<partial>N)"
      by (simp add: abs_mult)
  next
    show "AE \<omega> in M. integrable N
        (\<lambda>\<omega>'. X w (fst (\<omega>, \<omega>')) * Y z (snd (\<omega>, \<omega>')))"
      using MY.integrable[OF z] by simp
  qed
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y u (snd p))
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p) * Y v (snd p))"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have key1: "set_lebesgue_integral (M \<Otimes>\<^sub>M N)
          A (\<lambda>p. X w (fst p) * Y z (snd p))
        = (\<integral>\<omega>. X w \<omega> * set_lebesgue_integral N (Pair \<omega> -` A) (Y z) \<partial>M)"
      if w: "0 \<le> w" and z: "0 \<le> z" for w z
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>')))"
        using integrable_mult_indicator[OF AM pint[OF w z]]
        by (simp add: case_prod_unfold)
      have inner: "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N)
          = X w \<omega> * set_lebesgue_integral N (Pair \<omega> -` A) (Y z)" for \<omega>
      proof -
        have "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N)
            = (\<integral>\<omega>'. X w \<omega> * (indicator (Pair \<omega> -` A) \<omega>' * Y z \<omega>') \<partial>N)"
          by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
        also have "\<dots>
            = X w \<omega> * (\<integral>\<omega>'. indicator (Pair \<omega> -` A) \<omega>' * Y z \<omega>' \<partial>N)"
          by simp
        finally show ?thesis by (simp add: set_lebesgue_integral_def)
      qed
      have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N) \<partial>M)
          = (\<integral>p. indicator A p * (X w (fst p) * Y z (snd p)) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_fst[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        unfolding inner by (simp add: set_lebesgue_integral_def)
    qed
    have key2: "set_lebesgue_integral (M \<Otimes>\<^sub>M N)
          A (\<lambda>p. X w (fst p) * Y z (snd p))
        = (\<integral>\<omega>'. Y z \<omega>'
            * set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w) \<partial>N)"
      if w: "0 \<le> w" and z: "0 \<le> z" for w z
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>')))"
        using integrable_mult_indicator[OF AM pint[OF w z]]
        by (simp add: case_prod_unfold)
      have inner: "(\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M)
          = Y z \<omega>' * set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w)" for \<omega>'
      proof -
        have "(\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M)
            = (\<integral>\<omega>. Y z \<omega>'
                * (indicator ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) \<omega> * X w \<omega>) \<partial>M)"
          by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
        also have "\<dots> = Y z \<omega>'
            * (\<integral>\<omega>. indicator ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) \<omega> * X w \<omega> \<partial>M)"
          by simp
        finally show ?thesis by (simp add: set_lebesgue_integral_def)
      qed
      have "(\<integral>\<omega>'. (\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M) \<partial>N)
          = (\<integral>p. indicator A p * (X w (fst p) * Y z (snd p)) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_snd[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        unfolding inner by (simp add: set_lebesgue_integral_def)
    qed
    have eqY: "set_lebesgue_integral N (Pair \<omega> -` A) (Y u)
        = set_lebesgue_integral N (Pair \<omega> -` A) (Y v)" for \<omega>
      by (rule MY.set_integral_eq[OF sets_Pair1[OF A] u uv])
    have eqX: "set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X u)
        = set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X v)" for \<omega>'
      by (rule MX.set_integral_eq[OF sets_Pair2[OF A] u uv])
    have "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y u (snd p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y v (snd p))"
      unfolding key1[OF u u] key1[OF u v] using eqY by simp
    also have "\<dots>
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p) * Y v (snd p))"
      unfolding key2[OF u v] key2[OF v v] using eqX by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0
        (\<lambda>u p. X u (fst p) * Y u (snd p))"
    proof (unfold_locales)
      fix i :: real assume i: "0 \<le> i"
      show "(\<lambda>p. X i (fst p) * Y i (snd p))
          \<in> borel_measurable (F i \<Otimes>\<^sub>M G i)"
        by (rule borel_measurable_times
            [OF measurable_compose[OF measurable_fst MX.adapted[OF i]]
                measurable_compose[OF measurable_snd MY.adapted[OF i]]])
    qed
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X i (fst p) * Y i (snd p))"
      if "0 \<le> i" for i
      by (rule pint[OF that that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X i (fst p) * Y i (snd p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X j (fst p) * Y j (snd p))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

section \<open>Lifting a martingale to an infinite product\<close>

text \<open>Pasting with a kernel --- a continuation chosen per endpoint --- uses
  as second factor the product \<open>\<Pi>\<^sub>M i. R i\<close> of all candidate
  continuations, from which the glue picks the one the endpoint selects;
  so the \<open>i\<close>-th coordinate process must be a martingale for the product
  filtration.  The route: split the coordinate off with
  \<open>distr_pair_PiM_eq_PiM\<close>, apply \<open>martingale_pair_fst\<close>, transport back
  along the \<open>distr\<close>.\<close>

lemma sets_PiM_mono:
  assumes S: "\<And>i. i \<in> I \<Longrightarrow> sets (A i) \<subseteq> sets (B i)"
    and SP: "\<And>i. i \<in> I \<Longrightarrow> space (A i) = space (B i)"
  shows "sets (Pi\<^sub>M I A) \<subseteq> sets (Pi\<^sub>M I B)"
proof -
  have sp: "(\<Pi>\<^sub>E i\<in>I. space (A i)) = (\<Pi>\<^sub>E i\<in>I. space (B i))"
    using SP by (intro PiE_cong) simp
  have gen: "{{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} | i X. i \<in> I \<and> X \<in> sets (A i)}
      \<subseteq> sets (Pi\<^sub>M I B)"
  proof safe
    fix i X assume iX: "i \<in> I" "X \<in> sets (A i)"
    then have "X \<in> sets (B i)" using S by blast
    then have "{f \<in> \<Pi>\<^sub>E i\<in>I. space (B i). f i \<in> X} \<in> sets (Pi\<^sub>M I B)"
      using iX(1) unfolding sets_PiM_single by (intro sigma_sets.Basic) blast
    then show "{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} \<in> sets (Pi\<^sub>M I B)"
      unfolding sp .
  qed
  have "sigma_sets (space (Pi\<^sub>M I B))
      {{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} | i X. i \<in> I \<and> X \<in> sets (A i)}
      \<subseteq> sets (Pi\<^sub>M I B)"
    by (rule sets.sigma_sets_subset[OF gen])
  then show ?thesis
    unfolding sets_PiM_single using sp by (simp add: space_PiM)
qed

lemma filtered_measure_PiM:
  fixes G :: "'i \<Rightarrow> real \<Rightarrow> 'a measure"
  assumes F: "\<And>i. i \<in> I \<Longrightarrow> filtered_measure (R i) (G i) (0::real)"
  shows "filtered_measure (Pi\<^sub>M I R) (\<lambda>u. Pi\<^sub>M I (\<lambda>i. G i u)) (0::real)"
proof (unfold_locales)
  fix u :: real assume u: "0 \<le> u"
  have spu: "space (G i u) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] u])
  have "space (Pi\<^sub>M I (\<lambda>i. G i u)) = space (Pi\<^sub>M I R)"
    using spu by (simp add: space_PiM cong: PiE_cong)
  moreover have "sets (Pi\<^sub>M I (\<lambda>i. G i u)) \<subseteq> sets (Pi\<^sub>M I R)"
  proof (rule sets_PiM_mono)
    show "sets (G i u) \<subseteq> sets (R i)" if "i \<in> I" for i
      by (rule filtered_measure.sets_F_subset[OF F[OF that] u])
    show "space (G i u) = space (R i)" if "i \<in> I" for i by (rule spu[OF that])
  qed
  ultimately show "subalgebra (Pi\<^sub>M I R) (Pi\<^sub>M I (\<lambda>i. G i u))"
    by (simp add: subalgebra_def)
next
  fix u v :: real assume uv: "0 \<le> u" "u \<le> v"
  then have v: "0 \<le> v" by simp
  have spu: "space (G i u) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] uv(1)])
  have spv: "space (G i v) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] v])
  show "sets (Pi\<^sub>M I (\<lambda>i. G i u)) \<le> sets (Pi\<^sub>M I (\<lambda>i. G i v))"
  proof (rule sets_PiM_mono)
    show "sets (G i u) \<subseteq> sets (G i v)" if "i \<in> I" for i
      by (rule filtered_measure.sets_F_mono[OF F[OF that] uv(1) uv(2)])
    show "space (G i u) = space (G i v)" if "i \<in> I" for i
      using spu[OF that] spv[OF that] by simp
  qed
qed

text \<open>Transport of the martingale property along a pushforward.  This is
  the general form of what \<open>martingale_pair_law\<close> does for path spaces: if
  \<open>\<phi>\<close> pulls the target filtration back into the source one, a source
  martingale of the composed process is a target martingale.\<close>

theorem martingale_distr:
  fixes Z :: "real \<Rightarrow> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes prob: "prob_space M"
    and phim: "\<phi> \<in> M \<rightarrow>\<^sub>M N"
    and GG: "filtered_measure (distr M N \<phi>) GG (0::real)"
    and pull: "\<And>u. 0 \<le> u \<Longrightarrow> \<phi> \<in> FF u \<rightarrow>\<^sub>M GG u"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable (GG u)"
    and mg: "martingale M FF 0 (\<lambda>u \<omega>. Z u (\<phi> \<omega>))"
  shows "martingale (distr M N \<phi>) GG 0 Z"
proof -
  interpret PM: prob_space M by (rule prob)
  interpret MG: martingale M FF "0::real" "\<lambda>u \<omega>. Z u (\<phi> \<omega>)" by (rule mg)
  interpret PD: prob_space "distr M N \<phi>" by (rule PM.prob_space_distr[OF phim])
  interpret FD: finite_filtered_measure "distr M N \<phi>" GG "0::real"
    unfolding finite_filtered_measure_def
    using GG PD.finite_measure_axioms by blast
  have ZM: "Z u \<in> borel_measurable N" if u: "0 \<le> u" for u
  proof -
    have "Z u \<in> borel_measurable (distr M N \<phi>)"
      by (rule measurable_from_subalg[OF FD.subalgebras[OF u] Zm[OF u]])
    then show ?thesis by simp
  qed
  have int: "integrable (distr M N \<phi>) (Z u)" if u: "0 \<le> u" for u
  proof -
    have e: "integrable (distr M N \<phi>) (Z u) = integrable M (\<lambda>\<omega>. Z u (\<phi> \<omega>))"
      by (rule integrable_distr_eq[OF phim ZM[OF u]])
    show ?thesis unfolding e by (rule MG.integrable[OF u])
  qed
  show ?thesis
  proof (rule FD.martingale_of_set_integral_eq)
    show "adapted_process (distr M N \<phi>) GG 0 Z"
      unfolding adapted_process_def adapted_process_axioms_def
      using GG Zm by blast
    show "integrable (distr M N \<phi>) (Z i)" if "0 \<le> i" for i by (rule int[OF that])
    fix A and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and A: "A \<in> sets (GG i)"
    then have j: "0 \<le> j" by simp
    have AN: "A \<in> sets N" using A FD.sets_F_subset[OF ij(1)] by auto
    have pre: "\<phi> -` A \<inter> space M \<in> sets (FF i)"
      using measurable_sets[OF pull[OF ij(1)] A] MG.space_F[OF ij(1)] by simp
    have key: "set_lebesgue_integral (distr M N \<phi>) A (Z w)
        = set_lebesgue_integral M (\<phi> -` A \<inter> space M) (\<lambda>\<omega>. Z w (\<phi> \<omega>))"
      if w: "0 \<le> w" for w
    proof -
      have "set_lebesgue_integral (distr M N \<phi>) A (Z w)
          = (\<integral>y. indicator A y *\<^sub>R Z w y \<partial>(distr M N \<phi>))"
        by (simp add: set_lebesgue_integral_def)
      also have "\<dots> = (\<integral>\<omega>. indicator A (\<phi> \<omega>) *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
      proof (rule integral_distr[OF phim])
        show "(\<lambda>y. indicator A y *\<^sub>R Z w y) \<in> borel_measurable N"
          using ZM[OF w] AN by measurable
      qed
      also have "\<dots> = (\<integral>\<omega>. indicator (\<phi> -` A \<inter> space M) \<omega> *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis by (simp add: set_lebesgue_integral_def)
    qed
    show "set_lebesgue_integral (distr M N \<phi>) A (Z i)
        = set_lebesgue_integral (distr M N \<phi>) A (Z j)"
      unfolding key[OF ij(1)] key[OF j] by (rule MG.set_integral_eq[OF pre ij])
  qed
qed

theorem martingale_PiM_component:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
    and R :: "'i \<Rightarrow> 'a measure" and G :: "'i \<Rightarrow> real \<Rightarrow> 'a measure"
  assumes R: "\<And>j. prob_space (R j)"
    and F: "\<And>j. filtered_measure (R j) (G j) (0::real)"
    and mg: "martingale (R i) (G i) 0 Y"
  shows "martingale (Pi\<^sub>M UNIV R) (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. G j u)) 0 (\<lambda>u f. Y u (f i))"
proof -
  let ?I = "UNIV - {i}"
  let ?S = "Pi\<^sub>M ?I R"
  let ?P = "R i \<Otimes>\<^sub>M ?S"
  let ?\<phi> = "\<lambda>(x, X). X(i := x)"
  let ?GG = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. G j u)"
  let ?FF = "\<lambda>u. G i u \<Otimes>\<^sub>M Pi\<^sub>M ?I (\<lambda>j. G j u)"
  interpret MG: martingale "R i" "G i" "0::real" Y by (rule mg)
  have ins: "insert i ?I = (UNIV :: 'i set)" by auto
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule R)
  have PP: "prob_space ?P" by (rule prob_space_pair_measure[OF R PS])
  have GI: "filtered_measure ?S (\<lambda>u. Pi\<^sub>M ?I (\<lambda>j. G j u)) (0::real)"
    by (rule filtered_measure_PiM) (rule F)
  have GU: "filtered_measure (Pi\<^sub>M UNIV R) ?GG (0::real)"
    by (rule filtered_measure_PiM) (rule F)

  \<comment> \<open>the coordinate-insertion map, uniformly in the family of factors\<close>
  have phim: "(\<lambda>(x, X). X(i := x)) \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M Pi\<^sub>M UNIV H"
    for H :: "'i \<Rightarrow> 'a measure"
  proof -
    have e: "(\<lambda>(x, X). X(i := x))
        = (\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). \<lambda>j. if j = i then fst p else snd p j)"
      by (rule ext) (auto simp: fun_upd_def case_prod_unfold)
    show ?thesis
      unfolding e
    proof (rule measurable_PiM_single')
      fix j :: 'i assume "j \<in> (UNIV :: 'i set)"
      show "(\<lambda>p. if j = i then fst p else snd p j)
          \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M H j"
      proof (cases "j = i")
        case True
        then show ?thesis using measurable_fst by simp
      next
        case False
        then have jI: "j \<in> ?I" by simp
        have "(\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). snd p j) \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M H j"
          by (rule measurable_compose[OF measurable_snd
                measurable_component_singleton[OF jI]])
        then show ?thesis using False by simp
      qed
    next
      show "(\<lambda>p j. if j = i then fst p else snd p j)
          \<in> space (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow> (\<Pi>\<^sub>E j\<in>UNIV. space (H j))"
      proof (rule Pi_I)
        fix p :: "'a \<times> ('i \<Rightarrow> 'a)"
        assume p: "p \<in> space (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H)"
        then have p1: "fst p \<in> space (H i)"
          and p2: "snd p \<in> (\<Pi>\<^sub>E j\<in>?I. space (H j))"
          by (simp_all add: space_pair_measure space_PiM mem_Times_iff)
        have "(if j = i then fst p else snd p j) \<in> space (H j)" for j :: 'i
        proof (cases "j = i")
          case True
          then show ?thesis using p1 by simp
        next
          case False
          then have "j \<in> ?I" by simp
          then show ?thesis using p2 False by (simp add: PiE_iff)
        qed
        then show "(\<lambda>j. if j = i then fst p else snd p j)
            \<in> (\<Pi>\<^sub>E j\<in>UNIV. space (H j))" by (simp add: PiE_iff)
      qed
    qed
  qed

  \<comment> \<open>the product is the pushforward of the split product\<close>
  have D: "distr ?P (Pi\<^sub>M UNIV R) ?\<phi> = Pi\<^sub>M UNIV R"
  proof -
    have "distr (R i \<Otimes>\<^sub>M Pi\<^sub>M ?I R) (Pi\<^sub>M (insert i ?I) R) (\<lambda>(x, X). X(i := x))
        = Pi\<^sub>M (insert i ?I) R"
      by (rule distr_pair_PiM_eq_PiM) (auto simp: R)
    then show ?thesis unfolding ins .
  qed

  have Zm: "(\<lambda>f. Y u (f i)) \<in> borel_measurable (?GG u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>f :: 'i \<Rightarrow> 'a. f i) \<in> ?GG u \<rightarrow>\<^sub>M G i u"
      by (rule measurable_component_singleton) simp
    then show ?thesis by (rule measurable_compose[OF _ MG.adapted[OF u]])
  qed
  have mgP: "martingale ?P ?FF 0 (\<lambda>u p. Y u ((case p of (x, X) \<Rightarrow> X(i := x)) i))"
  proof (rule martingale_cong_ge[OF martingale_pair_fst[OF R PS mg GI]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). Y u (fst p))
        = (\<lambda>p. Y u ((case p of (x, X) \<Rightarrow> X(i := x)) i))"
      by (rule ext) (simp add: case_prod_unfold)
  qed
  have "martingale (distr ?P (Pi\<^sub>M UNIV R) ?\<phi>) ?GG 0 (\<lambda>u f. Y u (f i))"
  proof (rule martingale_distr[OF PP phim[of R]])
    show "filtered_measure (distr ?P (Pi\<^sub>M UNIV R) ?\<phi>) ?GG (0::real)"
      unfolding D by (rule GU)
    show "?\<phi> \<in> ?FF u \<rightarrow>\<^sub>M ?GG u" if "0 \<le> u" for u by (rule phim)
    show "(\<lambda>f. Y u (f i)) \<in> borel_measurable (?GG u)" if "0 \<le> u" for u
      by (rule Zm[OF that])
    show "martingale ?P ?FF 0
        (\<lambda>u \<omega>. Y u ((case \<omega> of (x, X) \<Rightarrow> X(i := x)) i))"
      by (rule mgP)
  qed
  then show ?thesis unfolding D .
qed

section \<open>Conditioning on an event of the past keeps martingales martingales\<close>

text \<open>Conditioning on an event \<open>A\<close> of the past rescales the measure by a
  density that is measurable for the filtration at time \<open>0\<close>; a set integral
  over \<open>C \<in> \<F>\<^sub>i\<close> then becomes one over \<open>C \<inter> A \<in> \<F>\<^sub>i\<close>, and the martingale
  property applies unchanged, with no approximation or monotone-class
  step.\<close>

lemma uniform_measure_density_real:
  assumes M: "prob_space M" and pos: "0 < measure M A"
  shows "uniform_measure M A = density M (\<lambda>x. ennreal (indicator A x / measure M A))"
proof -
  interpret PM: prob_space M by (rule M)
  have "(\<lambda>x. indicator A x / emeasure M A)
      = (\<lambda>x. ennreal (indicator A x / measure M A))"
  proof
    fix x show "indicator A x / emeasure M A = ennreal (indicator A x / measure M A)"
    proof (cases "x \<in> A")
      case True
      have "indicator A x / emeasure M A = ennreal 1 / ennreal (measure M A)"
        using True by (simp add: PM.emeasure_eq_measure)
      also have "\<dots> = ennreal (1 / measure M A)"
        by (rule divide_ennreal[OF _ pos]) simp
      finally show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  then show ?thesis unfolding uniform_measure_def by simp
qed

lemma integral_uniform_measure_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "f \<in> borel_measurable M"
  shows "(\<integral>x. f x \<partial>uniform_measure M A)
      = (\<integral>x. (indicator A x / measure M A) *\<^sub>R f x \<partial>M)"
proof -
  have gm: "(\<lambda>x. indicator A x / measure M A) \<in> borel_measurable M"
    using A by measurable
  show ?thesis
    unfolding uniform_measure_density_real[OF M pos]
    by (rule integral_density[OF f gm]) (use pos in auto)
qed

lemma integrable_uniform_measureI:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "integrable M f"
  shows "integrable (uniform_measure M A) f"
proof -
  have fm: "f \<in> borel_measurable M" using f by simp
  have gm: "(\<lambda>x. indicator A x / measure M A) \<in> borel_measurable M"
    using A by measurable
  have i1: "integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (rule integrable_mult_indicator[OF A f])
  have i2: "integrable M (\<lambda>x. (1 / measure M A) *\<^sub>R (indicator A x *\<^sub>R f x))"
    by (rule integrable_scaleR_right[OF i1])
  have eq: "(\<lambda>x. (1 / measure M A) *\<^sub>R (indicator A x *\<^sub>R f x))
      = (\<lambda>x. (indicator A x / measure M A) *\<^sub>R f x)"
    by (rule ext) (simp add: field_simps)
  have "integrable (uniform_measure M A) f
      \<longleftrightarrow> integrable M (\<lambda>x. (indicator A x / measure M A) *\<^sub>R f x)"
    unfolding uniform_measure_density_real[OF M pos]
    by (rule integrable_density[OF fm gm]) (use pos in auto)
  then show ?thesis using i2 eq by simp
qed

lemma set_integral_uniform_measure_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "f \<in> borel_measurable M" and C: "C \<in> sets M"
  shows "set_lebesgue_integral (uniform_measure M A) C f
      = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) f"
proof -
  have cm: "(\<lambda>x. indicator C x *\<^sub>R f x) \<in> borel_measurable M" using f C by measurable
  have "set_lebesgue_integral (uniform_measure M A) C f
      = (\<integral>x. indicator C x *\<^sub>R f x \<partial>uniform_measure M A)"
    unfolding set_lebesgue_integral_def ..
  also have "\<dots> = (\<integral>x. (indicator A x / measure M A) *\<^sub>R (indicator C x *\<^sub>R f x) \<partial>M)"
    by (rule integral_uniform_measure_eq[OF M A pos cm])
  also have "\<dots> = (\<integral>x. (1 / measure M A) *\<^sub>R (indicator (C \<inter> A) x *\<^sub>R f x) \<partial>M)"
    by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (1 / measure M A) *\<^sub>R (\<integral>x. indicator (C \<inter> A) x *\<^sub>R f x \<partial>M)"
    by (rule integral_scaleR_right)
  finally show ?thesis unfolding set_lebesgue_integral_def .
qed

theorem martingale_uniform_measure:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and mg: "martingale M F (0::real) X"
    and A: "A \<in> sets (F 0)" and pos: "0 < measure M A"
  shows "martingale (uniform_measure M A) F 0 X"
proof -
  interpret PM: prob_space M by (rule M)
  interpret MG: martingale M F "0::real" X by (rule mg)
  have F0M: "sets (F 0) \<subseteq> sets M" by (rule MG.sets_F_subset[OF order_refl])
  have AM: "A \<in> sets M" using A F0M by blast
  have ea0: "emeasure M A \<noteq> 0" using pos by (simp add: PM.emeasure_eq_measure)
  have eafin: "emeasure M A \<noteq> \<infinity>" by (simp add: PM.emeasure_eq_measure)
  interpret PU: prob_space "uniform_measure M A"
    by (rule prob_space_uniform_measure[OF ea0 eafin])
  have FU: "filtered_measure (uniform_measure M A) F 0"
  proof (unfold_locales)
    show "subalgebra (uniform_measure M A) (F i)" if "0 \<le> i" for i :: real
      using MG.subalgebras[OF that] by (simp add: subalgebra_def)
    show "sets (F i) \<le> sets (F j)" if "0 \<le> i" "i \<le> j" for i j :: real
      by (rule MG.sets_F_mono[OF that])
  qed
  interpret FU: finite_filtered_measure "uniform_measure M A" F "0::real"
    unfolding finite_filtered_measure_def
    using FU PU.finite_measure_axioms by blast
  show ?thesis
  proof (rule FU.martingale_of_set_integral_eq)
    show "adapted_process (uniform_measure M A) F 0 X"
      unfolding adapted_process_def adapted_process_axioms_def
      using FU MG.adapted by blast
    show "integrable (uniform_measure M A) (X i)" if "0 \<le> i" for i
      by (rule integrable_uniform_measureI[OF M AM pos MG.integrable[OF that]])
    fix C and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and C: "C \<in> sets (F i)"
    have CM: "C \<in> sets M" using C MG.sets_F_subset[OF ij(1)] by auto
    have AFi: "A \<in> sets (F i)" using A MG.sets_F_mono[OF order_refl ij(1)] by auto
    have CA: "C \<inter> A \<in> sets (F i)" using C AFi by (rule sets.Int)
    have Xm: "X i \<in> borel_measurable M"
      by (rule measurable_from_subalg[OF MG.subalgebras[OF ij(1)] MG.adapted[OF ij(1)]])
    have j0: "0 \<le> j" using ij by simp
    have Xmj: "X j \<in> borel_measurable M"
      by (rule measurable_from_subalg[OF MG.subalgebras[OF j0] MG.adapted[OF j0]])
    have "set_lebesgue_integral (uniform_measure M A) C (X i)
        = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) (X i)"
      by (rule set_integral_uniform_measure_eq[OF M AM pos Xm CM])
    also have "\<dots> = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) (X j)"
      using MG.set_integral_eq[OF CA ij(1) ij(2)] by simp
    also have "\<dots> = set_lebesgue_integral (uniform_measure M A) C (X j)"
      by (rule set_integral_uniform_measure_eq[OF M AM pos Xmj CM, symmetric])
    finally show "set_lebesgue_integral (uniform_measure M A) C (X i)
        = set_lebesgue_integral (uniform_measure M A) C (X j)" .
  qed
qed

section \<open>Restriction of a filtered probability space to a full-measure event\<close>

text \<open>Restricting a filtered probability space to a full-measure event turns
  every almost-sure hypothesis into a pointwise one while changing nothing
  visible to the laws: the restricted measure is again a probability space,
  integrals and integrability are unchanged, pushforwards are unchanged, and
  adaptedness and the martingale property descend to the restricted
  filtration.\<close>

context
  fixes M :: "'a measure" and G :: "'a set"
  assumes P: "prob_space M"
      and G: "G \<in> sets M"
      and full: "AE \<omega> in M. \<omega> \<in> G"
begin

lemma space_restrict_full: "space (restrict_space M G) = G"
  using sets.sets_into_space[OF G] by (auto simp: space_restrict_space)

lemma sets_restrict_full: "G \<inter> space M \<in> sets M"
  using G by (simp add: sets.sets_into_space Int_absorb2)

lemma emeasure_restrict_full:
  assumes S: "S \<in> sets M"
  shows "emeasure (restrict_space M G) (S \<inter> G) = emeasure M S"
proof -
  have "emeasure (restrict_space M G) (S \<inter> G) = emeasure M (S \<inter> G)"
    by (rule emeasure_restrict_space[OF sets_restrict_full]) auto
  also have "\<dots> = emeasure M S"
    using full S G by (intro emeasure_eq_AE) auto
  finally show ?thesis .
qed

lemma prob_space_restrict_full: "prob_space (restrict_space M G)"
proof -
  interpret prob_space M by (rule P)
  have sG: "space M \<inter> G = G"
    using sets.sets_into_space[OF G] by auto
  have "emeasure (restrict_space M G) (space (restrict_space M G))
      = emeasure M (space M)"
    using emeasure_restrict_full[OF sets.top] space_restrict_full
    unfolding sG by simp
  then show ?thesis
    by (intro prob_spaceI) (simp add: emeasure_space_1)
qed

lemma integrable_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f"
  shows "integrable (restrict_space M G) f"
proof -
  have "integrable M (\<lambda>x. indicator G x *\<^sub>R f x)"
    by (rule integrable_mult_indicator[OF G assms])
  then show ?thesis
    by (subst integrable_restrict_space[OF sets_restrict_full])
qed

lemma integral_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<integral>\<omega>. f \<omega> \<partial>restrict_space M G) = (\<integral>\<omega>. f \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. f \<omega> \<partial>restrict_space M G) = (\<integral>\<omega>. indicator G \<omega> *\<^sub>R f \<omega> \<partial>M)"
    by (rule integral_restrict_space[OF sets_restrict_full])
  also have "\<dots> = (\<integral>\<omega>. f \<omega> \<partial>M)"
  proof -
    have m: "(\<lambda>\<omega>. indicator G \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_scaleR borel_measurable_indicator G f)
    show ?thesis
      using full by (intro integral_cong_AE[OF m f]) auto
  qed
  finally show ?thesis .
qed

lemma distr_restrict_full:
  assumes f: "f \<in> measurable M N"
  shows "distr (restrict_space M G) N f = distr M N f"
proof (rule measure_eqI)
  show "sets (distr (restrict_space M G) N f) = sets (distr M N f)"
    by simp
  fix B assume "B \<in> sets (distr (restrict_space M G) N f)"
  then have B: "B \<in> sets N" by simp
  have f': "f \<in> measurable (restrict_space M G) N"
    by (rule measurable_restrict_space1[OF f])
  have vim: "f -` B \<inter> space M \<in> sets M"
    by (rule measurable_sets[OF f B])
  have "emeasure (distr (restrict_space M G) N f) B
      = emeasure (restrict_space M G) (f -` B \<inter> space (restrict_space M G))"
    by (rule emeasure_distr[OF f' B])
  also have "f -` B \<inter> space (restrict_space M G) = (f -` B \<inter> space M) \<inter> G"
    unfolding space_restrict_full using sets.sets_into_space[OF G] by auto
  also have "emeasure (restrict_space M G) ((f -` B \<inter> space M) \<inter> G)
      = emeasure M (f -` B \<inter> space M)"
    by (rule emeasure_restrict_full[OF vim])
  also have "\<dots> = emeasure (distr M N f) B"
    by (rule emeasure_distr[symmetric, OF f B])
  finally show "emeasure (distr (restrict_space M G) N f) B
      = emeasure (distr M N f) B" .
qed

lemma set_integral_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "f \<in> borel_measurable M" and S: "S \<in> sets M"
  shows "set_lebesgue_integral (restrict_space M G) (G \<inter> S) f
       = set_lebesgue_integral M S f"
proof -
  have GS: "G \<inter> S \<in> sets M"
    using G S by blast
  have m: "(\<lambda>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_scaleR borel_measurable_indicator GS f)
  have m': "(\<lambda>\<omega>. indicator S \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_scaleR borel_measurable_indicator S f)
  have "set_lebesgue_integral (restrict_space M G) (G \<inter> S) f
      = (\<integral>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega> \<partial>restrict_space M G)"
    by (simp add: set_lebesgue_integral_def)
  also have "\<dots> = (\<integral>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega> \<partial>M)"
    by (rule integral_restrict_full[OF m])
  also have "\<dots> = (\<integral>\<omega>. indicator S \<omega> *\<^sub>R f \<omega> \<partial>M)"
    using full by (intro integral_cong_AE[OF m m']) (auto simp: indicator_def)
  also have "\<dots> = set_lebesgue_integral M S f"
    by (simp add: set_lebesgue_integral_def)
  finally show ?thesis .
qed

lemma filtered_measure_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
  assumes fm: "filtered_measure M F (0::real)"
  shows "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
proof -
  interpret FM: filtered_measure M F 0 by (rule fm)
  show ?thesis
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    have "sets (restrict_space (F i) G) = (\<inter>) G ` sets (F i)"
      by (rule sets_restrict_space)
    also have "\<dots> \<subseteq> (\<inter>) G ` sets M"
      using FM.subalgebras[OF i] by (auto simp: subalgebra_def)
    also have "\<dots> = sets (restrict_space M G)"
      by (rule sets_restrict_space[symmetric])
    finally have 1: "sets (restrict_space (F i) G)
        \<subseteq> sets (restrict_space M G)" .
    have 2: "space (restrict_space (F i) G) = space (restrict_space M G)"
      by (simp add: space_restrict_space FM.space_F[OF i])
    show "subalgebra (restrict_space M G) (restrict_space (F i) G)"
      using 1 2 by (simp add: subalgebra_def)
  next
    fix i j :: real assume "0 \<le> i" "i \<le> j"
    then show "sets (restrict_space (F i) G)
        \<subseteq> sets (restrict_space (F j) G)"
      using FM.sets_F_mono by (auto simp: sets_restrict_space)
  qed
qed

lemma sigma_finite_filtered_measure_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
  assumes fm: "filtered_measure M F (0::real)"
  shows "sigma_finite_filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
proof -
  have fm': "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
    by (rule filtered_measure_restrict_full[OF fm])
  have fin: "finite_measure (restrict_space M G)"
    by (rule prob_space.finite_measure[OF prob_space_restrict_full])
  have sub0: "subalgebra (restrict_space M G) (restrict_space (F 0) G)"
    by (rule filtered_measure.subalgebras[OF fm']) simp
  show ?thesis
    by (intro sigma_finite_filtered_measure.intro fm'
        sigma_finite_filtered_measure_axioms.intro
        finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fin sub0)
qed

lemma adapted_process_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
    and A :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes ap: "adapted_process M F (0::real) A"
  shows "adapted_process (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0 A"
proof -
  interpret AP: adapted_process M F 0 A by (rule ap)
  have fm: "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
    by (rule filtered_measure_restrict_full[OF AP.filtered_measure_axioms])
  show ?thesis
    by (intro adapted_process.intro fm adapted_process_axioms.intro
        measurable_restrict_space1 AP.adapted)
qed

theorem martingale_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes mg: "martingale M F (0::real) X"
  shows "martingale (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0 X"
proof -
  interpret MX: martingale M F 0 X by (rule mg)
  let ?M' = "restrict_space M G"
  let ?F' = "\<lambda>t. restrict_space (F t) G"
  interpret SFF: sigma_finite_filtered_measure ?M' ?F' 0
    by (rule sigma_finite_filtered_measure_restrict_full
        [OF MX.filtered_measure_axioms])
  have ap: "adapted_process ?M' ?F' 0 X"
    by (rule adapted_process_restrict_full[OF MX.adapted_process_axioms])
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M' (X i)"
      by (intro integrable_restrict_full MX.integrable)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (?F' i)"
    have j: "0 \<le> j" using i ij by linarith
    from A obtain S where S: "S \<in> sets (F i)" and AS: "A = G \<inter> S"
      by (auto simp: sets_restrict_space)
    have SM: "S \<in> sets M"
      using MX.subalgebras[OF i] S by (auto simp: subalgebra_def)
    have Xi: "X i \<in> borel_measurable M"
      by (rule borel_measurable_integrable[OF MX.integrable[OF i]])
    have Xj: "X j \<in> borel_measurable M"
      by (rule borel_measurable_integrable[OF MX.integrable[OF j]])
    have "set_lebesgue_integral ?M' A (X i)
        = set_lebesgue_integral M S (X i)"
      unfolding AS by (rule set_integral_restrict_full[OF Xi SM])
    also have "\<dots> = set_lebesgue_integral M S (X j)"
      using S i ij by (rule MX.set_integral_eq)
    also have "\<dots> = set_lebesgue_integral ?M' A (X j)"
      unfolding AS by (rule set_integral_restrict_full[symmetric, OF Xj SM])
    finally show "set_lebesgue_integral ?M' A (X i)
        = set_lebesgue_integral ?M' A (X j)" .
  qed
qed

end

(*<*)
end
(*>*)
