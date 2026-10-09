section \<open>A continuous vector Brownian motion\<close>

(*<*)
theory Continuous_Brownian_Motion
  imports Vector_Brownian_Martingales "Continuous_Time_Martingales.Modification_Transfer"
    Brownian_Motion_Continuity
begin

(*>*)


text \<open>
  The continuous Brownian state process on the product path space,
             and the transfer of its martingale property to its own natural
             filtration.

    The product model \<open>bm_paths\<close> of \<open>Brownian_Market\<close> has no continuous paths: its
    sample points are arbitrary functions.  The Kolmogorov-Chentsov theorem
    provides a continuous modification Bcont of the coordinate process, and
    \<open>Modification_Transfer\<close> moves the martingale property of the state process
    to the natural filtration of the modification.  The continuous state
    process built here is what the exit-time market needs.\<close>
section \<open>A continuous version of the coordinate process\<close>

definition Bcont :: "(real, real \<Rightarrow> real, real) stochastic_process" where
  "Bcont = (SOME B. modification bm_coord B
     \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>)))"

lemma Bcont_ex: "modification bm_coord Bcont
    \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. Bcont t \<omega>))"
  unfolding Bcont_def
proof (rule someI_ex)
  show "\<exists>B. modification bm_coord B
      \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>))"
    by (rule Brownian_motion_exists[of "1/8"]) auto
qed

lemma Bcont_mod: "modification bm_coord Bcont"
  using Bcont_ex by simp

lemma Bcont_cont: "continuous_on {0..} (\<lambda>t. Bcont t \<omega>)"
  using Bcont_ex by simp

lemma Bcont_meas: "process Bcont u \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
  by (rule modification_bm_coord(2)[OF Bcont_mod])

lemma Bcont_coord:
  assumes u: "u \<in> {0..}"
  shows "AE \<omega> in wiener_pre. Bcont u \<omega> = \<omega> u"
  by (rule modification_bm_coord(3)[OF Bcont_mod u])

section \<open>The continuous state process\<close>

definition cbmX :: "real^'n::finite \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n"
  where "cbmX x0 t \<omega> = x0 + (\<chi> i. Bcont t (\<omega> i))"

lemma measurable_cbmX_coord:
  "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. Bcont t (\<omega> i))
    \<in> bm_paths \<rightarrow>\<^sub>M (borel :: real measure)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
      \<in> Pi\<^sub>M UNIV (\<lambda>_. wiener_pre) \<rightarrow>\<^sub>M wiener_pre"
    by (rule measurable_component_singleton) simp
  then show ?thesis
    unfolding bm_paths_def by (rule measurable_compose[OF _ Bcont_meas])
qed

lemma measurable_cbmX [measurable]:
  "cbmX x0 t \<in> bm_paths \<rightarrow>\<^sub>M (borel :: (real^'n::finite) measure)"
  unfolding cbmX_def
  by (intro borel_measurable_add borel_measurable_const
      measurable_vec_components measurable_cbmX_coord)

lemma cbmX_ae_eq:
  fixes x0 :: "real^'n::finite"
  assumes t: "t \<in> {0..}"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    cbmX x0 t \<omega> = bmX x0 t \<omega>"
proof -
  have coord: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      Bcont t (\<omega> i) = \<omega> i t" for i :: 'n
  proof -
    have proj: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
        \<in> bm_paths \<rightarrow>\<^sub>M wiener_pre"
      unfolding bm_paths_def by (rule measurable_component_singleton) simp
    have "AE \<omega> in distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        wiener_pre (\<lambda>\<omega>. \<omega> i). Bcont t \<omega> = \<omega> t"
      unfolding bm_paths_component using Bcont_coord[OF t] by simp
    from AE_distrD[OF proj this] show ?thesis by simp
  qed
  have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>i \<in> (UNIV :: 'n set). Bcont t (\<omega> i) = \<omega> i t"
    by (intro AE_finite_allI) (auto intro: coord)
  then show ?thesis
    by eventually_elim (simp add: cbmX_def bmX_def vec_eq_iff)
qed

section \<open>The continuous state process is a martingale\<close>

theorem martingale_cbmX:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmX x0)"
proof (rule martingale_of_modification_vec[where X = "bmX x0"])
  show "prob_space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by simp
  show "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (bmX x0)) 0 (bmX x0)"
    by (rule martingale_bmX)
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule measurable_cbmX)
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        cbmX x0 u \<omega> = bmX x0 u \<omega>"
    by (intro cbmX_ae_eq) simp
qed

section \<open>Path continuity\<close>

text \<open>\<open>continuous_on_vec_lambda\<close> is HOL-Analysis's, in
  \<open>Cartesian_Euclidean_Space\<close>, and carries \<open>[continuous_intros]\<close>; this
  theory re-proved it without the attribute, shadowing it.\<close>

lemma cbmX_cont:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..} (\<lambda>t. cbmX x0 t \<omega>)"
  unfolding cbmX_def
  by (intro continuous_on_add continuous_on_const continuous_on_vec_lambda
      Bcont_cont)

text \<open>The same compensated coordinate square, transferred to the continuous
  modification and its own natural filtration, by the general modification
  transfer theorem.  Adaptedness holds because the compensated square is a
  Borel function of the state.\<close>

theorem martingale_cbm_coord_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>t \<omega>. (cbmX x0 t \<omega> $ i)\<^sup>2
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  let ?c = "\<lambda>t. set_lebesgue_integral lborel {0..t}
    (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  let ?Z = "\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2 - ?c t"
  let ?Z' = "\<lambda>t \<omega>. (cbmX x0 t \<omega> $ i)\<^sup>2 - ?c t"
  have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have measZ': "?Z' u \<in> borel_measurable ?M" for u
    by (intro borel_measurable_diff borel_measurable_const
        borel_measurable_power measurable_compose[OF measurable_cbmX prj])
  have aeZ: "AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>" if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      using u by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have adaptZ': "adapted_process ?M ?F 0 ?Z'"
  proof (rule adapted_of_natural_filtration
      [where f = "\<lambda>u y. (y $ i)\<^sup>2 - ?c u"])
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. (\<lambda>y :: real^'n. (y $ i)\<^sup>2 - ?c u)
        \<in> borel_measurable borel"
      by (intro borel_measurable_diff borel_measurable_const
          borel_measurable_power prj)
  qed
  show ?thesis
  proof (rule martingale_of_modification_gen[where X = "bmX x0" and Y = ?Z])
    show "prob_space ?M"
      by simp
    show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 ?Z"
      by (rule martingale_bm_coord_square)
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (intro cbmX_ae_eq) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> ?Z' u \<in> borel_measurable ?M"
      by (rule measZ')
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>"
      by (rule aeZ)
    show "adapted_process ?M ?F 0 ?Z'"
      by (rule adaptZ')
  qed
qed


section \<open>The compensated square is a martingale for the same filtration\<close>

text \<open>The market locales need both the state process and its compensated
  square to be martingales for one filtration, namely the natural filtration
  of the continuous process.  The compensated square of the norm is the sum
  of the compensated coordinate squares above, a bounded linear image of the
  vector of them.\<close>

theorem martingale_cbmX_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>t \<omega>. cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega>
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  let ?V = "\<lambda>t \<omega>. \<chi> i. (cbmX x0 t \<omega> $ i)\<^sup>2
    - set_lebesgue_integral lborel {0..t} (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  have c: "set_lebesgue_integral lborel {0..u} (\<lambda>s. c) = u * c"
    if "0 \<le> u" for u c :: real
    using that by (simp add: set_integral_const)
  have "martingale ?M ?F 0 ?V"
    by (rule martingale_vecI) (unfold vec_lambda_beta, rule martingale_cbm_coord_square)
  then have "martingale ?M ?F 0 (\<lambda>t \<omega>. \<Sum>i\<in>UNIV. ?V t \<omega> $ i)"
    by (rule martingale_bounded_linear_image[where T = "\<lambda>v :: real^'n. \<Sum>i\<in>UNIV. v $ i",
          rotated]) (intro bounded_linear_sum bounded_linear_vec_nth)
  then show ?thesis
    by (rule martingale_cong_ge)
      (simp add: fun_eq_iff c inner_vec_def power2_eq_square sum_subtractf
        sum_distrib_left trace_def)
qed

(*<*)
end
(*>*)
