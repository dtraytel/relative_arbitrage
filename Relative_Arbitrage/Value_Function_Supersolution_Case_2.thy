section \<open>The supersolution, case 2: touching the lower envelope\<close>

(*<*)
theory Value_Function_Supersolution_Case_2
  imports Value_Function_Supersolution_Case_1
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

section \<open>The paper's supersolution: touching the lower envelope\<close>

text \<open>Definition 3.1(b) of the paper touches the lower semicontinuous
  envelope \<open>u\<^sub>*\<close>, not \<open>u\<close> itself, which is what makes the minimisers in
  the Case-2 dichotomy exist and is the form the comparison principle
  consumes.  This section builds the envelope, states the faithful
  supersolution notion, and records two algebraic facts that let the
  verified Euler machinery serve a process whose start is separated
  from the quadratic's centre, since the envelope argument runs the
  construction at points approaching the touching point rather than at
  the touching point itself.\<close>

subsection \<open>The lower semicontinuous envelope\<close>

text \<open>\<open>lsc_env\<close>, \<open>usc_env\<close>, their attainment/extension lemmas, and
  \<open>lsc_env_approx\<close> (arbitrarily near \<open>x\<close> there are points where \<open>u\<close> is
  arbitrarily close to \<open>u\<^sub>*(x)\<close> from above, which supplies the
  approximating sequence the construction below is run along) live in
  @{theory Semicontinuous_Analysis.Semicontinuous_Envelopes} and
  @{theory Semicontinuous_Analysis.Semicontinuity}; what follows are the
  \<open>exit_val\<close>-facing consequences.\<close>

subsection \<open>The faithful supersolution property\<close>

text \<open>\<open>visc_supersol_lsc\<close> lives in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>


subsection \<open>Recentring the quadratic\<close>

text \<open>\<open>quad_grad_shift\<close>, \<open>quad_shift\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>Growth up to a time, on a region\<close>

text \<open>@{thm [source] quad_good_upto} with the confinement region and the
  quadratic's centre both free.  Only reachability from below is used,
  so the proof is the same sequence-and-continuity passage.\<close>

lemma quad_good_upto_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and good: "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
        + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  define tj where "tj = (\<lambda>j. t - t / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "t / (2 * real (Suc j)) \<le> t / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> t" using t0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using t0 by linarith
  qed
  have tju: "tj j < t" for j
  proof -
    have "0 < t / (2 * real (Suc j))" using t0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjc: "tj j \<le> c" for j using tju[of j] tc by linarith
  have glow: "tj j * cm / 2 \<le> g (tj j)" for j
    unfolding g_def
  proof (rule good)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> c" by (rule tjc)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < t" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> t"
  proof -
    have eq: "(\<lambda>j. (t / 2) * inverse (real (Suc j)))
        = (\<lambda>j. t / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (t / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (t / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. t / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. t - t / (2 * real (Suc j))) \<longlonglongrightarrow> t - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..c}"
      using tjl tjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. tj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF tjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

subsection \<open>Case 1 for the lower envelope\<close>

text \<open>The touching-point argument at the envelope.  Two things change
  relative to @{thm [source] exit_val_supersol_contradiction_case1}.
  First, the horizon lemma is applied to the envelope, so it is stated
  for an arbitrary touching function with an explicit cap.  Second, the
  value at the touching point need not be attained there, so the
  construction is run at an approximating point \<open>y\<close> supplied by
  @{thm [source] lsc_env_approx}, with the quadratic still centred at
  \<open>x\<close>.  @{thm [source] quad_shift} and @{thm [source] quad_grad_shift}
  make the verified machinery serve that configuration unchanged: the
  gradient field and the kill hypothesis are the same, and the only
  trace of the displacement is the additive constant \<open>\<psi>(y)\<close>, which the
  choice of \<open>y\<close> drives below any prescribed margin.\<close>

lemma touching_grad_lt_horizon_gen:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and W :: "real^'n \<Rightarrow> real"
  assumes xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      W x - \<phi> x \<le> W y - \<phi> y"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> W y \<le> T"
    and gx0: "g x \<noteq> 0"
  shows "W x < T"
proof -
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  define h where "h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))"
  have hd: "(h has_field_derivative (g x \<bullet> g x)) (at 0)"
  proof -
    have i1: "((\<lambda>s :: real. x + s *\<^sub>R g x)
        has_derivative (\<lambda>u. u *\<^sub>R g x)) (at 0)"
      by (auto intro!: derivative_eq_intros)
    have mem0: "x + (0::real) *\<^sub>R g x \<in> ball x e" using e0 by simp
    have i2: "(\<phi> has_derivative (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> u))
        (at (x + (0::real) *\<^sub>R g x))"
      by (rule dphi[OF mem0])
    have "((\<lambda>s. \<phi> (x + s *\<^sub>R g x)) has_derivative
        (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> (u *\<^sub>R g x))) (at 0)"
      using diff_chain_at[OF i1 i2] by (simp add: o_def)
    then show ?thesis unfolding h_def
      by (rule has_derivative_imp_has_field_derivative)
        (simp add: ac_simps)
  qed
  have gg0: "0 < g x \<bullet> g x"
    using gx0 by simp
  have "((\<lambda>s. (h s - h 0) / (s - 0)) \<longlongrightarrow> g x \<bullet> g x) (at 0)"
    using hd by (simp add: has_field_derivative_iff)
  then have "\<forall>\<^sub>F s in at (0::real). 0 < (h s - h 0) / (s - 0)"
    by (rule order_tendstoD(1)[OF _ gg0])
  then obtain d where d0: "0 < d"
    and hpos: "\<And>s :: real. s \<noteq> 0 \<Longrightarrow> \<bar>s\<bar> < d \<Longrightarrow> 0 < (h s - h 0) / s"
    unfolding eventually_at by (auto simp: dist_real_def)
  define ng where "ng = norm (g x) + 1"
  have ng0: "0 < ng" unfolding ng_def
    using norm_ge_zero[of "g x"] by linarith
  define s where
    "s = min (min d (e / ng)) (min (eK / ng) (\<rho> / ng)) / 2"
  have s0: "0 < s"
    unfolding s_def using d0 e0 eK0 ng0 rho0 by simp
  have sd: "s < d" unfolding s_def using d0 e0 eK0 ng0 rho0 by auto
  have se: "s * ng < e"
  proof -
    have "s \<le> (e / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> e / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using e0 by linarith
  qed
  have sK: "s * ng < eK"
  proof -
    have "s \<le> (eK / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> eK / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using eK0 by linarith
  qed
  have sR: "s * ng < \<rho>"
  proof -
    have "s \<le> (\<rho> / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> \<rho> / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using rho0 by linarith
  qed
  have sg_lt: "s * norm (g x) < min e (min eK \<rho>)"
  proof -
    have "s * norm (g x) \<le> s * ng"
      unfolding ng_def using s0 by (intro mult_left_mono) auto
    then show ?thesis using se sK sR by simp
  qed
  define z where "z = x + s *\<^sub>R g x"
  have dz: "dist x z = s * norm (g x)"
    unfolding z_def dist_norm using s0 by simp
  have zK: "z \<in> K"
  proof -
    have "z \<in> ball x eK" using dz sg_lt by simp
    then show ?thesis using eKK by blast
  qed
  have zR: "dist x z < \<rho>" using dz sg_lt by simp
  have hgt: "\<phi> x < \<phi> z"
  proof -
    have "0 < (h s - h 0) / s" using hpos[of s] s0 sd by simp
    then have "0 < h s - h 0" using s0 by (simp add: zero_less_divide_iff)
    then show ?thesis unfolding h_def z_def by simp
  qed
  have "W x \<le> W z - (\<phi> z - \<phi> x)" using tmin[OF zK zR] by simp
  also have "\<dots> < W z" using hgt by simp
  also have "\<dots> \<le> T" by (rule bnd[OF zK])
  finally show ?thesis .
qed

theorem exit_val_supersol_contradiction_case1_lsc:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      lsc_env (\<lambda>z. enn2real (exit_val k L T K z)) x - \<phi> x
        \<le> lsc_env (\<lambda>z. enn2real (exit_val k L T K z)) y - \<phi> y"
    and gx0: "g x \<noteq> 0"
    and fail: "ell_op k L (g x) H < 1"
  shows False
proof -
  have L1': "1 \<le> L" using L1 by linarith
  have L0: "0 \<le> L" using L1 by linarith
  have T0': "0 \<le> T" using T0 by linarith
  define tv where "tv = (\<lambda>y. enn2real (exit_val k L T K y))"
  define vs where "vs = lsc_env tv"
  have tv0: "\<And>z. 0 \<le> tv z" unfolding tv_def by simp
  have tvT: "\<And>z. tv z \<le> T"
  proof -
    fix z :: "real^'n"
    have "tv z = min (tv z) T"
      unfolding tv_def
      by (rule enn2real_paper_v_horizon_cap[OF T0' order_refl L1' Kc])
    then show "tv z \<le> T" by linarith
  qed
  have vs_le: "\<And>z. vs z \<le> tv z"
    unfolding vs_def by (rule lsc_env_le_self[OF tv0])
  have vs_ge: "\<And>z. 0 \<le> vs z"
    unfolding vs_def by (rule lsc_env_ge[OF tv0])
  have tminv: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      vs x - \<phi> x \<le> vs y - \<phi> y"
    unfolding vs_def tv_def by (rule tmin)
  have vxT: "vs x < T"
  proof (rule touching_grad_lt_horizon_gen[OF xi tf rho0 tminv _ gx0])
    fix y :: "real^'n" assume "y \<in> K"
    show "vs y \<le> T" using vs_le[of y] tvT[of y] by linarith
  qed
  obtain a where aF: "a \<in> feasible k L (g x)"
    and aTr: "- trace (H ** a) / 2 < 1"
    by (rule ell_op_lt_witness[OF k1 kn L1' fail])
  define \<eta>\<^sub>0 where "\<eta>\<^sub>0 = (1 - (- trace (H ** a) / 2)) / 2"
  have h00: "0 < \<eta>\<^sub>0" unfolding \<eta>\<^sub>0_def using aTr by simp
  have trH: "2 * \<eta>\<^sub>0 \<le> 1 + trace (H ** a) / 2"
    unfolding \<eta>\<^sub>0_def by simp
  have aS: "a \<in> sconstraint k L"
    using aF feasible_subset_sconstraint by blast
  define TB where "TB = real CARD('n) * (real CARD('n) * L)"
  have trab: "trace a \<le> TB"
    unfolding TB_def by (rule sconstraint_trace_le[OF L0 aS])
  have tra0: "0 \<le> trace a"
    using sconstraint_trace_ge[OF kn aS] by linarith
  have TB1: "0 < TB + 1"
  proof -
    have "0 \<le> TB" using trab tra0 by linarith
    then show ?thesis by linarith
  qed
  define sft where "sft = min (\<eta>\<^sub>0 / (TB + 1)) 1"
  have sft0: "0 < sft"
    unfolding sft_def using h00 TB1 by simp
  define \<gamma> where "\<gamma> = sft / 4"
  define \<delta> where "\<delta> = sft / 2"
  have g0: "0 < \<gamma>" unfolding \<gamma>_def using sft0 by simp
  have d0: "0 < \<delta>" unfolding \<delta>_def using sft0 by simp
  have gd_le: "2 * \<gamma> + \<delta> \<le> sft" unfolding \<gamma>_def \<delta>_def by simp
  define M where "M = H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose M = M"
    unfolding M_def by (rule transpose_sub_smat[OF symH])
  define \<eta> where "\<eta> = \<eta>\<^sub>0 / 2"
  have e0: "0 < \<eta>" unfolding \<eta>_def using h00 by simp
  have trM: "2 * \<eta> \<le> 1 + trace (M ** a) / 2"
  proof -
    have tr_eq: "trace (M ** a) = trace (H ** a) - (2 * \<gamma> + \<delta>) * trace a"
      unfolding M_def by (rule trace_msub_mat)
    have "(2 * \<gamma> + \<delta>) * trace a \<le> sft * trace a"
      by (rule mult_right_mono[OF gd_le tra0])
    also have "\<dots> \<le> (\<eta>\<^sub>0 / (TB + 1)) * (TB + 1)"
    proof (rule mult_mono)
      show "sft \<le> \<eta>\<^sub>0 / (TB + 1)" unfolding sft_def by simp
      show "trace a \<le> TB + 1" using trab by linarith
      show "0 \<le> \<eta>\<^sub>0 / (TB + 1)" using h00 TB1 by simp
      show "0 \<le> trace a" by (rule tra0)
    qed
    also have "\<dots> = \<eta>\<^sub>0" using TB1 by simp
    finally have "(2 * \<gamma> + \<delta>) * trace a \<le> \<eta>\<^sub>0" .
    then show ?thesis unfolding \<eta>_def using trH tr_eq h00 by linarith
  qed
  have e3: "0 < 3 * \<eta>" using e0 by simp
  have trMa: "4 * \<eta> - 2 \<le> trace (M ** a)"
  proof -
    have d2: "2 * (1 + trace (M ** a) / 2) = 2 + trace (M ** a)"
      by (simp add: field_simps)
    have "2 * (2 * \<eta>) \<le> 2 * (1 + trace (M ** a) / 2)"
      by (rule mult_left_mono[OF trM]) simp
    then have "4 * \<eta> \<le> 2 + trace (M ** a)" unfolding d2 by simp
    then show ?thesis by linarith
  qed
  obtain rphi where rphi0: "0 < rphi"
    and mino: "\<And>z. z \<in> ball x rphi \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    using test_fun_quadratic_minorates[OF tf d0] by metis
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  have rmx0: "0 < min (rphi / 2) (min (eK / 2) (\<rho> / 2))"
    using rphi0 eK0 rho0 by simp
  show False
  proof (rule rotSF_exists[where M = M and x = x, OF aF gx0 e3 rmx0])
    fix SF :: "real^'n \<Rightarrow> real^'n^'n" and rr :: real
    assume rr0: "0 < rr"
      and rrx: "rr \<le> min (rphi / 2) (min (eK / 2) (\<rho> / 2))"
      and SFc: "continuous_on UNIV SF"
      and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
      and killc: "\<And>z. transpose (SF z)
          *v (g x + M *v (closest_point (cball x rr) z - x)) = 0"
      and trcl: "\<And>z. \<bar>trace (M ** (SF z ** transpose (SF z)))
          - trace (M ** a)\<bar> \<le> 3 * \<eta>"
    show False
    proof -
      define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
      have Cm0: "0 \<le> Cm" unfolding Cm_def by (intro sum_nonneg) simp_all
      have rr_phi: "rr < rphi" and rr_K: "rr < eK" and rr_rho: "rr < \<rho>"
        using rrx rphi0 eK0 rho0 by auto
      have cb_phi: "cball x rr \<subseteq> ball x rphi"
        using rr_phi by auto
      have cb_K: "cball x rr \<subseteq> K"
      proof -
        have "cball x rr \<subseteq> ball x eK"
          using rr_K by auto
        then show ?thesis using eKK by blast
      qed
      have marg: "\<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))" for z
      proof -
        have "- (trace (M ** (SF z ** transpose (SF z))) - trace (M ** a))
            \<le> 3 * \<eta>"
          by (rule abs_le_D2[OF trcl])
        then show ?thesis using trMa by linarith
      qed
      \<comment> \<open>on the ball the clamp is the identity, so the kill is the plain one\<close>
      have killR: "\<And>z. z \<in> ball x rr \<Longrightarrow>
          transpose (SF z) *v (g x + M *v (z - x)) = 0"
      proof -
        fix z :: "real^'n" assume "z \<in> ball x rr"
        then have "z \<in> cball x rr" using ball_subset_cball by blast
        then have "closest_point (cball x rr) z = z"
          by (intro closest_point_self)
        then show "transpose (SF z) *v (g x + M *v (z - x)) = 0"
          using killc[of z] by simp
      qed
      define cc where "cc = T / 2"
      have cc0: "0 < cc" unfolding cc_def using T0 by simp
      have ccT: "cc < T" unfolding cc_def using T0 by simp
      have ccT': "cc \<le> T" using ccT by linarith
      define mg where "mg = min (min (\<gamma> * rr\<^sup>2) (cc * \<eta> / 2)) ((T - vs x) / 2)"
      have mg0: "0 < mg"
      proof -
        have "0 < \<gamma> * rr\<^sup>2" using g0 rr0 by simp
        moreover have "0 < cc * \<eta> / 2" using cc0 e0 by simp
        moreover have "0 < (T - vs x) / 2" using vxT by simp
        ultimately show ?thesis unfolding mg_def by simp
      qed
      define cy where "cy = norm (g x) + 2 * Cm + 1"
      have cy1: "1 \<le> cy" unfolding cy_def
        using norm_ge_zero[of "g x"] Cm0 by linarith
      have cy0: "0 < cy" using cy1 by linarith
      define \<delta>y where "\<delta>y = min (rr / 2) (min 1 ((mg / 4) / cy))"
      have dy0: "0 < \<delta>y" unfolding \<delta>y_def using rr0 mg0 cy0 by simp
      have mg20: "0 < mg / 2" using mg0 by simp
      obtain y where dxy: "dist x y < \<delta>y"
          and tvy0: "tv y < lsc_env tv x + mg / 2"
        by (rule lsc_env_approx[OF tv0 dy0 mg20])
      have tvy: "tv y < vs x + mg / 2" unfolding vs_def by (rule tvy0)
      have nyx: "norm (y - x) < \<delta>y"
        using dxy by (simp add: dist_norm norm_minus_commute)
      have ny_rr: "norm (y - x) < rr"
      proof -
        have "\<delta>y \<le> rr / 2" unfolding \<delta>y_def by simp
        then show ?thesis using nyx rr0 by linarith
      qed
      have ny1: "norm (y - x) \<le> 1"
      proof -
        have "\<delta>y \<le> 1" unfolding \<delta>y_def by simp
        then show ?thesis using nyx by linarith
      qed
      have ny_c: "norm (y - x) \<le> (mg / 4) / cy"
      proof -
        have "\<delta>y \<le> (mg / 4) / cy" unfolding \<delta>y_def by simp
        then show ?thesis using nyx by linarith
      qed
      define qy where "qy = g x + M *v (y - x)"
      define psiY where "psiY = g x \<bullet> (y - x)
          + (1/2) * ((y - x) \<bullet> (M *v (y - x)))"
      \<comment> \<open>the displacement costs only the constant \<open>\<psi>(y)\<close>, and it is small\<close>
      have psiY_small: "\<bar>psiY\<bar> \<le> mg / 4"
      proof -
        have nx: "norm (x - x) \<le> norm (y - x)" by simp
        have nyy: "norm (y - x) \<le> norm (y - x)" by simp
        have "\<bar>g x \<bullet> (y - x) + (1/2) * ((y - x) \<bullet> (M *v (y - x)))
            - (g x \<bullet> (x - x) + (1/2) * ((x - x) \<bullet> (M *v (x - x))))\<bar>
            \<le> (norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)"
          unfolding Cm_def
          by (rule quad_diff_bound_gen[OF symM nx nyy])
        then have base: "\<bar>psiY\<bar>
            \<le> (norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)"
          unfolding psiY_def by simp
        have "(norm (g x) + 2 * Cm * norm (y - x)) \<le> cy"
        proof -
          have "2 * Cm * norm (y - x) \<le> 2 * Cm * 1"
            using Cm0 ny1 by (intro mult_left_mono) simp_all
          then show ?thesis unfolding cy_def by simp
        qed
        then have "(norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)
            \<le> cy * norm (y - x)"
          by (rule mult_right_mono) simp
        also have "\<dots> \<le> cy * ((mg / 4) / cy)"
          by (rule mult_left_mono[OF ny_c]) (use cy0 in simp)
        also have "\<dots> = mg / 4" using cy0 by simp
        finally show ?thesis using base by linarith
      qed
      have psiY_ub: "psiY \<le> mg / 4"
        using psiY_small[unfolded abs_le_iff] by linarith
      \<comment> \<open>the growth package, run at \<open>y\<close> with the quadratic centred at \<open>x\<close>\<close>
      obtain P where Pc: "P \<in> exit_class k L T y"
        and AEg: "AE \<omega> in P. \<forall>t.
          0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<longrightarrow>
          (t * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t) - y)
            + (1/2) * ((fst (\<omega> t) - y) \<bullet> (M *v (fst (\<omega> t) - y))))
          \<and> (t * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t) - y)
            + (1/2) * ((fst (\<omega> t) - y) \<bullet> (M *v (fst (\<omega> t) - y))))"
      proof -
        have ROo: "open (ball x rr)" by (rule open_ball)
        have ROb: "\<And>z. z \<in> ball x rr \<Longrightarrow> norm (z - y) \<le> 2 * rr"
        proof -
          fix z :: "real^'n" assume "z \<in> ball x rr"
          then have nz: "norm (z - x) < rr"
            by (simp add: dist_norm norm_minus_commute)
          have "z - y = (z - x) + (x - y)" by simp
          then have "norm (z - y) \<le> norm (z - x) + norm (x - y)"
            by (metis norm_triangle_ineq)
          moreover have "norm (x - y) < rr"
            using ny_rr by (simp add: norm_minus_commute)
          ultimately show "norm (z - y) \<le> 2 * rr" using nz by linarith
        qed
        have killy: "\<And>z. z \<in> ball x rr \<Longrightarrow>
            transpose (SF z) *v (qy + M *v (z - y)) = 0"
        proof -
          fix z :: "real^'n" assume zb: "z \<in> ball x rr"
          have "qy + M *v (z - y) = g x + M *v (z - x)"
            unfolding qy_def by (rule quad_grad_shift)
          then show "transpose (SF z) *v (qy + M *v (z - y)) = 0"
            using killR[OF zb] by simp
        qed
        have margy: "\<And>z. z \<in> ball x rr \<Longrightarrow>
            \<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))"
          using marg by blast
        show ?thesis
          using eulerp_limit_good2_region[OF T0 L1' SFc SFs symM symM
              ROo ROb killy margy killy margy] that by blast
      qed
      have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
        by (rule exit_class_sets[OF Pc])
      have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
        by (rule space_of_path_sets[OF setsP])
      have start: "AE \<omega> in P. fst (\<omega> 0) = y \<and> snd (\<omega> 0) = 0"
        by (rule exit_class_start[OF Pc])
      have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
      define \<theta> where "\<theta> = (\<lambda>\<omega> :: 'n pairpath. min cc (pball_exit T x rr \<omega>))"
      have st: "path_stopping_time T \<theta>"
        unfolding \<theta>_def
        by (rule path_stopping_time_min[OF
              pball_exit_path_stopping_time[OF T0']
              less_imp_le[OF cc0] ccT'])
      have thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
        unfolding \<theta>_def
        by (intro borel_measurable_min pball_exit_measurable[OF T0']
            borel_measurable_const)
      define FN where "FN = (\<lambda>\<omega> :: 'n pairpath.
          pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
          + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>
                \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
             then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
             else 0))"
      have dpp: "(SUP P' \<in> exit_class k L T y. ess_inf_time P' FN)
          \<le> exit_val k L T K y"
        unfolding FN_def
        by (rule exit_val_dpp_sup_ge_time[OF T0 L1' Kc st thM])
      have AEfun: "AE \<omega> in P. ennreal (vs x + mg + psiY) \<le> ennreal (FN \<omega>)"
        using AEg start sp
      proof (eventually_elim)
        case (elim \<omega>)
        have wsp: "\<omega> \<in> space P" using elim(3) .
        have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using wsp by (simp add: spaceP)
        have y0: "fst (\<omega> 0) = y" using elim(2) by blast
        have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
          by (rule path_sets_fst_continuous[OF setsP wsp])
        have sdist: "dist (fst (\<omega> 0)) x < rr"
          using y0 ny_rr by (simp add: dist_norm norm_minus_commute)
        define \<tau> where "\<tau> = pball_exit T x rr \<omega>"
        have tau0: "0 < \<tau>" unfolding \<tau>_def
          by (rule pball_exit_pos[OF T0 sdist cont])
        have tauT: "\<tau> \<le> T" unfolding \<tau>_def by (rule pball_exit_le[OF T0'])
        have thw: "\<theta> \<omega> = min cc \<tau>" unfolding \<theta>_def \<tau>_def by (rule refl)
        have th0: "0 < \<theta> \<omega>" unfolding thw using cc0 tau0 by simp
        have thcc: "\<theta> \<omega> \<le> cc" unfolding thw by simp
        have thtau: "\<theta> \<omega> \<le> \<tau>" unfolding thw by simp
        have thT: "\<theta> \<omega> < T" using thcc ccT by linarith
        have stays: "\<And>s. s \<in> {0..\<tau>} \<Longrightarrow> fst (\<omega> s) \<in> cball x rr"
        proof -
          fix s assume s: "s \<in> {0..\<tau>}"
          have "dist (fst (\<omega> s)) x \<le> rr"
            using pball_exit_stays_cball[OF T0' sdist cont, of s] s
            unfolding \<tau>_def by auto
          then show "fst (\<omega> s) \<in> cball x rr"
            by (simp add: dist_commute)
        qed
        have inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < \<tau> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
        proof -
          fix s assume s0: "0 \<le> s" and st': "s < \<tau>"
          show "fst (\<omega> s) \<in> ball x rr"
          proof (rule ccontr)
            assume nb: "fst (\<omega> s) \<notin> ball x rr"
            have sT: "s \<le> T" using st' tauT by linarith
            have "pexit T (ball x rr) (\<lambda>t. fst (\<omega> t)) \<le> s"
              by (rule pexit_le_of_mem[OF T0' s0 sT]) (use nb in simp)
            then have "\<tau> \<le> s" unfolding \<tau>_def pball_exit_def .
            then show False using st' by linarith
          qed
        qed
        have inK: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> K"
        proof -
          fix s assume s0: "0 \<le> s" and sth: "s \<le> \<theta> \<omega>"
          have "s \<in> {0..\<tau>}" using s0 sth thtau by simp
          then have "fst (\<omega> s) \<in> cball x rr" by (rule stays)
          then show "fst (\<omega> s) \<in> K" using cb_K by blast
        qed
        have pex: "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>"
          by (rule pexit_eq_of_stays[OF less_imp_le[OF th0]])
            (use inK in simp)
        have XinK: "fst (\<omega> (\<theta> \<omega>)) \<in> K" using inK[of "\<theta> \<omega>"] th0 by simp
        have cap: "enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
            = min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
          unfolding tv_def
          by (rule enn2real_paper_v_horizon_cap[OF _ _ L1' Kc])
            (use thT th0 in auto)
        have feq: "FN \<omega> = \<theta> \<omega> + min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
          unfolding FN_def using pex XinK cap by simp
        \<comment> \<open>growth at the stopping time, in the shifted coordinates\<close>
        have growth: "\<theta> \<omega> * (\<eta> - 2) / 2
            \<le> qy \<bullet> (fst (\<omega> (\<theta> \<omega>)) - y)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - y)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - y)))"
        proof (rule quad_good_upto_region[OF wm _ th0])
          show "\<theta> \<omega> \<le> T" using thT by linarith
          show "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> T \<Longrightarrow>
              (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> ball x rr) \<Longrightarrow>
              t' * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t') - y)
                + (1/2) * ((fst (\<omega> t') - y) \<bullet> (M *v (fst (\<omega> t') - y)))"
            using elim(1) by blast
          show "\<And>s. 0 \<le> s \<Longrightarrow> s < \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
          proof -
            fix s assume s0: "0 \<le> s" and sth: "s < \<theta> \<omega>"
            have "s < \<tau>" using sth thtau by linarith
            then show "fst (\<omega> s) \<in> ball x rr" using inside[OF s0] by blast
          qed
        qed
        \<comment> \<open>back to the quadratic centred at \<open>x\<close>\<close>
        define \<psi>X where "\<psi>X = g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
            + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
        have shift: "\<psi>X = psiY
            + (qy \<bullet> (fst (\<omega> (\<theta> \<omega>)) - y)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - y)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - y))))"
          unfolding \<psi>X_def psiY_def qy_def
          by (rule quad_shift[OF symM])
        have gX: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY \<le> \<psi>X"
          unfolding shift using growth by linarith
        \<comment> \<open>touching at the envelope, then the minorant\<close>
        have Xcb: "fst (\<omega> (\<theta> \<omega>)) \<in> cball x rr"
          using stays[of "\<theta> \<omega>"] th0 thtau by simp
        have Xphi: "fst (\<omega> (\<theta> \<omega>)) \<in> ball x rphi" using Xcb cb_phi by blast
        have XinR: "dist x (fst (\<omega> (\<theta> \<omega>))) < \<rho>"
        proof -
          have "dist x (fst (\<omega> (\<theta> \<omega>))) \<le> rr"
            using Xcb by (simp add: dist_commute)
          then show ?thesis using rr_rho by linarith
        qed
        have touch: "vs x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x)
            \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
        proof -
          have "vs x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x) \<le> vs (fst (\<omega> (\<theta> \<omega>)))"
            using tminv[OF XinK XinR] by linarith
          then show ?thesis using vs_le[of "fst (\<omega> (\<theta> \<omega>))"] by linarith
        qed
        have minor: "\<phi> x + g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
            + ((fst (\<omega> (\<theta> \<omega>)) - x)
                \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))) / 2
            \<le> \<phi> (fst (\<omega> (\<theta> \<omega>)))"
          by (rule mino[OF Xphi])
        have soften: "(fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))
            = (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x))
              + 2 * \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          unfolding M_def by (rule quad_soften_split)
        have tvX: "vs x + \<psi>X
            + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))
            \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
          using touch minor soften unfolding \<psi>X_def by linarith
        have QQ: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
            + (if \<tau> \<le> cc then \<gamma> * rr\<^sup>2 else 0)
            \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
        proof (cases "\<tau> \<le> cc")
          case True
          have theq: "\<theta> \<omega> = \<tau>" unfolding thw using True by simp
          have tauTs: "\<tau> < T" using True ccT by linarith
          have sphere: "dist (fst (\<omega> \<tau>)) x = rr"
          proof -
            have ge: "rr \<le> dist (fst (\<omega> \<tau>)) x"
              using pball_exit_outside[OF T0' cont] tauTs
              unfolding \<tau>_def by simp
            have inc: "fst (\<omega> \<tau>) \<in> cball x rr"
              using stays[of \<tau>] tau0 by simp
            then have "dist (fst (\<omega> \<tau>)) x \<le> rr"
              by (simp add: dist_commute)
            then show ?thesis using ge by linarith
          qed
          have nrm: "norm (fst (\<omega> \<tau>) - x) = rr"
            using sphere by (simp add: dist_norm norm_minus_commute)
          have dsq: "(fst (\<omega> \<tau>) - x) \<bullet> (fst (\<omega> \<tau>) - x) = rr\<^sup>2"
            using nrm by (simp add: dot_square_norm)
          have dsq': "(fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              = rr\<^sup>2"
            unfolding theq by (rule dsq)
          have "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY + \<gamma> * rr\<^sup>2
              \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            unfolding dsq' using gX by linarith
          then show ?thesis using True by simp
        next
          case False
          have nn: "0 \<le> \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            using g0 inner_ge_zero by simp
          have "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
              \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            using gX nn by linarith
          then show ?thesis using False by simp
        qed
        have fun_ge: "vs x + mg + psiY \<le> FN \<omega>"
        proof (cases "tv (fst (\<omega> (\<theta> \<omega>))) \<le> T - \<theta> \<omega>")
          case True
          have mfe: "FN \<omega> = \<theta> \<omega> + tv (fst (\<omega> (\<theta> \<omega>)))"
            unfolding feq using True by simp
          have id1: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<theta> \<omega> = \<theta> \<omega> * \<eta> / 2"
            by (simp add: field_simps)
          show ?thesis
          proof (cases "\<tau> \<le> cc")
            case True
            have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY + \<gamma> * rr\<^sup>2
                \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                    \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
              using QQ True by simp
            have the0: "0 \<le> \<theta> \<omega> * \<eta> / 2" using th0 e0 by simp
            have mg1: "mg \<le> \<gamma> * rr\<^sup>2" unfolding mg_def by linarith
            show ?thesis
              unfolding mfe using tvX QQc id1 the0 mg1 by linarith
          next
            case False
            have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
                \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                    \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
              using QQ False by simp
            have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
            have mg2: "mg \<le> cc * \<eta> / 2" unfolding mg_def by linarith
            show ?thesis
              unfolding mfe theq
              using tvX[unfolded theq] QQc[unfolded theq]
                id1[unfolded theq] mg2
              by linarith
          qed
        next
          case False
          have mfe: "FN \<omega> = \<theta> \<omega> + (T - \<theta> \<omega>)"
            unfolding feq using False by simp
          have fT: "FN \<omega> = T" unfolding mfe by simp
          have m3: "mg \<le> (T - vs x) / 2"
            unfolding mg_def by (rule min.cobounded2)
          have mgT: "vs x + 2 * mg \<le> T"
          proof -
            have "(2::real) * mg \<le> 2 * ((T - vs x) / 2)"
              by (rule mult_left_mono[OF m3]) simp
            then have "2 * mg \<le> T - vs x" by simp
            then show ?thesis by (metis le_diff_eq add.commute)
          qed
          have "vs x + mg + psiY \<le> vs x + mg + mg / 4"
            using psiY_ub by linarith
          also have "\<dots> \<le> vs x + 2 * mg" using mg0 by linarith
          also have "\<dots> \<le> T" by (rule mgT)
          finally show ?thesis unfolding fT .
        qed
        show ?case by (rule ennreal_leI[OF fun_ge])
      qed
      have essge: "ennreal (vs x + mg + psiY) \<le> ess_inf_time P FN"
        unfolding ess_inf_time_def
        by (rule Sup_upper) (use AEfun in blast)
      have esle: "ess_inf_time P FN \<le> exit_val k L T K y"
      proof -
        have "ess_inf_time P FN
            \<le> (SUP P' \<in> exit_class k L T y. ess_inf_time P' FN)"
          by (rule SUP_upper[OF Pc])
        then show ?thesis using dpp by (rule order_trans)
      qed
      have vfin: "ennreal (tv y) = exit_val k L T K y"
        unfolding tv_def
        using exit_val_neq_top[OF T0', of k L K y]
        by (simp add: less_top)
      have chain: "ennreal (vs x + mg + psiY) \<le> ennreal (tv y)"
        using order_trans[OF essge esle] by (simp add: vfin)
      have nn: "0 \<le> tv y" by (rule tv0)
      have "vs x + mg + psiY \<le> tv y"
        using chain nn by simp
      then show False using tvy psiY_small mg0 by linarith
    qed
  qed
qed

subsection \<open>Where the envelope is invisible\<close>

text \<open>The uniqueness theorem of \<open>Value_Function_Uniqueness\<close> works with continuous
  solutions, and at a point of continuity the lower envelope is the
  function itself, so on that class the faithful notion
  @{const visc_supersol_lsc} and @{const visc_supersol_env} agree and the
  envelope costs nothing at the interface.  The interface also relies on
  \<open>F\<^sup>* = F\<close> away from \<open>p = 0\<close>, a separate analytic fact.\<close>

text \<open>\<open>lsc_env_eq_self\<close> (at a point of continuity the lower envelope is the
  function itself) lives in
  @{theory Semicontinuous_Analysis.Semicontinuous_Envelopes}.\<close>

lemma visc_supersol_lsc_iff_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and sub: "\<Omega> \<subseteq> K"
    and cont: "\<And>y. y \<in> K \<Longrightarrow> isCont u y"
  shows "visc_supersol_lsc k L K \<Omega> u \<longleftrightarrow> visc_supersol_env k L K \<Omega> u"
proof -
  have eqK: "\<And>y. y \<in> K \<Longrightarrow> lsc_env u y = u y"
    by (rule lsc_env_eq_self[OF B cont])
  have eqO: "\<And>y. y \<in> \<Omega> \<Longrightarrow> lsc_env u y = u y"
    using eqK sub by blast
  show ?thesis
    unfolding visc_supersol_lsc_def visc_supersol_env_def
  proof (intro iffI ballI allI impI)
    fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
    assume h: "\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H"
      and x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
      and tm: "\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y"
    have "\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
    proof
      fix y assume y: "y \<in> K"
      show "lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
        unfolding eqO[OF x] eqK[OF y] using tm y by blast
    qed
    then show "1 \<le> ell_op_usc k L (g x) H" using h x tf by blast
  next
    fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
    assume h: "\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H"
      and x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
      and tm: "\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
    have "\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y"
    proof
      fix y assume y: "y \<in> K"
      have h1: "lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
        using tm y by blast
      show "u x - \<phi> x \<le> u y - \<phi> y"
        using h1 unfolding eqO[OF x] eqK[OF y] .
    qed
    then show "1 \<le> ell_op_usc k L (g x) H" using h x tf by blast
  qed
qed

subsection \<open>The envelope is lower semicontinuous, and attains its infimum\<close>

text \<open>Case 2 tilts the test function and reads off a minimiser of
  \<open>v\<^sub>* - \<psi>\<close> over a small closed ball.  The minimiser exists because the
  lower envelope is lower semicontinuous --- which is the point of the
  envelope --- and an lsc function attains its infimum on a nonempty
  compact set.  The semicontinuity is \<open>lsc_env_lsc\<close> and the attainment is
  \<open>lsc_attains_inf_gen\<close>/\<open>lsc_attains_inf_ex\<close>, both from
  @{theory Semicontinuous_Analysis.Semicontinuous_Envelopes} and
  @{theory Semicontinuous_Analysis.Semicontinuity}.\<close>

subsection \<open>Case 2: minimisers of a tilted quadratic\<close>

text \<open>Case 2 of the supersolution proof perturbs the test function and
  reads off a minimiser of \<open>v\<^sub>* - \<psi>\<close>.  Three ingredients are needed and
  none of them mentions the value function, so all three are proved here
  in the abstract.

  First, an infimum-attainment statement for a lower semicontinuous
  function.  The envelope version proved above attains the infimum of
  \<open>lsc_env u\<close> itself, but what Case 2 minimises is \<open>lsc_env u\<close> minus a
  quadratic, so the argument needs lower semicontinuity as a
  hypothesis rather than as a property of the envelope: this is exactly
  \<open>lsc_attains_inf_gen\<close> from @{theory Semicontinuous_Analysis.Semicontinuity},
  stated there at \<open>'a::metric_space\<close> and instantiated here at
  \<open>real^'n::finite\<close>.  Second, lower semicontinuity is stable under
  subtracting a continuous function --- which is what turns the envelope
  into something whose minimiser over a small closed ball exists; this is
  \<open>lsc_diff_continuous\<close>, from the same theory.\<close>

text \<open>\<open>continuous_on_quad_tilt\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>Third, the strict quadratic minorant.  This is what replaces the
  paper's bump construction.  The paper builds a \<open>C\<^sup>2\<close> function
  \<open>\<phi>\<^sup>m\<close> lying strictly below \<open>v\<^sub>*\<close> off the touching point, exactly
  quadratic near it with a nonsingular Hessian tending to
  \<open>\<nabla>\<^sup>2\<phi>(0)\<close>.  All three of those properties come for free from
  \<open>test_fun_quadratic_minorates\<close> applied at level \<open>\<epsilon>/2\<close>: since
  \<open>H - (\<epsilon>/2) \<cdot> 1 = (H - \<epsilon> \<cdot> 1) + (\<epsilon>/2) \<cdot> 1\<close>, the surplus
  \<open>(\<epsilon>/2)|z - x|\<^sup>2/2\<close> is exactly the strict separation wanted, while
  \<open>H - \<epsilon> \<cdot> 1\<close> is quadratic by construction and tends to \<open>H\<close>.\<close>

lemma test_fun_strict_minorant_zero_grad:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<epsilon> :: real
  assumes tf: "test_fun_at \<phi> g H x" and g0: "g x = 0" and e0: "0 < \<epsilon>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z"
proof -
  have he: "0 < \<epsilon> / 2" using e0 by simp
  obtain r where r0: "0 < r"
    and min2: "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    by (rule test_fun_quadratic_minorates[OF tf he]) blast
  have key: "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
      + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z" if zr: "z \<in> ball x r" for z
  proof -
    have e1: "(H - \<epsilon> *\<^sub>R mat 1) *v (z - x) = H *v (z - x) - \<epsilon> *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib
          scaleR_matrix_vector)
    have e2: "(H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x)
        = H *v (z - x) - (\<epsilon>/2) *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib
          scaleR_matrix_vector)
    have i1: "(z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - \<epsilon> * ((z - x) \<bullet> (z - x))"
      unfolding e1 by (simp add: inner_diff_right)
    have i2: "(z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - (\<epsilon>/2) * ((z - x) \<bullet> (z - x))"
      unfolding e2 by (simp add: inner_diff_right)
    have "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      = \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2"
      unfolding i1 i2 g0 by (simp add: field_simps)
    also have "\<dots> \<le> \<phi> z" by (rule min2[OF zr])
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF r0]) (use key in blast)
qed

text \<open>\<open>tilted_minimiser_close\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>The tilted test function of Case 2 is the quadratic
  \<open>b + \<onehalf>(z - x)\<^sup>T M (z - x) + \<langle>\<eta>, z - x\<rangle>\<close>, centred at the touching point
  \<open>x\<close> but examined at a nearby point \<open>y\<close>.  Recentring it into the normal
  form \<open>c + \<langle>p, z\<rangle> + \<onehalf>z\<^sup>T M z\<close> uses only symmetry of \<open>M\<close>, which
  \<open>test_fun_at\<close> supplies as part of its own definition.\<close>

lemma test_fun_at_shifted_quadratic:
  fixes M :: "real^'n::finite^'n" and x \<eta> y :: "real^'n" and b :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. M *v (z - x) + \<eta>) M y"
proof -
  define p where "p = \<eta> - M *v x"
  define cc where "cc = b + (x \<bullet> (M *v x)) / 2 - \<eta> \<bullet> x"
  have f_eq: "(\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      = (\<lambda>z. cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2)"
  proof (rule ext)
    fix z :: "real^'n"
    have m1: "M *v (z - x) = M *v z - M *v x"
      by (simp add: matrix_vector_mult_diff_distrib)
    have s1: "x \<bullet> (M *v z) = z \<bullet> (M *v x)"
    proof -
      have "x \<bullet> (M *v z) = (transpose M *v x) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (M *v x) \<bullet> z" using sym by simp
      finally show ?thesis by (simp add: inner_commute)
    qed
    have s2: "(M *v x) \<bullet> z = z \<bullet> (M *v x)" by (rule inner_commute)
    have e: "(z - x) \<bullet> (M *v (z - x))
        = z \<bullet> (M *v z) - 2 * (z \<bullet> (M *v x)) + x \<bullet> (M *v x)"
      unfolding m1 using s1
      by (simp add: inner_diff_left inner_diff_right)
    have pz: "p \<bullet> z = \<eta> \<bullet> z - z \<bullet> (M *v x)"
      unfolding p_def by (simp add: inner_diff_left s2)
    have ez: "\<eta> \<bullet> (z - x) = \<eta> \<bullet> z - \<eta> \<bullet> x"
      by (simp add: inner_diff_right)
    show "b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x)
        = cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2"
      unfolding e cc_def pz ez by (simp add: field_simps)
  qed
  have g_eq: "(\<lambda>z :: real^'n. M *v (z - x) + \<eta>) = (\<lambda>z. p + M *v z)"
    by (rule ext) (simp add: p_def algebra_simps)
  show ?thesis
    unfolding f_eq g_eq by (rule test_fun_at_quadratic[OF sym])
qed

text \<open>The heart of Case 2.  Given a strict quadratic separation on a
  closed ball --- which is what \<open>test_fun_strict_minorate_zero_grad\<close>
  delivers once the gradient vanishes --- a tilt by \<open>\<eta>\<close> has a minimiser
  \<open>y\<close>, and that minimiser is within \<open>\<bar>\<eta>\<bar>/c\<close> of the centre.  For
  \<open>\<bar>\<eta>\<bar> < c\<rho>\<close> that puts \<open>y\<close> strictly inside the ball, so the minimality
  is a genuine local touching at \<open>y\<close> --- exactly the hypothesis the
  localised Case 1 consumes.

  No properties of \<open>W\<close> are used beyond lower semicontinuity: the lower
  bound needed for the infimum comes from the separation itself, since
  \<open>W \<ge> W x + Q + c\<bar>z - x\<bar>\<^sup>2\<close> already forces \<open>W - Q - \<langle>\<eta>, \<cdot> - x\<rangle> \<ge> W x - \<bar>\<eta>\<bar>\<rho>\<close>
  on the ball.\<close>

lemma tilted_local_touching:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n"
    and x \<eta> :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y"
    and rho0: "0 < \<rho>" and c0: "0 < c"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hsmall: "norm \<eta> < c * \<rho>"
  obtains y where "dist x y < \<rho>" and "norm (y - x) \<le> norm \<eta> / c"
    and "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
proof -
  define Q where "Q = (\<lambda>z :: real^'n. ((z - x) \<bullet> (M *v (z - x))) / 2)"
  define \<psi> where "\<psi> = (\<lambda>z :: real^'n. Q z + \<eta> \<bullet> (z - x))"
  have Qx: "Q x = 0" unfolding Q_def by simp
  have cpsi: "continuous_on UNIV \<psi>"
    unfolding \<psi>_def Q_def by (rule continuous_on_quad_tilt)
  have flsc: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y - \<psi> y"
    if "a < W z - \<psi> z" for a and z :: "real^'n"
    by (rule lsc_diff_continuous[OF lsc cpsi that])
  have sep': "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    unfolding Q_def by (rule sep)
  have Bnd: "W x - norm \<eta> * \<rho> \<le> W z - \<psi> z" if zc: "z \<in> cball x \<rho>" for z
  proof -
    have s: "W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z" by (rule sep'[OF zc])
    have q0: "0 \<le> c * ((z - x) \<bullet> (z - x))"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF c0] inner_ge_zero])
    have n1: "norm (z - x) \<le> \<rho>"
      using zc by (simp add: dist_norm norm_minus_commute)
    have "norm \<eta> * norm (z - x) \<le> norm \<eta> * \<rho>"
      by (rule mult_left_mono[OF n1 norm_ge_zero])
    then have cs: "\<eta> \<bullet> (z - x) \<le> norm \<eta> * \<rho>"
      using norm_cauchy_schwarz[of \<eta> "z - x"] by linarith
    show ?thesis unfolding \<psi>_def using s q0 cs by linarith
  qed
  have cc: "compact (cball x \<rho>)" by simp
  have ne: "cball x \<rho> \<noteq> {}" using rho0 by auto
  obtain y where yc: "y \<in> cball x \<rho>"
    and ymin: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W y - \<psi> y \<le> W w - \<psi> w"
  proof (rule lsc_attains_inf_gen[OF flsc Bnd cc ne])
    fix z :: "real^'n" assume a1: "z \<in> cball x \<rho>"
      and a2: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W z - \<psi> z \<le> W w - \<psi> w"
    show thesis by (rule that[OF a1 a2])
  qed
  have xc: "x \<in> cball x \<rho>" using rho0 by simp
  have close: "norm (y - x) \<le> norm \<eta> / c"
  proof (rule tilted_minimiser_close[OF sep' Qx c0 xc yc])
    fix z :: "real^'n" assume zc: "z \<in> cball x \<rho>"
    show "W y - Q y - \<eta> \<bullet> (y - x) \<le> W z - Q z - \<eta> \<bullet> (z - x)"
      using ymin[OF zc] unfolding \<psi>_def by simp
  qed
  have hlt: "norm \<eta> / c < \<rho>"
    using hsmall c0 by (simp add: pos_divide_less_eq mult.commute)
  have dxy: "dist x y < \<rho>"
  proof -
    have "dist x y = norm (y - x)" by (simp add: dist_norm norm_minus_commute)
    then show ?thesis using close hlt by linarith
  qed
  have loc: "W y - \<psi> y \<le> W w - \<psi> w" if dw: "dist y w < \<rho> - dist x y" for w
  proof -
    have "dist x w \<le> dist x y + dist y w" by (rule dist_triangle)
    then have "dist x w < \<rho>" using dw by linarith
    then have "w \<in> cball x \<rho>" by (auto simp: dist_commute)
    then show ?thesis by (rule ymin)
  qed
  show ?thesis
  proof (rule that[OF dxy close])
    fix w :: "real^'n" assume dw: "dist y w < \<rho> - dist x y"
    show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      using loc[OF dw] by (simp add: \<psi>_def Q_def)
  qed
qed

text \<open>Assembling the separation for the value function.  On a small
  enough ball the touching hypothesis and the strict quadratic minorant
  combine into exactly the separation \<open>tilted_local_touching\<close> wants:
  the touching gives \<open>\<phi> z - \<phi> x \<le> W z - W x\<close> and the minorant gives
  \<open>Q\<^sub>\<epsilon>(z) + (\<epsilon>/4)\<bar>z - x\<bar>\<^sup>2 \<le> \<phi> z - \<phi> x\<close>.  The radius is also shrunk
  below the distance to the complement of \<open>interior K\<close>, so that every
  point of the ball is an admissible touching point in its own right.\<close>

lemma exit_val_case2_separation:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
    and e0: "0 < \<epsilon>"
  obtains \<rho> where "0 < \<rho>" and "cball x \<rho> \<subseteq> interior K"
    and "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x
        + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) z"
proof -
  obtain r where r0: "0 < r"
    and mino: "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z"
    by (rule test_fun_strict_minorant_zero_grad[OF tf gx0 e0]) blast
  have exb: "\<exists>e>0. ball x e \<subseteq> interior K"
    using open_interior[of K, unfolded open_contains_ball] xi by blast
  obtain e where e0': "0 < e" and eK: "ball x e \<subseteq> interior K"
    using exb by blast
  define \<rho> where "\<rho> = min (r / 2) (min (\<rho>\<^sub>0 / 2) (e / 2))"
  have rho: "0 < \<rho>" unfolding \<rho>_def using r0 rho0 e0' by simp
  have rlt: "\<rho> < r" unfolding \<rho>_def using r0 rho0 e0' by simp
  have rholt: "\<rho> < \<rho>\<^sub>0" unfolding \<rho>_def using r0 rho0 e0' by simp
  have elt: "\<rho> < e" unfolding \<rho>_def using r0 rho0 e0' by simp
  have sub: "cball x \<rho> \<subseteq> interior K"
  proof
    fix z :: "real^'n" assume "z \<in> cball x \<rho>"
    then have "dist x z \<le> \<rho>" by simp
    then have "dist x z < e" using elt by linarith
    then show "z \<in> interior K" using eK by auto
  qed
  have key: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x
      + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
      + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
    \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) z"
    if zc: "z \<in> cball x \<rho>" for z
  proof -
    have dzx: "dist x z \<le> \<rho>" using zc by simp
    have zb: "z \<in> ball x r" using dzx rlt by auto
    have zK: "z \<in> K" using sub zc interior_subset by blast
    have dxz: "dist x z < \<rho>\<^sub>0" using dzx rholt by linarith
    have t: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) z - \<phi> z"
      by (rule tmin[OF zK dxz])
    have m: "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z" by (rule mino[OF zb])
    show ?thesis using t m by linarith
  qed
  show ?thesis by (rule that[OF rho sub]) (use key in blast)
qed

text \<open>Case 2's tilt step for the value function.  The minimiser \<open>y\<close>
  produced by \<open>tilted_local_touching\<close> lies strictly inside the ball, so
  it is an interior point of \<open>K\<close> at which the tilted quadratic touches
  \<open>v\<^sub>*\<close> from below on a whole neighbourhood.  That is precisely the
  hypothesis of the localised Case 1, which therefore applies at \<open>y\<close>
  whenever the tilted gradient there is nonzero.\<close>

theorem exit_val_case2_tilt_step:
  fixes K :: "(real^'n::finite) set" and x \<eta> :: "real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and symH: "transpose H = H"
    and e0: "0 < \<epsilon>" and rho: "0 < \<rho>"
    and sub: "cball x \<rho> \<subseteq> interior K"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x
        + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) z"
    and hsm: "norm \<eta> < (\<epsilon> / 4) * \<rho>"
  obtains y where "dist x y < \<rho>" and "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
    and "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0 \<Longrightarrow>
      1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  have symM: "transpose (H - \<epsilon> *\<^sub>R mat 1) = H - \<epsilon> *\<^sub>R mat 1"
    by (rule transpose_sub_smat[OF symH])
  have c0: "0 < \<epsilon> / 4" using e0 by simp
  have tv0: "\<And>u. 0 \<le> enn2real (exit_val k L T K u)" by simp
  have lscW: "\<exists>d>0. \<forall>u. dist z u < d \<longrightarrow>
      a < lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) u"
    if lt: "a < lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) z"
    for a and z :: "real^'n"
    by (rule lsc_env_lsc[OF tv0 lt])
  obtain y where dxy: "dist x y < \<rho>"
    and close: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
    and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y
          - (((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) w
          - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
  proof (rule tilted_local_touching[OF lscW rho c0 sep hsm])
    fix yy :: "real^'n"
    assume a1: "dist x yy < \<rho>" and a2: "norm (yy - x) \<le> norm \<eta> / (\<epsilon> / 4)"
      and a3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
        lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) yy
            - (((yy - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (yy - x))) / 2
               + \<eta> \<bullet> (yy - x))
          \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) w
            - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2
               + \<eta> \<bullet> (w - x))"
    show thesis by (rule that[OF a1 a2 a3])
  qed
  have rp: "0 < \<rho> - dist x y" using dxy by simp
  have yi: "y \<in> interior K"
  proof -
    have "y \<in> cball x \<rho>" using dxy by (auto simp: dist_commute)
    then show ?thesis using sub by blast
  qed
  have tfy: "test_fun_at
      (\<lambda>z. 0 + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. (H - \<epsilon> *\<^sub>R mat 1) *v (z - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1) y"
    by (rule test_fun_at_shifted_quadratic[OF symM])
  have tminy: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y
        - (0 + ((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) w
        - (0 + ((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    if wK: "w \<in> K" and dw: "dist y w < \<rho> - dist x y" for w
    using loc[OF dw] by simp
  have gt: "1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
      (H - \<epsilon> *\<^sub>R mat 1)"
    if gy: "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1)"
    then have flt: "ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1) < 1" by simp
    show False
      by (rule exit_val_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc yi
            tfy rp tminy gy flt])
  qed
  show ?thesis by (rule that[OF dxy close]) (use gt in blast)
qed

subsection \<open>Case 2, second horn: quadratic pinching forces local constancy\<close>

text \<open>\<open>pinch_segment_bound\<close>, \<open>pinch_implies_constant\<close>, \<open>quad_form_bounded_below\<close>, \<open>quad_minimality_pinch\<close>, \<open>singular_matrix_avoids_range\<close>, \<open>invertible_matrix_vector_inj\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma horn_B_locally_constant:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n" and x :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>d>0. \<forall>u. dist z u < d \<longrightarrow> a < W u"
    and symM: "transpose M = M" and inv: "invertible M"
    and rho: "0 < \<rho>" and c0: "0 < c"
    and h0: "0 < h" and hle: "h \<le> c * \<rho>"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hornB: "\<And>\<eta> y. norm \<eta> < h \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      norm (y - x) \<le> norm \<eta> / c \<Longrightarrow>
      (\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
        W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x)))
      \<Longrightarrow> M *v (y - x) + \<eta> = 0"
  obtains r where "0 < r" and "\<And>y. dist x y < r \<Longrightarrow> W y = W x"
proof -
  obtain C where C0: "0 \<le> C"
    and Cb: "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
  proof (rule quad_form_bounded_below[where M = M])
    fix CC :: real
    assume a1: "0 \<le> CC"
      and a2: "\<And>u :: real^'n.
        - (CC * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    show thesis by (rule that[OF a1 a2])
  qed
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define N where "N = onorm ((*v) M)"
  have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
  have N1: "0 < N + 1" using N0 by simp
  define r0 where "r0 = min (\<rho> / 2) (h / (2 * (N + 1)))"
  have r00: "0 < r0" unfolding r0_def using rho h0 N1 by simp
  have cp: "0 < c * \<rho>" using c0 rho by simp
  have pinch0: "W y - C * (dist y w * dist y w) \<le> W w"
    if dy: "dist x y < r0" and dw: "dist y w < \<rho> - dist x y"
    for y w :: "real^'n"
  proof -
    define \<eta> where "\<eta> = - (M *v (y - x))"
    have nyx: "norm (y - x) = dist x y"
      by (simp add: dist_norm norm_minus_commute)
    have e1: "norm \<eta> = norm (M *v (y - x))" unfolding \<eta>_def by simp
    have e2: "norm (M *v (y - x)) \<le> N * norm (y - x)"
      unfolding N_def by (rule onorm[OF bl])
    have s1: "N * norm (y - x) \<le> N * r0"
      by (rule mult_left_mono) (use nyx dy N0 in auto)
    have s2: "N * r0 \<le> (N + 1) * r0"
      by (rule mult_right_mono) (use r00 in auto)
    have hb: "norm \<eta> \<le> (N + 1) * r0" using e1 e2 s1 s2 by linarith
    have q1: "(N + 1) * r0 \<le> (N + 1) * (h / (2 * (N + 1)))"
      by (rule mult_left_mono) (use r0_def N1 in auto)
    have q2: "(N + 1) * (h / (2 * (N + 1))) = h / 2"
      using N1 by (simp add: field_simps)
    have hlth: "norm \<eta> < h" using hb q1 q2 h0 by linarith
    have hlt: "norm \<eta> < c * \<rho>" using hlth hle by linarith
    obtain y' where dxy': "dist x y' < \<rho>"
      and cl': "norm (y' - x) \<le> norm \<eta> / c"
      and loc': "\<And>w. dist y' w < \<rho> - dist x y' \<Longrightarrow>
        W y' - (((y' - x) \<bullet> (M *v (y' - x))) / 2 + \<eta> \<bullet> (y' - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    proof (rule tilted_local_touching[OF lsc rho c0 sep hlt])
      fix yy :: "real^'n"
      assume b1: "dist x yy < \<rho>" and b2: "norm (yy - x) \<le> norm \<eta> / c"
        and b3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
          W yy - (((yy - x) \<bullet> (M *v (yy - x))) / 2 + \<eta> \<bullet> (yy - x))
            \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      show thesis by (rule that[OF b1 b2 b3])
    qed
    have g0: "M *v (y' - x) + \<eta> = 0"
      by (rule hornB[OF hlth dxy' cl' loc'])
    have meq: "M *v (y' - x) = M *v (y - x)"
      using g0 unfolding \<eta>_def by (simp add: algebra_simps)
    have yeq: "y' = y"
      using invertible_matrix_vector_inj[OF inv meq] by simp
    show ?thesis
    proof (rule quad_minimality_pinch[OF symM Cb])
      show "M *v (y - x) + \<eta> = 0" using g0 unfolding yeq .
      show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        using loc'[of w] dw unfolding yeq by simp
    qed
  qed
  define r where "r = min r0 (\<rho> / 4)"
  have r0': "0 < r" unfolding r_def using r00 rho by simp
  have pin: "W u - C * (dist u w * dist u w) \<le> W w"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" for u w :: "real^'n"
  proof -
    have du: "dist x u < r" using ub by simp
    have dw: "dist x w < r" using wb by simp
    have a1: "dist x u < r0" using du unfolding r_def by simp
    have a2: "dist u w < \<rho> - dist x u"
    proof -
      have t: "dist u w \<le> dist u x + dist x w" by (rule dist_triangle)
      have "dist u x < r" using du by (simp add: dist_commute)
      then have lt2: "dist u w < 2 * r" using t dw by linarith
      have g1: "2 * r \<le> \<rho> / 2" unfolding r_def using rho by simp
      have g2: "dist x u < \<rho> / 4" using du unfolding r_def by simp
      show ?thesis using lt2 g1 g2 rho by linarith
    qed
    show ?thesis by (rule pinch0[OF a1 a2])
  qed
  have const: "W y = W x" if dy: "dist x y < r" for y :: "real^'n"
  proof (rule pinch_implies_constant[OF r0' C0])
    show "\<And>u w. u \<in> ball x r \<Longrightarrow> w \<in> ball x r \<Longrightarrow>
        W u - C * (dist u w * dist u w) \<le> W w"
      by (rule pin)
    show "y \<in> ball x r" using dy by simp
  qed
  show ?thesis by (rule that[OF r0']) (use const in blast)
qed

text \<open>The second horn dies here.  Suppose \<open>v\<^sub>*\<close> were constant \<open>= c\<close> on a
  ball around \<open>x\<close> whose closure lies in \<open>K\<close>.  The envelope's own defining
  property supplies points \<open>z\<close> arbitrarily close to \<open>x\<close> at which \<open>v\<close>
  itself is within \<open>\<theta>/2\<close> of \<open>c\<close>.  But the deterministic-radius member
  started at such a \<open>z\<close> stays inside the ball for a time \<open>\<theta>\<close> that does
  not shrink with \<open>z\<close>, and its endpoint is again in the ball where
  \<open>v \<ge> c\<close>; so \<open>exit_val_ball_lower_plus\<close> gives \<open>v z \<ge> \<theta> + c\<close>.  Those two
  are incompatible.

  The hypothesis \<open>c < T/2\<close> is what keeps the horizon cap inert.  It
  cannot be dropped: if \<open>v \<equiv> T\<close> on an open set then \<open>v\<^sub>*\<close> is locally
  constant there, and no contradiction is available --- indeed the
  supersolution inequality itself fails at such a point, since a
  constant test function would demand \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.  For a
  bounded \<open>K\<close> the hypothesis is discharged by
  @{thm [source] exit_val_le_ball_bound} once \<open>T\<close> exceeds twice the ball
  bound.\<close>

theorem exit_val_not_locally_constant:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and tv :: "real^'n \<Rightarrow> real" and r T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and tvdef: "tv = (\<lambda>u. enn2real (exit_val k L T K u))"
    and r0: "0 < r" and sub: "cball x r \<subseteq> K"
    and cap: "lsc_env tv x < T / 2"
    and const: "\<And>y. dist x y < r \<Longrightarrow> lsc_env tv y = lsc_env tv x"
  shows False
proof -
  have tv0: "\<And>u. 0 \<le> tv u" unfolding tvdef by simp
  have c0: "0 \<le> lsc_env tv x" by (rule lsc_env_ge[OF tv0])
  define rB where "rB = r / 4"
  have rB0: "0 < rB" unfolding rB_def using r0 by simp
  have rBr: "5 * rB / 4 \<le> r" unfolding rB_def using r0 by simp
  define e :: "real^'n" where "e = axis (undefined :: 'n) (1 :: real)"
  have e1: "norm e = 1" unfolding e_def by simp
  define y\<^sub>0 where "y\<^sub>0 = x + (rB / 4) *\<^sub>R e"
  have dxy: "dist x y\<^sub>0 = rB / 4"
  proof -
    have "dist x y\<^sub>0 = norm ((rB / 4) *\<^sub>R e)"
      unfolding y\<^sub>0_def by (simp add: dist_norm)
    also have "\<dots> = \<bar>rB / 4\<bar> * norm e" by simp
    finally show ?thesis using rB0 e1 by simp
  qed
  have near: "dist x w \<le> 5 * rB / 4" if "dist y\<^sub>0 w \<le> rB" for w
  proof -
    have "dist x w \<le> dist x y\<^sub>0 + dist y\<^sub>0 w" by (rule dist_triangle)
    then show ?thesis using dxy that by linarith
  qed
  have subB: "cball y\<^sub>0 rB \<subseteq> K"
  proof
    fix w :: "real^'n" assume "w \<in> cball y\<^sub>0 rB"
    then have "dist y\<^sub>0 w \<le> rB" by simp
    then have "dist x w \<le> r" using near[of w] rBr by linarith
    then show "w \<in> K" using sub by auto
  qed
  have cn0: "0 < real CARD('n) - 1"
  proof -
    have "2 \<le> CARD('n)" using k1 kn by linarith
    then have "(2 :: real) \<le> real CARD('n)"
      by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis by linarith
  qed
  define \<theta> where "\<theta> = min (T / 2) (rB\<^sup>2 / (4 * (real CARD('n) - 1)))"
  have th0: "0 < \<theta>" unfolding \<theta>_def using T0 rB0 cn0 by simp
  have vlow: "lsc_env tv x \<le> tv w" if wb: "w \<in> ball y\<^sub>0 rB" for w
  proof -
    have lt: "dist y\<^sub>0 w < rB" using wb by simp
    have tr: "dist x w \<le> dist x y\<^sub>0 + dist y\<^sub>0 w" by (rule dist_triangle)
    have "dist x w < r" using tr lt dxy rBr by linarith
    then have "lsc_env tv w = lsc_env tv x" by (rule const)
    moreover have "lsc_env tv w \<le> tv w" by (rule lsc_env_le_self[OF tv0])
    ultimately show ?thesis by linarith
  qed
  have d8: "0 < rB / 8" using rB0 by simp
  have t2: "0 < \<theta> / 2" using th0 by simp
  obtain z where dz: "dist x z < rB / 8"
    and vz: "tv z < lsc_env tv x + \<theta> / 2"
  proof (rule lsc_env_approx[OF tv0 d8 t2])
    fix zz :: "real^'n"
    assume a1: "dist x zz < rB / 8" and a2: "tv zz < lsc_env tv x + \<theta> / 2"
    show thesis by (rule that[OF a1 a2])
  qed
  have dzy: "dist z y\<^sub>0 < 3 * rB / 8"
  proof -
    have "dist z y\<^sub>0 \<le> dist z x + dist x y\<^sub>0" by (rule dist_triangle)
    moreover have "dist z x = dist x z" by (rule dist_commute)
    ultimately show ?thesis using dz dxy by linarith
  qed
  have dzy': "rB / 8 < dist z y\<^sub>0"
  proof -
    have "dist x y\<^sub>0 \<le> dist x z + dist z y\<^sub>0" by (rule dist_triangle)
    then show ?thesis using dz dxy by linarith
  qed
  have nzy: "norm (z - y\<^sub>0) = dist z y\<^sub>0" by (simp add: dist_norm)
  have zy: "z \<noteq> y\<^sub>0" using dzy' rB0 by auto
  have zin: "norm (z - y\<^sub>0) < rB" unfolding nzy using dzy rB0 by linarith
  have pv: "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min (lsc_env tv x) (T / 2))
      \<le> exit_val k L T K z"
  proof (rule exit_val_ball_lower_plus[OF T0 L1 k1 kn Kc subB zy zin c0])
    fix w :: "real^'n" assume "w \<in> ball y\<^sub>0 rB"
    then have "lsc_env tv x \<le> tv w" by (rule vlow)
    then show "lsc_env tv x \<le> enn2real (exit_val k L T K w)"
      using tvdef by simp
  qed
  have sq: "(norm (z - y\<^sub>0))\<^sup>2 \<le> rB\<^sup>2 / 2"
  proof -
    have n0: "0 \<le> norm (z - y\<^sub>0)" by simp
    have rBsq: "0 \<le> rB\<^sup>2" by simp
    have "(norm (z - y\<^sub>0))\<^sup>2 \<le> (3 * rB / 8)\<^sup>2"
      using zin dzy n0 unfolding nzy by (intro power_mono) auto
    also have "\<dots> = 9 / 64 * rB\<^sup>2"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> \<le> 1 / 2 * rB\<^sup>2"
      by (rule mult_right_mono[OF _ rBsq]) simp
    also have "\<dots> = rB\<^sup>2 / 2" by simp
    finally show ?thesis .
  qed
  have B: "rB\<^sup>2 / (4 * (real CARD('n) - 1))
      \<le> (rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
  proof -
    have m0: "0 \<le> 2 * (real CARD('n) - 1)" using cn0 by auto
    have a: "rB\<^sup>2 / 2 \<le> rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2" using sq by linarith
    have eqd: "(rB\<^sup>2 / 2) / (2 * (real CARD('n) - 1))
        = rB\<^sup>2 / (4 * (real CARD('n) - 1))"
      by (simp add: field_simps)
    have "(rB\<^sup>2 / 2) / (2 * (real CARD('n) - 1))
        \<le> (rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
      by (rule divide_right_mono[OF a m0])
    then show ?thesis unfolding eqd[symmetric] .
  qed
  have mc: "min (lsc_env tv x) (T / 2) = lsc_env tv x" using cap by simp
  have fin: "\<theta> + lsc_env tv x \<le> min (T / 2)
      ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min (lsc_env tv x) (T / 2)"
    unfolding \<theta>_def mc using B by linarith
  have T0': "0 \<le> T" using T0 by linarith
  have ltop: "exit_val k L T K z < \<top>"
    using exit_val_neq_top[OF T0'] by (simp add: less_top)
  have eq: "ennreal (tv z) = exit_val k L T K z"
    unfolding tvdef using ltop by simp
  have "ennreal (\<theta> + lsc_env tv x) \<le> exit_val k L T K z"
  proof -
    have "ennreal (\<theta> + lsc_env tv x) \<le> ennreal (min (T / 2)
        ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
        + min (lsc_env tv x) (T / 2))"
      by (rule ennreal_leI[OF fin])
    then show ?thesis using pv by (rule order_trans)
  qed
  then have "ennreal (\<theta> + lsc_env tv x) \<le> ennreal (tv z)"
    unfolding eq .
  then have ge: "\<theta> + lsc_env tv x \<le> tv z"
    using tv0[of z] by simp
  show False using ge vz th0 by linarith
qed

text \<open>Horn A at a given local minimiser.  \<open>exit_val_case2_tilt_step\<close>
  produces its own minimiser; the assembly instead has one handed to it
  by the case split, so the last step of that proof is isolated here.\<close>

lemma exit_val_case2_at_minimiser:
  fixes K :: "(real^'n::finite) set" and x y \<eta> :: "real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and symH: "transpose H = H"
    and rho: "0 < \<rho>" and sub: "cball x \<rho> \<subseteq> interior K"
    and dxy: "dist x y < \<rho>"
    and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y
          - (((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) w
          - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    and gy: "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0"
  shows "1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
      (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  have symM: "transpose (H - \<epsilon> *\<^sub>R mat 1) = H - \<epsilon> *\<^sub>R mat 1"
    by (rule transpose_sub_smat[OF symH])
  have rp: "0 < \<rho> - dist x y" using dxy by simp
  have yi: "y \<in> interior K"
  proof -
    have "y \<in> cball x \<rho>" using dxy by (auto simp: dist_commute)
    then show ?thesis using sub by blast
  qed
  have tfy: "test_fun_at
      (\<lambda>z. 0 + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. (H - \<epsilon> *\<^sub>R mat 1) *v (z - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1) y"
    by (rule test_fun_at_shifted_quadratic[OF symM])
  have tminy: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y
        - (0 + ((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) w
        - (0 + ((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    if wK: "w \<in> K" and dw: "dist y w < \<rho> - dist x y" for w
    using loc[OF dw] by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1)"
    then have flt: "ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1) < 1" by simp
    show False
      by (rule exit_val_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc yi
            tfy rp tminy gy flt])
  qed
qed

subsection \<open>Case 2 assembled at a fixed \<open>\<epsilon>\<close>\<close>

text \<open>The dichotomy.  Either arbitrarily small tilts admit a local
  minimiser with nonzero gradient --- and then Case 1 fires at each of
  them, the gradients tend to \<open>0\<close> because \<open>\<bar>y - x\<bar> \<le> 4\<bar>\<eta>\<bar>/\<epsilon>\<close>, and
  \<open>ell_op_usc_ge_one_limit\<close> delivers the inequality at \<open>p = 0\<close> --- or
  some threshold fails, which is exactly the hypothesis of
  \<open>horn_B_locally_constant\<close>, and then \<open>v\<^sub>*\<close> is locally constant, which
  \<open>exit_val_not_locally_constant\<close> refutes.

  A singular \<open>H - \<epsilon>\<cdot>1\<close> needs no separate treatment: it supplies
  arbitrarily small tilts for which the gradient can never vanish, so
  the first branch always applies.  That is why the second branch may
  assume invertibility.\<close>

theorem exit_val_case2_eps:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
    and cap: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
    and e0: "0 < \<epsilon>"
  shows "1 \<le> ell_op_usc k L 0 (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  let ?W = "lsc_env (\<lambda>u. enn2real (exit_val k L T K u))"
  let ?M = "H - \<epsilon> *\<^sub>R mat 1"
  have L1': "1 \<le> L" using L1 by linarith
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose ?M = ?M" by (rule transpose_sub_smat[OF symH])
  have c0: "0 < \<epsilon> / 4" using e0 by simp
  have tv0: "\<And>u. (0 :: real) \<le> enn2real (exit_val k L T K u)" by simp
  have lscW: "\<exists>d>0. \<forall>u. dist z u < d \<longrightarrow> a < ?W u"
    if lt: "a < ?W z" for a and z :: "real^'n"
    by (rule lsc_env_lsc[OF tv0 lt])
  obtain \<rho> where rho: "0 < \<rho>" and subK: "cball x \<rho> \<subseteq> interior K"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      ?W x + ((z - x) \<bullet> (?M *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> ?W z"
  proof (rule exit_val_case2_separation[OF xi tf gx0 rho0 tmin e0])
    fix rr :: real
    assume a1: "0 < rr" and a2: "cball x rr \<subseteq> interior K"
      and a3: "\<And>z. z \<in> cball x rr \<Longrightarrow>
        ?W x + ((z - x) \<bullet> (?M *v (z - x))) / 2
          + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> ?W z"
    show thesis by (rule that[OF a1 a2 a3])
  qed
  define good where "good = (\<lambda>\<delta> :: real. \<exists>\<eta> y :: real^'n.
      norm \<eta> < \<delta> \<and> dist x y < \<rho> \<and> norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4) \<and>
      (\<forall>w. dist y w < \<rho> - dist x y \<longrightarrow>
        ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x)))
      \<and> ?M *v (y - x) + \<eta> \<noteq> 0)"
  define \<delta>s where "\<delta>s = (\<lambda>j :: nat. min ((\<epsilon> / 4) * \<rho>) (1 / real (Suc j)))"
  have ds0: "0 < \<delta>s j" for j unfolding \<delta>s_def using c0 rho by simp
  show ?thesis
  proof (cases "\<forall>j. good (\<delta>s j)")
    case True
    have bl: "bounded_linear ((*v) ?M)"
      by (rule matrix_vector_mul_bounded_linear)
    define N where "N = onorm ((*v) ?M)"
    have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
    have Cpos: "0 \<le> 4 * N / \<epsilon> + 1" using N0 e0 by simp
    have ex: "\<exists>p :: real^'n. 1 \<le> ell_op k L p ?M
        \<and> norm p \<le> (4 * N / \<epsilon> + 1) * \<delta>s j" for j
    proof -
      have gd: "good (\<delta>s j)" using True by blast
      obtain \<eta> y :: "real^'n" where hn: "norm \<eta> < \<delta>s j"
        and dxy: "dist x y < \<rho>"
        and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
        and loc: "\<forall>w. dist y w < \<rho> - dist x y \<longrightarrow>
          ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        and gy: "?M *v (y - x) + \<eta> \<noteq> 0"
        using gd unfolding good_def by blast
      have ge: "1 \<le> ell_op k L (?M *v (y - x) + \<eta>) ?M"
      proof (rule exit_val_case2_at_minimiser[OF T0 L1 k1 kn Kc symH rho subK
              dxy _ gy])
        fix w :: "real^'n" assume "dist y w < \<rho> - dist x y"
        then show "?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
          using loc by blast
      qed
      have nb: "norm (?M *v (y - x) + \<eta>) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
      proof -
        have t1: "norm (?M *v (y - x) + \<eta>) \<le> norm (?M *v (y - x)) + norm \<eta>"
          by (rule norm_triangle_ineq)
        have t2: "norm (?M *v (y - x)) \<le> N * norm (y - x)"
          unfolding N_def by (rule onorm[OF bl])
        have t3: "N * norm (y - x) \<le> N * (norm \<eta> / (\<epsilon> / 4))"
          by (rule mult_left_mono[OF cl N0])
        have t4: "N * (norm \<eta> / (\<epsilon> / 4)) = (4 * N / \<epsilon>) * norm \<eta>"
          using e0 by (simp add: field_simps)
        have t5: "(4 * N / \<epsilon>) * norm \<eta> + norm \<eta> = (4 * N / \<epsilon> + 1) * norm \<eta>"
          by (simp add: field_simps)
        have t6: "(4 * N / \<epsilon> + 1) * norm \<eta> \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
          by (rule mult_left_mono[OF _ Cpos]) (use hn in linarith)
        show ?thesis using t1 t2 t3 t4 t5 t6 by linarith
      qed
      show ?thesis using ge nb by blast
    qed
    obtain ps :: "nat \<Rightarrow> real^'n" where
      psge: "\<And>j. 1 \<le> ell_op k L (ps j) ?M"
      and psn: "\<And>j. norm (ps j) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
      using ex by metis
    have dslim: "\<delta>s \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F j in sequentially. (0 :: real) \<le> \<delta>s j"
        using ds0 by (simp add: less_imp_le)
      show "\<forall>\<^sub>F j in sequentially. \<delta>s j \<le> 1 / real (Suc j)"
        unfolding \<delta>s_def by simp
      show "((\<lambda>j. 0 :: real) \<longlongrightarrow> 0) sequentially" by simp
      show "((\<lambda>j :: nat. 1 / real (Suc j)) \<longlongrightarrow> 0) sequentially"
        using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
    qed
    have d1: "(\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlonglongrightarrow> (4 * N / \<epsilon> + 1) * 0"
        by (intro tendsto_mult tendsto_const dslim)
      then show ?thesis by simp
    qed
    have d2: "(\<lambda>j. norm (ps j)) \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F j in sequentially. (0 :: real) \<le> norm (ps j)" by simp
      show "\<forall>\<^sub>F j in sequentially. norm (ps j) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
        using psn by simp
      show "((\<lambda>j. 0 :: real) \<longlongrightarrow> 0) sequentially" by simp
      show "((\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlongrightarrow> 0) sequentially" by (rule d1)
    qed
    have plim: "ps \<longlonglongrightarrow> 0" using d2 by (simp add: tendsto_norm_zero_iff)
    have lim: "(\<lambda>j. (ps j, ?M)) \<longlonglongrightarrow> (0, ?M)"
      by (intro tendsto_Pair plim tendsto_const)
    have gew: "1 \<le> ell_op_usc k L (ps j) ?M" for j
    proof -
      have "(1 :: ereal) \<le> ereal (ell_op k L (ps j) ?M)"
        using psge[of j] by simp
      also have "\<dots> \<le> ell_op_usc k L (ps j) ?M"
        by (rule ell_op_le_ell_op_usc)
      finally show ?thesis .
    qed
    show ?thesis by (rule ell_op_usc_ge_one_limit[OF gew lim])
  next
    case False
    then obtain j where nj: "\<not> good (\<delta>s j)" by blast
    have h0: "0 < \<delta>s j" by (rule ds0)
    have hle: "\<delta>s j \<le> (\<epsilon> / 4) * \<rho>" unfolding \<delta>s_def by simp
    show ?thesis
    proof (cases "invertible ?M")
      case False
      \<comment> \<open>a singular \<open>?M\<close> yields tilts whose gradient never vanishes\<close>
      obtain \<eta> :: "real^'n" where hn: "norm \<eta> < \<delta>s j"
        and nz: "\<And>z :: real^'n. ?M *v z + \<eta> \<noteq> 0"
      proof (rule singular_matrix_avoids_range[OF False h0])
        fix ee :: "real^'n"
        assume b1: "norm ee < \<delta>s j" and b2: "\<And>z :: real^'n. ?M *v z + ee \<noteq> 0"
        show thesis by (rule that[OF b1 b2])
      qed
      have hlt: "norm \<eta> < (\<epsilon> / 4) * \<rho>" using hn hle by linarith
      obtain y :: "real^'n" where dxy: "dist x y < \<rho>"
        and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
        and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
          ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      proof (rule tilted_local_touching[OF lscW rho c0 sep hlt])
        fix yy :: "real^'n"
        assume b1: "dist x yy < \<rho>" and b2: "norm (yy - x) \<le> norm \<eta> / (\<epsilon> / 4)"
          and b3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
            ?W yy - (((yy - x) \<bullet> (?M *v (yy - x))) / 2 + \<eta> \<bullet> (yy - x))
              \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        show thesis by (rule that[OF b1 b2 b3])
      qed
      have gd: "good (\<delta>s j)"
        unfolding good_def using hn dxy cl loc nz[of "y - x"] by blast
      show ?thesis using gd nj by simp
    next
      case True
      \<comment> \<open>the second horn: \<open>v\<^sub>*\<close> would be locally constant\<close>
      have hornB: "?M *v (y - x) + \<eta> = 0"
        if hn: "norm \<eta> < \<delta>s j" and dxy: "dist x y < \<rho>"
          and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
          and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
            ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
              \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        for \<eta> y :: "real^'n"
      proof (rule ccontr)
        assume "?M *v (y - x) + \<eta> \<noteq> 0"
        then have "good (\<delta>s j)"
          unfolding good_def using hn dxy cl loc by blast
        then show False using nj by simp
      qed
      obtain rr where rr0: "0 < rr"
        and rc: "\<And>y. dist x y < rr \<Longrightarrow> ?W y = ?W x"
      proof (rule horn_B_locally_constant[OF lscW symM True rho c0 h0 hle sep
              hornB])
        fix r' :: real
        assume b1: "0 < r'" and b2: "\<And>y. dist x y < r' \<Longrightarrow> ?W y = ?W x"
        show thesis by (rule that[OF b1 b2])
      qed
      define r2 where "r2 = min (rr / 2) (\<rho> / 2)"
      have r20: "0 < r2" unfolding r2_def using rr0 rho by simp
      have r2K: "cball x r2 \<subseteq> K"
      proof -
        have "cball x r2 \<subseteq> cball x \<rho>"
          unfolding r2_def using rho by auto
        then show ?thesis using subK interior_subset by blast
      qed
      have contra: False
      proof (rule exit_val_not_locally_constant[OF T0 L1' k1 kn Kc refl r20 r2K])
        show "?W x < T / 2" by (rule cap)
      next
        fix y :: "real^'n" assume dy: "dist x y < r2"
        have "r2 \<le> rr / 2" unfolding r2_def by simp
        then have "dist x y < rr" using dy rr0 by linarith
        then show "?W y = ?W x" by (rule rc)
      qed
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>Case 2, and the supersolution property\<close>

text \<open>Letting \<open>\<epsilon> \<rightarrow> 0\<close> along \<open>1/(j+1)\<close> moves the Hessian back to \<open>H\<close>,
  and one more application of \<open>ell_op_usc_ge_one_limit\<close> --- this time in
  the matrix argument rather than the gradient --- finishes Case 2.\<close>

theorem exit_val_case2:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
    and cap: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
  shows "1 \<le> ell_op_usc k L 0 H"
proof -
  define es where "es = (\<lambda>j :: nat. 1 / real (Suc j))"
  have es0: "0 < es j" for j unfolding es_def by simp
  have eslim: "es \<longlonglongrightarrow> 0"
    unfolding es_def using LIMSEQ_inverse_real_of_nat
    by (simp add: divide_inverse)
  have ge: "1 \<le> ell_op_usc k L 0 (H - es j *\<^sub>R mat 1)" for j
    by (rule exit_val_case2_eps[OF T0 L1 k1 kn Kc xi tf gx0 rho0 tmin cap es0])
  have lim: "(\<lambda>j. (0 :: real^'n, H - es j *\<^sub>R mat 1)) \<longlonglongrightarrow> (0, H)"
  proof -
    have "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0 *\<^sub>R mat 1"
      by (rule tendsto_scaleR[OF eslim tendsto_const])
    then have z: "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0" by simp
    have "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H - 0"
      by (rule tendsto_diff[OF tendsto_const z])
    then have m: "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H" by simp
    show ?thesis by (rule tendsto_Pair[OF tendsto_const m])
  qed
  show ?thesis by (rule ell_op_usc_ge_one_limit[OF ge lim])
qed

text \<open>Definition 3.1(b) for the paper's own value function.  Case 1
  (\<open>\<nabla>\<phi>(x) \<noteq> 0\<close>) is the skew-trick contradiction, lifted from
  \<open>ell_op\<close> to \<open>ell_op_usc\<close>; Case 2 (\<open>\<nabla>\<phi>(x) = 0\<close>) is the dichotomy
  above.  A global touching over \<open>K\<close> is in particular a local one, which
  is all either case consumes.

  The hypothesis \<open>cap\<close> says the horizon never binds on the interior.  It
  is needed only by Case 2 --- Case 1 derives it from the nonvanishing
  gradient --- and it is faithful to the paper, which has no horizon at
  all.  For a bounded \<open>K\<close> it follows from
  @{thm [source] exit_val_le_ball_bound}.\<close>

theorem exit_val_supersol_lsc:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and cap: "\<And>x :: real^'n. x \<in> interior K \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
  shows "visc_supersol_lsc k L K (interior K)
      (\<lambda>u. enn2real (exit_val k L T K u))"
  unfolding visc_supersol_lsc_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<forall>y\<in>K. lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
  have loc: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
    if yK: "y \<in> K" and dy: "dist x y < 1" for y
    using tmin yK by blast
  show "1 \<le> ell_op_usc k L (g x) H"
  proof (cases "g x = 0")
    case False
    have plain: "1 \<le> ell_op k L (g x) H"
    proof (rule ccontr)
      assume "\<not> 1 \<le> ell_op k L (g x) H"
      then have flt: "ell_op k L (g x) H < 1" by simp
      show False
        by (rule exit_val_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc xi
              tf zero_less_one loc False flt])
    qed
    have "(1 :: ereal) \<le> ereal (ell_op k L (g x) H)" using plain by simp
    also have "\<dots> \<le> ell_op_usc k L (g x) H" by (rule ell_op_le_ell_op_usc)
    finally show ?thesis .
  next
    case True
    have "1 \<le> ell_op_usc k L 0 H"
      by (rule exit_val_case2[OF T0 L1 k1 kn Kc xi tf True zero_less_one loc
            cap[OF xi]])
    then show ?thesis unfolding True .
  qed
qed

subsection \<open>The same inequality for the envelope taken within \<open>K\<close>\<close>

text \<open>The touching in @{thm [source] exit_val_supersol_lsc} is global over \<open>K\<close>
  but its proof only ever uses it near the touching point, so the local form
  is the one actually proved; and once it is stated locally the paper's
  envelope @{const lsc_envK} follows at once, since the two envelopes agree at
  interior points and a small enough ball around an interior point meets \<open>K\<close>
  only in interior points.\<close>

theorem exit_val_supersol_lsc_local:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and cap: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
    and xi: "x \<in> interior K" and tf: "test_fun_at \<phi> g H x" and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
  shows "1 \<le> ell_op_usc k L (g x) H"
proof (cases "g x = 0")
  case False
  have plain: "1 \<le> ell_op k L (g x) H"
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L (g x) H"
    then have flt: "ell_op k L (g x) H < 1" by simp
    show False
      by (rule exit_val_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc xi
            tf rho0 tmin False flt])
  qed
  have "(1 :: ereal) \<le> ereal (ell_op k L (g x) H)" using plain by simp
  also have "\<dots> \<le> ell_op_usc k L (g x) H" by (rule ell_op_le_ell_op_usc)
  finally show ?thesis .
next
  case True
  have "1 \<le> ell_op_usc k L 0 H"
    by (rule exit_val_case2[OF T0 L1 k1 kn Kc xi tf True rho0 tmin cap])
  then show ?thesis unfolding True .
qed

theorem exit_val_supersol_envK:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and cap: "\<And>x :: real^'n. x \<in> interior K \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
  shows "visc_supersol_env k L K (interior K)
      (lsc_envK K (\<lambda>u. enn2real (exit_val k L T K u)))"
  unfolding visc_supersol_env_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<forall>y\<in>K. lsc_envK K (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
      \<le> lsc_envK K (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
  have v0: "(0 :: real) \<le> enn2real (exit_val k L T K y)" for y by simp
  obtain \<rho> where rho0: "0 < \<rho>" and rsub: "ball x \<rho> \<subseteq> interior K"
    using openE[OF open_interior xi] by blast
  have eqI: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y
      = lsc_envK K (\<lambda>u. enn2real (exit_val k L T K u)) y"
    if "y \<in> interior K" for y
    by (rule lsc_env_eq_on_interior[OF v0 that])
  have loc: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x - \<phi> x
      \<le> lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) y - \<phi> y"
    if yK: "y \<in> K" and dy: "dist x y < \<rho>" for y
  proof -
    have "y \<in> interior K" using rsub dy by auto
    then show ?thesis using tmin yK eqI[OF xi] eqI[of y] by simp
  qed
  show "1 \<le> ell_op_usc k L (g x) H"
    by (rule exit_val_supersol_lsc_local[OF T0 L1 k1 kn Kc cap[OF xi] xi tf
          rho0 loc])
qed

subsection \<open>Discharging the horizon hypothesis\<close>

text \<open>@{thm [source] exit_val_supersol_lsc} carries the assumption that the
  horizon never binds on the interior.  For a bounded \<open>K\<close> that is not an
  assumption at all but a consequence of choosing \<open>T\<close> large enough:
  @{thm [source] exit_val_le_ball_bound} caps the value at
  \<open>(r\<^sup>2 - \<bar>x\<bar>\<^sup>2)/(n - k)\<close>, so \<open>T > 2r\<^sup>2/(n - k)\<close> already forces
  \<open>v\<^sub>* < T/2\<close> everywhere.  This is the paper's own setting: it has no
  horizon, and the cap here is a device of this formalisation.\<close>

lemma exit_val_cap_inert:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes kn: "k < CARD('n)" and L0: "0 \<le> L" and T0: "0 \<le> T"
    and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
proof -
  have tv0: "\<And>u. 0 \<le> enn2real (exit_val k L T K u)" by simp
  have nk0: "0 < real (CARD('n) - k)" using kn by simp
  define A where "A = rK * rK / real (CARD('n) - k)"
  have A0: "0 \<le> A" unfolding A_def using nk0 by simp
  have AT: "2 * A < T"
  proof -
    have "2 * A = 2 * (rK * rK) / real (CARD('n) - k)"
      unfolding A_def by simp
    then show ?thesis using Tbig by simp
  qed
  have b: "exit_val k L T K x
      \<le> ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k))"
    by (rule exit_val_le_ball_bound[OF kn T0 L0 KB])
  have le1: "(rK * rK - x \<bullet> x) / real (CARD('n) - k) \<le> A"
    unfolding A_def
  proof (rule divide_right_mono)
    show "rK * rK - x \<bullet> x \<le> rK * rK" using inner_ge_zero[of x] by linarith
    show "0 \<le> real (CARD('n) - k)" using nk0 by linarith
  qed
  have b': "exit_val k L T K x \<le> ennreal A"
  proof -
    have "ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)) \<le> ennreal A"
      by (rule ennreal_leI[OF le1])
    with b show ?thesis by (rule order_trans)
  qed
  have le2: "enn2real (exit_val k L T K x) \<le> A"
  proof -
    have "enn2real (exit_val k L T K x) \<le> enn2real (ennreal A)"
      by (rule enn2real_mono[OF b' ennreal_less_top])
    then show ?thesis using enn2real_ennreal[OF A0] by simp
  qed
  have le3: "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x
      \<le> enn2real (exit_val k L T K x)"
    by (rule lsc_env_le_self[OF tv0])
  show ?thesis using le2 le3 AT by linarith
qed

text \<open>So on a bounded \<open>K\<close> the supersolution property is unconditional.\<close>

corollary exit_val_supersol_lsc_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "visc_supersol_lsc k L K (interior K)
      (\<lambda>u. enn2real (exit_val k L T K u))"
proof (rule exit_val_supersol_lsc[OF T0 L1 k1 kn Kc])
  fix x :: "real^'n" assume "x \<in> interior K"
  show "lsc_env (\<lambda>u. enn2real (exit_val k L T K u)) x < T / 2"
    by (rule exit_val_cap_inert[OF kn _ _ KB Tbig]) (use L1 T0 in linarith)+
qed


(*<*)
end
(*>*)
