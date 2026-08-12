section \<open>Theorem 1.1: the assembly point\<close>

text \<open>
  The join of the development (STATUS.md, task 28). Theorem 1.1 of
  arXiv:2512.17702 asserts that the value function \<open>v\<close> of Eq. (1.6) is the
  unique upper semicontinuous viscosity solution of Eq. (1.9)--(1.10) with
  zero boundary values. Its full proof requires Section 2 (Lemmas 2.2/2.3 and
  Proposition 2.4, task 25), Section 4's uniqueness (task 26) and Section 5's
  continuity (task 27). This theory collects the parts provable TODAY, for
  the ball \<open>K = cball 0 r\<close> where Section 4 is unconditional:

  \<^item> the value-function upper bound \<open>v \<le> ball_v\<close> everywhere (the \<open>\<le>\<close> half of
    the identification of \<open>v\<close>, via Example 3.1's optimal-boundary analysis);
  \<^item> the boundary identification \<open>v = ball_v = 0\<close> on the sphere;
  \<^item> the uniqueness clause: ANY continuous viscosity solution with \<open>ball_v\<close>'s
    boundary data coincides with \<open>ball_v\<close> on the ball — so once the DPP
    machinery of task 25 delivers that \<open>v\<close> is a viscosity solution with the
    right boundary data and the matching lower bound, Theorem 1.1 for the
    ball follows by instantiating the third clause at \<open>u = v\<close>.

  What is missing, and where it comes from: upper semicontinuity of \<open>v\<close> and
  the viscosity property (Prop 2.4 via Lemmas 2.2/2.3); the lower bound
  \<open>ball_v \<le> v\<close> at interior points (the martingale construction of
  Section 3.1, which needs weak existence for Eq. (3.11)); and general
  compact \<open>K\<close> (Theorem 4.2(a), behind Crandall--Ishii).

  STATUS OF THE THIRD ITEM (2026-07-31). \<open>Comparison_Assembly\<close> is now imported,
  and it carries the Crandall--Ishii development: Rademacher, Alexandrov,
  Jensen's lemma, the theorem on sums, the envelope calculus, and the closing
  chain of Theorem 4.2(a). Its endpoint is
  \<open>comparison_supconv_sequence_complete\<close>, which derives \<open>False\<close> from the two
  viscosity properties together with a SEQUENCE of Jensen applications: for
  each index, a doubled maximiser, its Alexandrov jet, and the point at which
  each sup-convolution is attained, plus convergence of the four resulting
  sequences and \<open>p \<noteq> 0\<close> at the limit.

  What still blocks general \<open>K\<close> is therefore not the Crandall--Ishii analysis
  but the CONSTRUCTION that feeds it: producing that sequence from the doubling
  of \<open>\<theta> u\<close> against \<open>w\<close> on \<open>K \<times> K\<close>, with a shrinking Jensen tilt. The
  existence ingredients for it are proved (\<open>doubling_maximiser_exists\<close>,
  \<open>doubling_complete\<close>, \<open>doubled_supconv_jet_exists\<close>); what is not written is
  their instantiation as a single indexed family.

  NOTE on imports: Value\_Function (probabilistic chain) and
  Relative\_Arbitrage\_Comparison (Envelopes chain) share draft ancestors, so
  this theory is BATCH-ONLY, like Path\_Tightness\_Market. (Adding
  \<open>Comparison_Assembly\<close> as a third import does NOT change that: it builds
  green. Note also that the analogous "batch-only" claim once recorded for
  \<open>Comparison_Assembly\<close> itself was simply WRONG -- PIDE holds that theory
  fine -- so this note should be re-tested rather than trusted.)
\<close>

theory Theorem_1_1
  imports Value_Function Relative_Arbitrage_Comparison Comparison_Assembly
    Section_2_Usc Deterministic_Radius_Market Paper_Viscosity
begin

theorem theorem_1_1_ball_fragment:
  fixes x0 :: "real^'n::finite" and u :: "real^'n \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
  shows "val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
    and "norm x0 = r \<Longrightarrow> val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
    and "continuous_on (cball 0 r) u \<Longrightarrow>
         visc_sol k L (ball (0::real^'n) r) u \<Longrightarrow>
         (\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r \<Longrightarrow>
            u y = ball_v r k y) \<Longrightarrow>
         x0 \<in> ball (0::real^'n) r \<Longrightarrow> u x0 = ball_v r k x0"
proof -
  show "val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
    by (rule val_fn_le_ball_v)
  show "norm x0 = r \<Longrightarrow> val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
    by (rule val_fn_boundary)
  assume cu: "continuous_on (cball 0 r) u"
    and u: "visc_sol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r \<Longrightarrow>
        u y = ball_v r k y"
    and x0: "x0 \<in> ball (0::real^'n) r"
  have sub: "visc_subsol k L (ball (0::real^'n) r) u"
    and sup: "visc_supersol k L (ball (0::real^'n) r) u"
    using u by (auto simp: visc_sol_def)
  have le: "u x0 \<le> ball_v r k x0"
    by (rule visc_subsol_le_ball_v[OF k L r cu sub _ x0]) (simp add: bd)
  have ge: "ball_v r k x0 \<le> u x0"
    by (rule ball_v_le_visc_supersol[OF k L r cu sup _ x0]) (simp add: bd)
  from le ge show "u x0 = ball_v r k x0" by simp
qed

text \<open>UPDATE (2026-08-02).  Blocker (iii) above --- "general compact \<open>K\<close>,
  behind Crandall--Ishii" --- is GONE.  Theorem 4.2(a) is proved, as
  \<open>max_principle_boundary_holds\<close> in Comparison\_Assembly:

    \<open>compact K \<Longrightarrow> K \<noteq> {} \<Longrightarrow> 1 \<le> k \<Longrightarrow> k < CARD('n) \<Longrightarrow> 1 \<le> L
       \<Longrightarrow> max_principle_boundary k L K\<close>

  so the uniqueness clause is no longer tied to the ball.  The third clause of
  \<open>theorem_1_1_ball_fragment\<close> above reaches \<open>u = ball_v\<close> through Example 3.1's
  explicit optimal-boundary formula; the theorem below reaches uniqueness for an
  arbitrary compact \<open>K\<close> through comparison instead, and needs no formula at all.

  What still blocks the FULL Theorem 1.1 is unchanged, and is not PDE work:

  \<^item> upper semicontinuity of \<open>v\<close> and the viscosity property (Prop 2.4 via
    Lemmas 2.2/2.3);
  \<^item> the lower bound \<open>ball_v \<le> v\<close> at interior points --- the Section 3.1
    martingale construction, which needs weak existence for Eq. (3.11).

  Both are stochastic analysis, not comparison.\<close>

section \<open>Theorem 1.1: exactly which clauses are proved\<close>

text \<open>Theorem 1.1 asserts that \<open>v\<close> of Eq. (1.6) is the unique upper
  semicontinuous viscosity solution with zero boundary values.  In this
  development's vocabulary, with \<open>v = enn2real \<circ> val_fn k L K\<close>, it has five
  clauses.  Status as of 2026-08-02:

  \<^item> (0) FINITENESS, \<open>val_fn k L K x < \<top>\<close> --- PROVED for every bounded \<open>K\<close>:
    \<open>val_fn_finite_bounded\<close> (Value\_Function).
  \<^item> (1) REGULARITY (the paper's usc; this development has no usc predicate and
    uses continuity) --- OPEN.
  \<^item> (2) \<open>visc_sol k L (interior K) v\<close>, Eq. (1.9) --- OPEN.
  \<^item> (3) ZERO BOUNDARY VALUES, Eq. (1.10) --- PROVED for \<open>K = cball 0 r\<close>:
    \<open>val_fn_zero_on_frontier_ball\<close> (Value\_Function).  OPEN for general \<open>K\<close>,
    where it is Lemma 5.3 of the paper.
  \<^item> (4) UNIQUENESS --- PROVED for every compact \<open>K\<close>:
    \<open>theorem_1_1_uniqueness_general\<close> below, via Theorem 4.2(a).

  WHAT BLOCKS (1), (2) AND (3)-for-general-\<open>K\<close>, and why it is not a matter of
  assembly.  All three reduce to two things the paper does not supply:

  \<^item> Proposition 2.4 --- which gives usc of \<open>v\<close>, the dynamic programming
    principle AND attainment of the supremum --- has NO proof in the paper.  Its
    entire proof is the sentence "It suffices to repeat [larsson\_minimum\_2022,
    proofs of Proposition 2.2(ii), (iii)] word by word."  Discharging it without
    assumption needs a universally measurable selection theorem over analytic
    sets and a Skorokhod representation on \<open>C([0,\<infinity>))\<close>, NEITHER of which exists
    in Isabelle/HOL, the AFP, or this repository.
  \<^item> Example 3.1's lower bound \<open>ball_v \<le> v\<close> needs a global weak solution of
    Eq. (3.11) --- a bounded, continuous, DEGENERATE, NON-LIPSCHITZ SDE on the
    punctured space --- for which the paper cites no theorem by name.

  Note the second point means even "Theorem 1.1 for the ball" is out of reach:
  the \<open>\<le>\<close> half (\<open>val_fn_le_ball_v\<close>) has always been available; it is the \<open>\<ge>\<close>
  half that is missing, and it is missing structurally.\<close>

section \<open>A SECOND refutable interface, found by scoping Theorem 1.1\<close>

text \<open>\<open>comparison_principle\<close> (Relative\_Arbitrage\_Uniqueness) axiomatises
  comparison with NO continuity hypothesis on \<open>u\<close> and \<open>w\<close>.  That is the same
  defect the project already found and repaired in \<open>max_principle_boundary_raw\<close>,
  and it is fatal for the same reason: \<open>visc_subsol\<close>/\<open>visc_supersol\<close> are LOCAL
  conditions on \<open>\<Omega>\<close>, so the values of a sub- or supersolution OUTSIDE \<open>\<Omega>\<close> are
  completely unconstrained and can be moved to violate any boundary comparison.

  Concretely: take \<open>u = ball_v + 1\<close> (a subsolution, since adding a constant
  changes neither gradient nor Hessian of a test function) and \<open>w'\<close> equal to
  \<open>ball_v\<close> INSIDE the ball and to \<open>ball_v + 1\<close> outside.  \<open>visc_supersol_cong_on\<close>
  keeps \<open>w'\<close> a supersolution because it agrees with \<open>ball_v\<close> on the open ball;
  on \<open>closure (ball 0 r) - ball 0 r\<close> the two functions are EQUAL, so the
  locale's boundary hypothesis holds; and the locale then forces
  \<open>ball_v + 1 \<le> ball_v\<close> at the centre.

  CONSEQUENCE: \<open>ball_v_unique_solution\<close> (Relative\_Arbitrage\_Uniqueness:499),
  which carries \<open>comparison_principle k L (ball 0 r)\<close> as a hypothesis, is
  VACUOUS for every \<open>r > 0\<close>.  It should be restated against
  \<open>comparison_compact\<close> or \<open>viscosity_uniqueness_compact\<close>, both of which are now
  unconditional --- \<open>theorem_1_1_uniqueness_general\<close> below is the replacement.\<close>

lemma visc_subsol_shift:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_subsol k L \<Omega> u"
  shows "visc_subsol k L \<Omega> (\<lambda>y. u y + c)"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. (u y + c) - \<phi> y \<le> (u x + c) - \<phi> x"
  from lm have "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x" by auto
  with s x tf show "ell_op k L (g x) H \<le> 1"
    unfolding visc_subsol_def by blast
qed

theorem comparison_principle_refuted:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L" and r: "0 < r"
  shows "\<not> comparison_principle k L (ball (0::real^'n) r)"
proof
  assume cp: "comparison_principle k L (ball (0::real^'n) r)"
  have vs: "visc_sol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
    by (rule ball_v_visc_sol_exists(2)[OF k L])
  have subv: "visc_subsol k L (ball (0::real^'n) r) (ball_v r k)"
    and supv: "visc_supersol k L (ball (0::real^'n) r) (ball_v r k)"
    using vs by (auto simp: visc_sol_def)
  \<comment> \<open>the raised subsolution\<close>
  have subu: "visc_subsol k L (ball (0::real^'n) r) (\<lambda>y. ball_v r k y + 1)"
    by (rule visc_subsol_shift[OF subv])
  \<comment> \<open>the supersolution altered only OUTSIDE the ball\<close>
  define w' :: "real^'n \<Rightarrow> real" where
    "w' = (\<lambda>y. if y \<in> ball (0::real^'n) r then ball_v r k y else ball_v r k y + 1)"
  have eqw: "w' y = ball_v r k y" if "y \<in> ball (0::real^'n) r" for y
    unfolding w'_def using that by simp
  have supw: "visc_supersol k L (ball (0::real^'n) r) w'"
    by (rule visc_supersol_cong_on[OF supv open_ball eqw])
  \<comment> \<open>on the boundary the two agree, so the locale's hypothesis holds\<close>
  have bdy: "\<forall>y \<in> closure (ball (0::real^'n) r) - ball (0::real^'n) r.
      ball_v r k y + 1 \<le> w' y"
  proof
    fix y assume y: "y \<in> closure (ball (0::real^'n) r) - ball (0::real^'n) r"
    have "y \<notin> ball (0::real^'n) r" using y by simp
    then show "ball_v r k y + 1 \<le> w' y" unfolding w'_def by simp
  qed
  have zin: "(0::real^'n) \<in> ball (0::real^'n) r" using r by simp
  \<comment> \<open>and the locale then forces an absurdity at the centre\<close>
  have lt: "ball_v r k (0::real^'n) + 1 \<le> w' 0"
    by (rule comparison_principle.comparison[OF cp subu supw bdy zin])
  have eq0: "w' (0::real^'n) = ball_v r k (0::real^'n)"
    unfolding w'_def by (rule if_P[OF zin])
  from lt[unfolded eq0] show False by simp
qed

theorem theorem_1_1_uniqueness_general:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and subu: "visc_subsol_env k L K (interior K) u"
    and supu: "visc_supersol_env k L K (interior K) u"
    and subw: "visc_subsol_env k L K (interior K) w"
    and supw: "visc_supersol_env k L K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
    and x: "x \<in> K"
  shows "u x = w x"
  by (rule viscosity_uniqueness_compact
      [OF cK neK k(1) k(2) L cu cw subu supu subw supw bd x])

section \<open>Example 3.1 realises the ball value exactly (clause (3), n − k = 1)\<close>

lemma ess_inf_time_const:
  assumes M: "prob_space M"
  shows "ess_inf_time M (\<lambda>_. c) = ennreal c"
proof (rule antisym)
  show "ess_inf_time M (\<lambda>_. c) \<le> ennreal c"
    by (rule ess_inf_time_le_const[OF M]) simp
  have "AE \<omega> in M. ennreal c \<le> ennreal c" by simp
  then show "ennreal c \<le> ess_inf_time M (\<lambda>_. c)"
    unfolding ess_inf_time_def by (intro Sup_upper) simp
qed

theorem deterministic_radius_stopped_market:
  fixes q \<phi> r L :: real
  assumes q: "0 < q" and L: "1 \<le> L" and qr: "q \<le> r\<^sup>2" and r0: "0 \<le> r"
  shows "stopped_market 1 L (cball 0 r)
      (sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>))
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      (drXs q \<phi> (r\<^sup>2 - q)) (dras q \<phi> (r\<^sup>2 - q)) (\<lambda>_. r\<^sup>2 - q)"
  unfolding stopped_market_def
proof (intro conjI)
  show "sufficiently_volatile_market
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      (drXs q \<phi> (r\<^sup>2 - q)) (dras q \<phi> (r\<^sup>2 - q)) 1 L (cball 0 r)
      (sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>))
      (\<lambda>_. r\<^sup>2 - q)"
    by (rule deterministic_radius_sufficiently_volatile[OF assms])
  show "\<forall>s \<omega>. \<omega> \<in> space (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) \<longrightarrow>
      drXs q \<phi> (r\<^sup>2 - q) s \<omega> = drXs q \<phi> (r\<^sup>2 - q) (min s (r\<^sup>2 - q)) \<omega>"
    using drXs_stopped by blast
  show "\<forall>s \<omega>. \<omega> \<in> space (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) \<longrightarrow>
      r\<^sup>2 - q < s \<longrightarrow> dras q \<phi> (r\<^sup>2 - q) s \<omega> = 0"
    using dras_killed by blast
  have T0: "0 \<le> r\<^sup>2 - q" using qr by simp
  show "AE \<omega> in (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure). \<forall>l t. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. dras q \<phi> (r\<^sup>2 - q) s \<omega> $ l $ l)"
    by (intro AE_I2 allI impI dras_diag_time_integrable[OF q T0])
qed

theorem stopped_val_fn_ball_eq_2d:
  fixes x :: "real^2" and r L :: real
  assumes L: "1 \<le> L" and x0: "0 < norm x" and xr: "norm x \<le> r"
  shows "stopped_val_fn 1 L (cball 0 r) x = ennreal (ball_v r 1 x)"
proof (rule antisym)
  show "stopped_val_fn 1 L (cball 0 r) x \<le> ennreal (ball_v r 1 x)"
    by (rule stopped_val_fn_le_ball_v)
  define q where "q = x \<bullet> x"
  have xne: "x \<noteq> 0" using x0 by auto
  have qpos: "0 < q" unfolding q_def using xne
    by (simp add: inner_gt_zero_iff)
  have nsq: "(norm x)\<^sup>2 = q"
    unfolding q_def by (simp add: power2_norm_eq_inner)
  have qr: "q \<le> r\<^sup>2"
    using power_mono[OF xr norm_ge_zero, of 2] nsq by simp
  have r0: "0 \<le> r" using x0 xr by linarith
  have sqn: "sqrt q = norm x"
    using nsq by (metis norm_ge_zero real_sqrt_abs real_sqrt_pow2_iff
        real_sqrt_power)
  have unit: "(x $ 1 / norm x)\<^sup>2 + (x $ 2 / norm x)\<^sup>2 = 1"
  proof -
    have "x \<bullet> x = x $ 1 * x $ 1 + x $ 2 * x $ 2"
      by (simp add: inner_vec_def UNIV_2)
    then have "(x $ 1)\<^sup>2 + (x $ 2)\<^sup>2 = q"
      unfolding q_def by (simp add: power2_eq_square)
    then show ?thesis
      using qpos nsq
      by (simp add: power_divide add_divide_distrib [symmetric])
  qed
  obtain \<phi> where \<phi>1: "x $ 1 / norm x = cos \<phi>"
    and \<phi>2: "x $ 2 / norm x = sin \<phi>"
    by (rule sincos_total_2pi[OF unit]) blast
  have xrep: "x = sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)"
  proof -
    have c1: "x $ 1 = norm x * cos \<phi>"
      using \<phi>1 x0 by (simp add: field_simps)
    have c2: "x $ 2 = norm x * sin \<phi>"
      using \<phi>2 x0 by (simp add: field_simps)
    have comp: "x $ i
        = (sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)) $ i"
      for i
      using exhaust_2[of i] c1 c2 sqn by auto
    show ?thesis
      by (rule vec_eq_iff[THEN iffD2]) (simp add: comp)
  qed
  have SM: "stopped_market 1 L (cball 0 r) x
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      (drXs q \<phi> (r\<^sup>2 - q)) (dras q \<phi> (r\<^sup>2 - q)) (\<lambda>_. r\<^sup>2 - q)"
    using deterministic_radius_stopped_market[OF qpos L qr r0, of \<phi>]
    unfolding xrep[symmetric] .
  have EI: "ess_inf_time (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>_. r\<^sup>2 - q) = ennreal (r\<^sup>2 - q)"
    by (rule ess_inf_time_const) simp
  have mem: "ennreal (r\<^sup>2 - q) \<in> stopped_exit_vals 1 L (cball 0 r) x"
    unfolding stopped_exit_vals_def
  proof (intro CollectI)
    show "\<exists>M F X acov tau.
        stopped_market 1 L (cball 0 r) x M F X acov tau
        \<and> ennreal (r\<^sup>2 - q) = ess_inf_time M tau"
      by (intro exI[where x = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"]
          exI[where x = "\<lambda>t. natural_filtration bm_paths 0
            (cbmX (0 :: real^2)) (drc q t)"]
          exI[where x = "drXs q \<phi> (r\<^sup>2 - q)"]
          exI[where x = "dras q \<phi> (r\<^sup>2 - q)"]
          exI[where x = "\<lambda>_ :: 2 \<Rightarrow> real \<Rightarrow> real. r\<^sup>2 - q"]
          conjI SM EI[symmetric])
  qed
  have bv: "ball_v r 1 x = r\<^sup>2 - q"
    unfolding ball_v_def q_def[symmetric]
    using qr by (simp add: max_absorb1)
  show "ennreal (ball_v r 1 x) \<le> stopped_val_fn 1 L (cball 0 r) x"
    unfolding stopped_val_fn_def bv
    by (rule Sup_upper[OF mem])
qed


section \<open>Clause (2) joined to uniqueness: \<open>paper_v\<close> IS the solution\<close>

text \<open>The two halves of clause (2) live in Paper\_Viscosity and the
  comparison principle in Comparison\_Assembly, and until now nothing saw
  both.  They meet here.

  Both halves land in the envelope forms that
  @{thm [source] viscosity_uniqueness_compact} now consumes ---
  @{thm [source] visc_subsol_imp_env} on the subsolution side, since the
  envelope-free notion proved for \<open>paper_v\<close> is the STRONGER one, and
  @{thm [source] visc_supersol_lsc_iff_env} on the supersolution side.
  The horizon hypothesis is discharged by
  @{thm [source] paper_v_cap_inert}, so the only thing assumed about
  \<open>paper_v\<close> is CONTINUITY on \<open>K\<close>.

  That continuity is the one genuine gap.  What is proved elsewhere in
  this development is that \<open>paper_v\<close> is upper semicontinuous; lower
  semicontinuity is not, and the paper's own Theorem 1.1 speaks of the
  unique UPPER SEMICONTINUOUS solution, so closing the gap properly means
  the paper's Theorem 4.3 (comparison with semicontinuous data), not
  this theorem.  Stated with continuity as a hypothesis, the assembly is
  honest and immediately usable the moment continuity is available.\<close>

theorem paper_v_unique_viscosity_solution:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 < L"
    and T0: "0 < T"
    and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
    and cv: "\<And>y. y \<in> K \<Longrightarrow>
      isCont (\<lambda>z. enn2real (paper_v k L T K z)) y"
    and cu: "continuous_on K u"
    and subu: "visc_subsol_env k L K (interior K) u"
    and supu: "visc_supersol_env k L K (interior K) u"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow>
      u y = enn2real (paper_v k L T K y)"
    and x: "x \<in> K"
  shows "u x = enn2real (paper_v k L T K x)"
proof -
  have L1': "1 \<le> L" using L1 by linarith
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  have tv0: "\<And>y. (0 :: real) \<le> enn2real (paper_v k L T K y)" by simp
  \<comment> \<open>continuity of the value function, in the two shapes needed\<close>
  have cw: "continuous_on K (\<lambda>z. enn2real (paper_v k L T K z))"
    by (rule continuous_at_imp_continuous_on) (use cv in blast)
  \<comment> \<open>clause (2), subsolution half --- the envelope-free form is stronger\<close>
  have sub0: "visc_subsol k L (interior K) (\<lambda>z. enn2real (paper_v k L T K z))"
    by (rule paper_v_visc_subsol[OF T0 L1' Kc kn])
  have subw: "visc_subsol_env k L K (interior K)
      (\<lambda>z. enn2real (paper_v k L T K z))"
    by (rule visc_subsol_imp_env[OF sub0 iK open_interior])
  \<comment> \<open>clause (2), supersolution half --- Definition 3.1(b), horizon discharged\<close>
  have sup0: "visc_supersol_lsc k L K (interior K)
      (\<lambda>z. enn2real (paper_v k L T K z))"
    by (rule paper_v_supersol_lsc_bounded[OF T0 L1 k1 kn Kc KB Tbig])
  have supw: "visc_supersol_env k L K (interior K)
      (\<lambda>z. enn2real (paper_v k L T K z))"
    using sup0 visc_supersol_lsc_iff_env[OF tv0 iK cv] by blast
  show ?thesis
    by (rule viscosity_uniqueness_compact[OF cK neK k1 kn L1' cu cw
          subu supu subw supw bd x])
qed


section \<open>P7: Theorem 1.1 assembled\<close>

text \<open>\<open>paper_v\<close> as a real-valued function: nonnegative, globally bounded, and
  upper semicontinuous in the \<open>\<epsilon>\<close>-form the comparison machinery consumes.\<close>

lemma paper_v_real_nonneg: "0 \<le> enn2real (paper_v k L T K x)"
  by simp

lemma paper_v_real_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
  shows "\<bar>enn2real (paper_v k L T K x)\<bar> \<le> rK * rK / real (CARD('n) - k)"
proof -
  have nk: "0 < real (CARD('n) - k)" using kn by simp
  have le: "paper_v k L T K x
      \<le> ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k))"
    by (rule paper_v_le_ball_bound[OF kn T0 L0 KB])
  have fin: "ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)) < \<top>"
    by simp
  have "enn2real (paper_v k L T K x)
      \<le> enn2real (ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)))"
    by (rule enn2real_mono[OF le fin])
  also have "\<dots> \<le> rK * rK / real (CARD('n) - k)"
  proof (cases "0 \<le> (rK * rK - x \<bullet> x) / real (CARD('n) - k)")
    case True
    then have "enn2real (ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)))
        = (rK * rK - x \<bullet> x) / real (CARD('n) - k)" by simp
    also have "\<dots> \<le> rK * rK / real (CARD('n) - k)"
      using nk inner_ge_zero[of x] by (simp add: divide_right_mono)
    finally show ?thesis .
  next
    case False
    then have "ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)) = 0"
      by (simp add: ennreal_neg)
    then show ?thesis using nk r0 by simp
  qed
  finally show ?thesis using paper_v_real_nonneg[of k L T K x] by simp
qed

lemma paper_v_real_usc:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)" and KB: "K \<subseteq> cball 0 rK"
    and lt: "enn2real (paper_v k L T K z) < cc"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (paper_v k L T K y) < cc"
proof -
  have L0: "0 \<le> L" using L by simp
  have T0: "0 \<le> T" using T by simp
  have cc0: "0 < cc" using lt paper_v_real_nonneg[of k L T K z] by linarith
  have fin: "paper_v k L T K y < \<top>" for y
  proof -
    have "paper_v k L T K y
        \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      by (rule paper_v_le_ball_bound[OF kn T0 L0 KB])
    also have "\<dots> < \<top>" by simp
    finally show ?thesis .
  qed
  have zlt: "paper_v k L T K z < ennreal cc"
    using lt fin[of z] by (simp add: enn2real_less_iff)
  have "eventually (\<lambda>y. paper_v k L T K y < ennreal cc) (nhds z)"
    by (rule paper_v_usc_unconditional[OF T L Kc zlt])
  then obtain U where opU: "open U" and zU: "z \<in> U"
    and Uy: "\<And>y. y \<in> U \<Longrightarrow> paper_v k L T K y < ennreal cc"
    unfolding eventually_nhds by blast
  obtain e where e0: "0 < e" and eU: "ball z e \<subseteq> U"
    using opU zU unfolding open_contains_ball by blast
  have "enn2real (paper_v k L T K y) < cc" if dy: "dist z y < e" for y
  proof -
    have "y \<in> U" using eU dy by auto
    then have "paper_v k L T K y < ennreal cc" by (rule Uy)
    then show ?thesis using fin[of y] cc0 by (simp add: enn2real_less_iff)
  qed
  then show ?thesis using e0 by blast
qed

text \<open>The supersolution clause of Definition 3.1 for \<open>paper_v\<close>, with the
  boundary gate included.  The gate is VACUOUS: \<open>paper_v \<ge> 0\<close>, hence so is its
  lower envelope, so \<open>{x. lsc_env v x < 0} = {}\<close> and the \<open>\<Omega>\<close> of Definition 3.1(b)
  collapses to \<open>interior K\<close>, which is what \<open>paper_v_supersol_lsc_bounded\<close>
  already gives.\<close>

theorem paper_v_supersol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
          lsc_env (\<lambda>z. enn2real (paper_v k L T K z)) x < 0})
      (lsc_env (\<lambda>z. enn2real (paper_v k L T K z)))"
proof -
  define v where "v = (\<lambda>z. enn2real (paper_v k L T K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by (rule paper_v_real_nonneg)
  have lsc0: "0 \<le> lsc_env v x" for x by (rule lsc_env_ge[OF v0])
  have gate: "interior K \<union> {x \<in> K - interior K. lsc_env v x < 0} = interior K"
  proof
    show "interior K \<union> {x \<in> K - interior K. lsc_env v x < 0} \<subseteq> interior K"
    proof
      fix y assume "y \<in> interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}"
      then consider "y \<in> interior K" | "lsc_env v y < 0" by auto
      then show "y \<in> interior K"
      proof cases
        case 1 then show ?thesis .
      next
        case 2
        have "0 \<le> lsc_env v y" by (rule lsc0)
        then have False using 2 by linarith
        then show ?thesis by simp
      qed
    qed
    show "interior K \<subseteq> interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}"
      by blast
  qed
  have "visc_supersol_lsc k L K (interior K) v"
    unfolding v_def
    by (rule paper_v_supersol_lsc_bounded[OF T0 L1 k1 kn Kc KB Tbig])
  then have "visc_supersol_env k L K (interior K) (lsc_env v)"
    unfolding visc_supersol_lsc_def visc_supersol_env_def by blast
  then show ?thesis unfolding v_def[symmetric] gate .
qed

text \<open>\<^bold>\<open>Theorem 1.1, uniqueness clause.\<close>  Every hypothesis about \<open>paper_v\<close> is
  now discharged: it is usc (\<open>paper_v_real_usc\<close>), nonnegative, globally
  bounded (\<open>paper_v_real_bounded\<close>), and satisfies BOTH clauses of
  Definition 3.1 with their boundary gates --- \<open>paper_v_subsol_bc\<close> (P6) and
  \<open>paper_v_supersol_bc\<close>.  The only thing the statement still rests on is
  \<open>comparison_two_domain\<close> (P4), the paper's Theorem 4.2(b), which is the sole
  admitted step in the development.\<close>

theorem theorem_1_1_uniqueness_faithful:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> rK * rK / real (CARD('n) - k)"
    and subu: "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and x: "x \<in> K"
  shows "u x = enn2real (paper_v k L T K x)"
proof -
  define v where "v = (\<lambda>z. enn2real (paper_v k L T K z))"
  define B where "B = rK * rK / real (CARD('n) - k)"
  have L0: "1 \<le> L" using L1 by simp
  have T0': "0 \<le> T" using T0 by simp
  have L0': "0 \<le> L" using L1 by simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have Bv: "\<bar>v y\<bar> \<le> B" for y
    unfolding v_def B_def by (rule paper_v_real_bounded[OF kn T0' L0' KB r0])
  have uscv: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c" if "v z < c" for c z
    using that unfolding v_def by (rule paper_v_real_usc[OF T0 L0 Kc kn KB])
  have supv: "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}) (lsc_env v)"
    unfolding v_def by (rule paper_v_supersol_bc[OF T0 L1 k1 kn Kc KB Tbig])
  have subv: "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def by (rule paper_v_subsol_bc[OF T0 L0 Kc kn])
  have "u x = v x"
    by (rule uniqueness_expandable
        [OF k1 kn L0 cK neK expK uscu uscv Bu[unfolded B_def[symmetric]] Bv
            subu supu subv supv x])
  then show ?thesis unfolding v_def by simp
qed

text \<open>\<^bold>\<open>What is left: exactly one thing.\<close>  \<open>comparison_two_domain\<close> (P4) in
  \<open>Comparison_Assembly\<close> --- the paper's Theorem 4.2(b) --- is the only admitted
  step in the whole development.  Discharging it makes Theorem 1.1 complete:
  \<open>paper_v\<close> is a bounded usc viscosity solution of \<open>F(\<nabla>v, \<nabla>\<^sup>2v) = 1\<close> on \<open>K\<close> with
  the zero boundary condition of Definition 3.1, and on an expandable \<open>K\<close> it is
  the only one.

  \<^bold>\<open>P6 was closed 2026-08-11\<close> (\<open>Paper_Viscosity.paper_v_subsol_bc\<close>), and the
  audit predicted in this note came out the easy way, though not for the
  reason predicted.  \<open>paper_v_visc_subsol\<close> turns out never to USE
  \<open>x \<in> interior K\<close> at all --- it is assumed and then ignored, since
  \<open>paper_v_touch_orth\<close> is indifferent to where \<open>x\<close> sits; hence
  \<open>paper_v_visc_subsol_any\<close> for an arbitrary \<open>\<Omega>\<close>.  What the gate actually buys
  is the upgrade from a touching that is global over \<open>K\<close> to a local one: off
  \<open>K\<close> the value is \<open>0\<close> (\<open>paper_v_zero_outside\<close>, because the exit time of a
  path starting outside \<open>K\<close> is \<open>0\<close>), while \<open>\<phi>\<close> is continuous, so for \<open>z\<close> near a
  boundary \<open>x\<close> with \<open>v x > 0\<close> the needed \<open>0 - \<phi> z \<le> v x - \<phi> x\<close> follows from
  \<open>\<phi> x - \<phi> z < v x\<close>.  No stochastic argument was involved.\<close>


section \<open>E4: Example 3.1 assembled from the interior lower bound\<close>

text \<open>PLAN \<open>\<section>2.2\<close>, package E4.  Everything of Example 3.1 EXCEPT the interior
  lower bound at nonzero points (which is E2--E3, the subspace-tangential
  field) is discharged here.  Four cases: outside the ball the value is \<open>0\<close>
  because a path starting outside \<open>K\<close> has exit time \<open>0\<close>
  (\<open>paper_v_zero_outside\<close>); on the sphere \<open>paper_v_boundary_zero\<close>; strictly
  inside and nonzero, the hypothesis against \<open>paper_v_le_ball_bound\<close>; and at
  the CENTRE by upper semicontinuity --- NOT by running the field from \<open>0\<close>,
  where the clamp sits.\<close>

lemma paper_v_ball_fin:
  fixes r :: real and y :: "real^'n::finite"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
  shows "paper_v k L T (cball 0 r) y < \<top>"
proof -
  have "paper_v k L T (cball 0 r) y
      \<le> ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k))"
    by (rule paper_v_le_ball_bound[OF kn T0 L0]) simp
  also have "\<dots> < \<top>" by simp
  finally show ?thesis .
qed

lemma paper_v_ball_upper:
  fixes r :: real and y :: "real^'n::finite"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
  shows "enn2real (paper_v k L T (cball 0 r) y)
      \<le> max ((r * r - y \<bullet> y) / real (CARD('n) - k)) 0"
proof -
  have le: "paper_v k L T (cball 0 r) y
      \<le> ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k))"
    by (rule paper_v_le_ball_bound[OF kn T0 L0]) simp
  have "enn2real (paper_v k L T (cball 0 r) y)
      \<le> enn2real (ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k)))"
    by (rule enn2real_mono[OF le]) simp
  also have "\<dots> \<le> max ((r * r - y \<bullet> y) / real (CARD('n) - k)) 0"
    by (cases "0 \<le> (r * r - y \<bullet> y) / real (CARD('n) - k)")
      (simp_all add: ennreal_neg)
  finally show ?thesis .
qed

theorem example_3_1_from_lower:
  fixes r :: real and x :: "real^'n::finite"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and T0: "0 < T" and r0: "0 < r"
    and lower: "\<And>y :: real^'n. norm y < r \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
        (r * r - y \<bullet> y) / real (CARD('n) - k)
          \<le> enn2real (paper_v k L T (cball 0 r) y)"
  shows "enn2real (paper_v k L T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof -
  have nk0: "0 < real (CARD('n) - k)" using kn by simp
  have L0: "0 \<le> L" using L1 by simp
  have T0': "0 \<le> T" using T0 by simp
  have Kc: "closed (cball (0 :: real^'n) r)" by simp
  have sq: "y \<bullet> y = norm y * norm y" for y :: "real^'n"
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  have upper: "enn2real (paper_v k L T (cball 0 r) y)
      \<le> max ((r * r - y \<bullet> y) / real (CARD('n) - k)) 0" for y :: "real^'n"
    by (rule paper_v_ball_upper[OF kn T0' L0])
  consider (out) "r < norm x" | (sph) "norm x = r"
    | (inn) "norm x < r" "x \<noteq> 0" | (ctr) "x = 0"
    by (cases "r < norm x", simp) (cases "norm x = r", simp, cases "x = 0", auto)
  then show ?thesis
  proof cases
    case out
    then have "x \<notin> cball (0 :: real^'n) r" by simp
    then have z: "paper_v k L T (cball 0 r) x = 0"
      by (rule paper_v_zero_outside[OF T0'])
    have "r * r < norm x * norm x"
      by (rule mult_strict_mono) (use out r0 in auto)
    then have "(r * r - x \<bullet> x) / real (CARD('n) - k) < 0"
      unfolding sq using nk0 by (simp add: divide_neg_pos)
    then show ?thesis unfolding z by simp
  next
    case sph
    then have z: "paper_v k L T (cball 0 r) x = 0"
      by (rule paper_v_boundary_zero[OF kn T0 L0])
    have "x \<bullet> x = r * r" unfolding sq sph by (rule refl)
    then show ?thesis unfolding z by simp
  next
    case inn
    have nn: "0 \<le> (r * r - x \<bullet> x) / real (CARD('n) - k)"
    proof -
      have "norm x * norm x \<le> r * r"
        by (rule mult_mono) (use inn(1) r0 in auto)
      then show ?thesis unfolding sq using nk0 by simp
    qed
    have "(r * r - x \<bullet> x) / real (CARD('n) - k)
        \<le> enn2real (paper_v k L T (cball 0 r) x)"
      by (rule lower[OF inn(1) inn(2)])
    with upper[of x] nn show ?thesis by simp
  next
    case ctr
    text \<open>Abstract the nat subtraction: \<open>linarith\<close> cannot see through
      \<open>real (CARD('n) - k)\<close>.\<close>
    define nk where "nk = real (CARD('n) - k)"
    have nkp: "0 < nk" unfolding nk_def using kn by simp
    have lower': "\<And>y :: real^'n. norm y < r \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
        (r * r - y \<bullet> y) / nk \<le> enn2real (paper_v k L T (cball 0 r) y)"
      unfolding nk_def by (rule lower)
    have upper': "enn2real (paper_v k L T (cball 0 r) y)
        \<le> max ((r * r - y \<bullet> y) / nk) 0" for y :: "real^'n"
      unfolding nk_def by (rule upper)
    have goalR: "max ((r * r - x \<bullet> x) / nk) 0 = r * r / nk"
      unfolding ctr using nkp r0 by simp
    have le: "enn2real (paper_v k L T (cball 0 r) x) \<le> r * r / nk"
      using upper'[of x] goalR by simp
    have ge: "r * r / nk \<le> enn2real (paper_v k L T (cball 0 r) x)"
    proof (rule ccontr)
      assume "\<not> r * r / nk \<le> enn2real (paper_v k L T (cball 0 r) x)"
      then have lt0: "enn2real (paper_v k L T (cball 0 r) x) < r * r / nk"
        by simp
      define b where "b = (enn2real (paper_v k L T (cball 0 r) x)
          + r * r / nk) / 2"
      have b2: "2 * b = enn2real (paper_v k L T (cball 0 r) x) + r * r / nk"
        unfolding b_def by simp
      have blo: "enn2real (paper_v k L T (cball 0 r) x) < b" using lt0 b2 by linarith
      have bhi: "b < r * r / nk" using lt0 b2 by linarith
      have "paper_v k L T (cball 0 r) x < ennreal b"
        using blo paper_v_ball_fin[OF kn T0' L0] by (simp add: enn2real_less_iff)
      then have "eventually (\<lambda>y. paper_v k L T (cball 0 r) y < ennreal b) (nhds x)"
        by (rule paper_v_usc_unconditional[OF T0 L1 Kc])
      then obtain U where opU: "open U" and xU: "x \<in> U"
        and Uy: "\<And>y. y \<in> U \<Longrightarrow> paper_v k L T (cball 0 r) y < ennreal b"
        unfolding eventually_nhds by blast
      obtain e where e0: "0 < e" and eU: "ball x e \<subseteq> U"
        using opU xU unfolding open_contains_ball by blast
      obtain i :: 'n where "True" by blast
      define u1 :: "real^'n" where "u1 = axis i 1"
      have nu1: "norm u1 = 1" unfolding u1_def by simp
      have q0: "0 < r * r - b * nk" using bhi nkp by (simp add: field_simps)
      define s where "s = min (min (e/2) (r/2)) (sqrt (r * r - b * nk) / 2)"
      have s0: "0 < s" unfolding s_def using e0 r0 q0 by simp
      define y where "y = s *\<^sub>R u1"
      have ny: "norm y = s" unfolding y_def using s0 by (simp add: nu1)
      have ynz: "y \<noteq> 0" using ny s0 by auto
      have ylt: "norm y < r" unfolding ny s_def using r0 by simp
      have yU: "y \<in> U"
      proof -
        have "dist x y = s" unfolding ctr using ny by (simp add: dist_norm)
        then have "y \<in> ball x e" unfolding s_def using e0 by simp
        then show ?thesis using eU by blast
      qed
      have vylt: "enn2real (paper_v k L T (cball 0 r) y) < b"
        using Uy[OF yU] paper_v_ball_fin[OF kn T0' L0]
        by (simp add: enn2real_less_iff)
      have "(r * r - y \<bullet> y) / nk \<le> enn2real (paper_v k L T (cball 0 r) y)"
        by (rule lower'[OF ylt ynz])
      then have vge: "(r * r - s * s) / nk < b"
        using vylt unfolding sq ny by simp
      have ssq: "s * s < r * r - b * nk"
      proof -
        have sle: "s \<le> sqrt (r * r - b * nk) / 2" unfolding s_def by simp
        have sq0: "0 \<le> sqrt (r * r - b * nk) / 2" using q0 by simp
        have "s * s \<le> (sqrt (r * r - b * nk) / 2) * (sqrt (r * r - b * nk) / 2)"
          by (rule mult_mono[OF sle sle sq0]) (use s0 in linarith)
        also have "\<dots> = (r * r - b * nk) / 4"
        proof -
          have "sqrt (r * r - b * nk) * sqrt (r * r - b * nk) = r * r - b * nk"
            using q0 by simp
          then show ?thesis by simp
        qed
        also have "\<dots> < r * r - b * nk" using q0 by simp
        finally show ?thesis .
      qed
      then have blt: "b < (r * r - s * s) / nk"
        using nkp by (simp add: field_simps)
      show False using vge blt by linarith
    qed
    show ?thesis using le ge goalR unfolding nk_def[symmetric] by simp
  qed
qed

subsection \<open>Example 3.1 for general \<open>k\<close>\<close>

text \<open>The interior lower bound is now available at the SHARP rate
  \<open>CARD('n) - k\<close>: for \<open>y \<noteq> 0\<close> take the \<open>(CARD('n) - k + 1)\<close>-dimensional
  subspace \<open>V\<close> spanned by an orthonormal family whose FIRST member is
  \<open>y / |y|\<close> (@{thm [source] orthonormal_family_containing}), so that
  \<open>y \<in> V\<close>, and run the subspace-tangential member of
  @{thm [source] paper_v_ball_lower_sharp} inside \<open>V\<close>.  Its growth rate is
  \<open>dim V - 1 = CARD('n) - k\<close>, which is exactly the constant in (3.1).

  The horizon hypothesis \<open>r\<^sup>2/(CARD('n) - k) \<le> T\<close> is NOT a weakening: the
  value function of a finite-horizon problem is capped by its horizon
  (@{thm [source] enn2real_paper_v_horizon_cap}), so without it the stated
  identity would be false at the centre.  It says only that the horizon does
  not bind.\<close>

theorem example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and T0: "0 < T" and r0: "0 < r"
    and Tbig: "r * r / real (CARD('n) - k) \<le> T"
  shows "enn2real (paper_v k L T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof (rule example_3_1_from_lower[OF kn L1 T0 r0])
  fix y :: "real^'n" assume ylt: "norm y < r" and ynz: "y \<noteq> 0"
  define m where "m = CARD('n) - k + 1"
  have nk0: "0 < real (CARD('n) - k)" using kn by simp
  have m2: "2 \<le> m" unfolding m_def using kn by simp
  have m0: "0 < m" using m2 by simp
  have mn: "m \<le> CARD('n)" unfolding m_def using k1 kn by simp
  have mk: "CARD('n) - k \<le> m - 1" unfolding m_def by simp
  have cn: "real m - 1 = real (CARD('n) - k)" unfolding m_def by simp
  have ny0: "0 < norm y" using ynz by simp
  define x0 where "x0 = (1 / norm y) *\<^sub>R y"
  have u: "x0 \<bullet> x0 = 1"
  proof -
    have "x0 \<bullet> x0 = (1 / norm y) * ((1 / norm y) * (y \<bullet> y))"
      unfolding x0_def by simp
    also have "\<dots> = 1" using ny0 by (simp add: dot_square_norm power2_eq_square)
    finally show ?thesis .
  qed
  obtain b :: "nat \<Rightarrow> real^'n" where b0: "b 0 = x0"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow>
        b i \<bullet> b j = (if i = j then 1 else 0)"
    using orthonormal_family_containing[OF u mn m0] by blast
  have yfix: "projmat b m *v y = y"
  proof -
    have yb: "y = norm y *\<^sub>R b 0"
      unfolding b0 x0_def using ny0 by simp
    have "projmat b m *v y = projmat b m *v (norm y *\<^sub>R b 0)"
      by (rule arg_cong[where f = "\<lambda>w. projmat b m *v w", OF yb])
    also have "\<dots> = norm y *\<^sub>R (projmat b m *v b 0)"
      by (rule matvec_scaleR_right)
    also have "\<dots> = norm y *\<^sub>R b 0"
      by (simp add: projmat_fix[OF orth m0])
    also have "\<dots> = y" by (rule yb[symmetric])
    finally show ?thesis .
  qed
  have Kc: "closed (cball (0 :: real^'n) r)" by simp
  have sub: "cball (0 :: real^'n) r \<subseteq> cball 0 r" by simp
  have bound: "ennreal (min T ((r\<^sup>2 - (norm y)\<^sup>2) / (real m - 1)))
      \<le> paper_v k L T (cball 0 r) y"
    by (rule paper_v_ball_lower_sharp[OF T0 L1 Kc sub ynz ylt orth mk m2 yfix])
  have sq: "(norm y)\<^sup>2 = y \<bullet> y" by (simp add: dot_square_norm)
  have rsq: "r\<^sup>2 = r * r" by (simp add: power2_eq_square)
  have nn: "0 \<le> (r * r - y \<bullet> y) / real (CARD('n) - k)"
  proof -
    have "norm y * norm y \<le> r * r"
      by (rule mult_mono) (use ylt r0 in auto)
    then have "y \<bullet> y \<le> r * r"
      unfolding sq[symmetric] by (simp add: power2_eq_square)
    then show ?thesis using nk0 by simp
  qed
  have dle: "(r * r - y \<bullet> y) / real (CARD('n) - k) \<le> T"
  proof -
    have "(r * r - y \<bullet> y) / real (CARD('n) - k)
        \<le> (r * r) / real (CARD('n) - k)"
      using nk0 by (intro divide_right_mono) simp_all
    then show ?thesis using Tbig by (rule order_trans)  qed
  have mineq: "min T ((r * r - y \<bullet> y) / real (CARD('n) - k))
      = (r * r - y \<bullet> y) / real (CARD('n) - k)"
    using dle by simp
  have bound': "ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k))
      \<le> paper_v k L T (cball 0 r) y"
    using bound unfolding sq rsq cn mineq .
  have fin: "paper_v k L T (cball 0 r) y < \<top>"
    by (rule paper_v_ball_fin[OF kn]) (use T0 L1 in auto)
  have ntop: "paper_v k L T (cball 0 r) y \<noteq> \<top>" using fin by simp
  have "enn2real (ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k)))
      \<le> enn2real (paper_v k L T (cball 0 r) y)"
    by (rule enn2real_mono[OF bound' fin])
  then show "(r * r - y \<bullet> y) / real (CARD('n) - k)
      \<le> enn2real (paper_v k L T (cball 0 r) y)"
    unfolding enn2real_ennreal[OF nn] .
qed

end
