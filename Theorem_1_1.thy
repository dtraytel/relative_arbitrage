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
    Section_2_Usc Deterministic_Radius_Market
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
    and su: "visc_sol k L (interior K) u"
    and sw: "visc_sol k L (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
    and x: "x \<in> K"
  shows "u x = w x"
  by (rule viscosity_uniqueness_compact
      [OF cK neK k(1) k(2) L cu cw su sw bd x])

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
    using power_mono[OF xr norm_ge_zero] nsq by simp
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
    show ?thesis
      unfolding sqn
      by (rule vec_eq_iff[THEN iffD2])
        (auto simp: c1 c2 exhaust_2)
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
    using SM EI by blast
  have bv: "ball_v r 1 x = r\<^sup>2 - q"
    unfolding ball_v_def q_def[symmetric]
    using qr by (simp add: max_absorb1)
  show "ennreal (ball_v r 1 x) \<le> stopped_val_fn 1 L (cball 0 r) x"
    unfolding stopped_val_fn_def bv
    by (rule Sup_upper[OF mem])
qed

end
