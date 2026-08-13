section \<open>Theorem 1.1: the value function is the unique viscosity solution\<close>

(*<*)
theory Value_Function_Uniqueness
  imports Value_Function_Market Viscosity_Solutions Comparison_Principle
    Exit_Time_Semicontinuity Deterministic_Radius_Market Value_Function_Viscosity
    Exit_Class_Infinite
begin
(*>*)

text \<open>
  Theorem 1.1 of arXiv:2512.17702 asserts that the value function \<open>v\<close> of
  Eq. (1.6) is the unique bounded upper semicontinuous viscosity solution of
  Eq. (1.9) satisfying the zero boundary condition of Eq. (1.10).  This theory
  joins the two halves of that statement: the viscosity property, proved in
  @{theory Relative_Arbitrage.Value_Function_Viscosity}, and the comparison principle, proved in
  @{theory Relative_Arbitrage.Comparison_Principle}.  It also derives Example 3.1 in closed form.
\<close>

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

section \<open>The clauses of Theorem 1.1 and where they are proved\<close>

text \<open>With \<open>v = enn2real \<circ> exit_val k L T K\<close>, Theorem 1.1 has five clauses.

  \<^item> Finiteness, \<open>exit_val k L T K x < \<top>\<close>: \<open>exit_val_le_T\<close>, and sharply
    \<open>exit_val_le_ball_bound\<close>.
  \<^item> Upper semicontinuity: \<open>Exit_Class_Compactness.exit_val_usc_unconditional\<close>.
  \<^item> The viscosity property of Eq. (1.9): \<open>Value_Function_Viscosity.exit_val_visc_subsol\<close>
    for the subsolution half, with the operator of Eq. (1.9) itself, and
    \<open>Value_Function_Viscosity.exit_val_supersol_lsc\<close> for the supersolution half.
  \<^item> The zero boundary condition of Eq. (1.10), in the viscosity sense of
    Definition 3.1: \<open>Value_Function_Viscosity.exit_val_subsol_bc\<close> and
    \<open>exit_val_supersol_bc\<close> below.
  \<^item> Uniqueness: \<open>theorem_1_1_uniqueness_faithful\<close> below, via the paper's
    Theorem 4.2(a), Theorem 4.2(b), Theorem 4.3 and Proposition 4.1.

  The boundary condition is a viscosity condition, not the pointwise identity
  \<open>v = 0\<close> on \<open>K - interior K\<close>, which is false in general: by Lemma 5.3 of the
  paper, a convex \<open>K\<close> has \<open>v x = 0\<close> exactly when the face containing \<open>x\<close> has
  dimension at most \<open>n - k\<close>, so the cube in \<open>\<real>\<^sup>3\<close> with \<open>k = 2\<close> has \<open>v > 0\<close> on
  the open two-dimensional faces of its boundary.  The pointwise identity is
  proved here only for a ball, where it holds.\<close>

section \<open>A comparison principle without a regularity hypothesis is refutable\<close>

text \<open>\<open>comparison_principle\<close> (@{theory Relative_Arbitrage.Viscosity_Comparison_Interface}) states comparison
  with no regularity hypothesis on \<open>u\<close> and \<open>w\<close>.  It holds for no ball.
  \<open>visc_subsol\<close> and \<open>visc_supersol\<close> are conditions local to \<open>\<Omega>\<close>, so the values
  of a sub- or supersolution outside \<open>\<Omega>\<close> are unconstrained: \<open>u = ball_v + 1\<close> is
  a subsolution, and \<open>w\<close> taken equal to \<open>ball_v\<close> inside the ball and to
  \<open>ball_v + 1\<close> outside is a supersolution agreeing with \<open>u\<close> on the boundary,
  yet \<open>u > w\<close> at the centre.  Hence \<open>ball_v_unique_solution\<close>, which carries
  \<open>comparison_principle\<close> as a hypothesis, is vacuous;
  \<open>theorem_1_1_uniqueness_general\<close> below replaces it.\<close>

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

section \<open>Example 3.1 realises the ball value exactly, for \<open>n - k = 1\<close>\<close>

section \<open>The value function satisfies both clauses of Definition 3.1\<close>

text \<open>Both halves of the viscosity property land in the envelope forms that
  @{thm [source] viscosity_uniqueness_compact} consumes:
  @{thm [source] visc_subsol_imp_env} on the subsolution side, the
  envelope-free notion proved for \<open>exit_val\<close> being the stronger one, and
  @{thm [source] visc_supersol_lsc_iff_env} on the supersolution side.  The
  horizon hypothesis is discharged by @{thm [source] exit_val_cap_inert}.

  The statement below assumes continuity of \<open>exit_val\<close> on \<open>K\<close>.  Theorem 1.1
  speaks of the unique upper semicontinuous solution and needs no continuity;
  \<open>theorem_1_1_uniqueness_faithful\<close> below is the faithful form, and
  supersedes this one.\<close>

section \<open>Theorem 1.1 assembled\<close>

text \<open>\<open>exit_val\<close> as a real-valued function: nonnegative, globally bounded, and
  upper semicontinuous in the \<open>\<epsilon>\<close>-form the comparison machinery consumes.\<close>

lemma exit_val_real_nonneg: "0 \<le> enn2real (exit_val k L T K x)"
  by simp

lemma exit_val_real_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
  shows "\<bar>enn2real (exit_val k L T K x)\<bar> \<le> rK * rK / real (CARD('n) - k)"
proof -
  have nk: "0 < real (CARD('n) - k)" using kn by simp
  have le: "exit_val k L T K x
      \<le> ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k))"
    by (rule exit_val_le_ball_bound[OF kn T0 L0 KB])
  have fin: "ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k)) < \<top>"
    by simp
  have "enn2real (exit_val k L T K x)
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
  finally show ?thesis using exit_val_real_nonneg[of k L T K x] by simp
qed

lemma exit_val_real_usc:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)" and KB: "K \<subseteq> cball 0 rK"
    and lt: "enn2real (exit_val k L T K z) < cc"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (exit_val k L T K y) < cc"
proof -
  have L0: "0 \<le> L" using L by simp
  have T0: "0 \<le> T" using T by simp
  have cc0: "0 < cc" using lt exit_val_real_nonneg[of k L T K z] by linarith
  have fin: "exit_val k L T K y < \<top>" for y
  proof -
    have "exit_val k L T K y
        \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      by (rule exit_val_le_ball_bound[OF kn T0 L0 KB])
    also have "\<dots> < \<top>" by simp
    finally show ?thesis .
  qed
  have zlt: "exit_val k L T K z < ennreal cc"
    using lt fin[of z] by simp
  have "eventually (\<lambda>y. exit_val k L T K y < ennreal cc) (nhds z)"
    by (rule exit_val_usc_unconditional[OF T L Kc zlt])
  then obtain U where opU: "open U" and zU: "z \<in> U"
    and Uy: "\<And>y. y \<in> U \<Longrightarrow> exit_val k L T K y < ennreal cc"
    unfolding eventually_nhds by blast
  obtain e where e0: "0 < e" and eU: "ball z e \<subseteq> U"
    using opU zU unfolding open_contains_ball by blast
  have "enn2real (exit_val k L T K y) < cc" if dy: "dist z y < e" for y
  proof -
    have "y \<in> U" using eU dy by auto
    then have "exit_val k L T K y < ennreal cc" by (rule Uy)
    then show ?thesis using fin[of y] cc0 by simp
  qed
  then show ?thesis using e0 by blast
qed

text \<open>The supersolution clause of Definition 3.1 for \<open>exit_val\<close>, with the
  boundary gate included.  The gate is vacuous: \<open>exit_val \<ge> 0\<close>, hence so is its
  lower envelope, so \<open>{x. lsc_env v x < 0} = {}\<close> and the \<open>\<Omega>\<close> of
  Definition 3.1(b) collapses to \<open>interior K\<close>.\<close>

theorem exit_val_supersol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
          lsc_env (\<lambda>z. enn2real (exit_val k L T K z)) x < 0})
      (lsc_env (\<lambda>z. enn2real (exit_val k L T K z)))"
proof -
  define v where "v = (\<lambda>z. enn2real (exit_val k L T K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by (rule exit_val_real_nonneg)
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
    by (rule exit_val_supersol_lsc_bounded[OF T0 L1 k1 kn Kc KB Tbig])
  then have "visc_supersol_env k L K (interior K) (lsc_env v)"
    unfolding visc_supersol_lsc_def visc_supersol_env_def by blast
  then show ?thesis unfolding v_def[symmetric] gate .
qed

text \<open>\<^bold>\<open>Theorem 1.1, uniqueness clause.\<close>  \<open>exit_val\<close> is upper semicontinuous
  (\<open>exit_val_real_usc\<close>), nonnegative, globally bounded (\<open>exit_val_real_bounded\<close>)
  and satisfies both clauses of Definition 3.1 with their boundary gates
  (\<open>exit_val_subsol_bc\<close>, \<open>exit_val_supersol_bc\<close>); on an expandable \<open>K\<close> it is the
  only such function.\<close>

theorem theorem_1_1_uniqueness_faithful:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and subu: "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and x: "x \<in> K"
  shows "u x = enn2real (exit_val k L T K x)"
proof -
  define v where "v = (\<lambda>z. enn2real (exit_val k L T K z))"
  define B where "B = max Bd (rK * rK / real (CARD('n) - k))"
  have L0: "1 \<le> L" using L1 by simp
  have T0': "0 \<le> T" using T0 by simp
  have L0': "0 \<le> L" using L1 by simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have Bv: "\<bar>v y\<bar> \<le> B" for y
  proof -
    have "\<bar>v y\<bar> \<le> rK * rK / real (CARD('n) - k)"
      unfolding v_def by (rule exit_val_real_bounded[OF kn T0' L0' KB r0])
    then show ?thesis unfolding B_def by (simp add: le_max_iff_disj)
  qed
  have Bu': "\<bar>u y\<bar> \<le> B" for y
    using Bu[of y] unfolding B_def by (simp add: le_max_iff_disj)
  have uscv: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c" if "v z < c" for c z
    using that unfolding v_def by (rule exit_val_real_usc[OF T0 L0 Kc kn KB])
  have supv: "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env v x < 0}) (lsc_env v)"
    unfolding v_def by (rule exit_val_supersol_bc[OF T0 L1 k1 kn Kc KB Tbig])
  have subv: "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def by (rule exit_val_subsol_bc[OF T0 L0 Kc kn])
  have "u x = v x"
    by (rule uniqueness_expandable
        [OF k1 kn L0 cK neK expK uscu uscv Bu' Bv subu supu subv supv x])
  then show ?thesis unfolding v_def by simp
qed

section \<open>Example 3.1 from the interior lower bound\<close>

text \<open>Everything of Example 3.1 except the interior lower bound at nonzero
  points.  Four cases: outside the ball the value is \<open>0\<close>, since a path starting
  outside \<open>K\<close> has exit time \<open>0\<close> (\<open>exit_val_zero_outside\<close>); on the sphere,
  \<open>exit_val_boundary_zero\<close>; strictly inside and nonzero, the hypothesis against
  \<open>exit_val_le_ball_bound\<close>; and at the centre by upper semicontinuity, rather
  than by running the tangential field from \<open>0\<close>, where the clamp sits.\<close>

lemma exit_val_ball_fin:
  fixes r :: real and y :: "real^'n::finite"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
  shows "exit_val k L T (cball 0 r) y < \<top>"
proof -
  have "exit_val k L T (cball 0 r) y
      \<le> ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k))"
    by (rule exit_val_le_ball_bound[OF kn T0 L0]) simp
  also have "\<dots> < \<top>" by simp
  finally show ?thesis .
qed

lemma exit_val_ball_upper:
  fixes r :: real and y :: "real^'n::finite"
  assumes kn: "k < CARD('n)" and T0: "0 \<le> T" and L0: "0 \<le> L"
  shows "enn2real (exit_val k L T (cball 0 r) y)
      \<le> max ((r * r - y \<bullet> y) / real (CARD('n) - k)) 0"
proof -
  have le: "exit_val k L T (cball 0 r) y
      \<le> ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k))"
    by (rule exit_val_le_ball_bound[OF kn T0 L0]) simp
  have "enn2real (exit_val k L T (cball 0 r) y)
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
          \<le> enn2real (exit_val k L T (cball 0 r) y)"
  shows "enn2real (exit_val k L T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof -
  have nk0: "0 < real (CARD('n) - k)" using kn by simp
  have L0: "0 \<le> L" using L1 by simp
  have T0': "0 \<le> T" using T0 by simp
  have Kc: "closed (cball (0 :: real^'n) r)" by simp
  have sq: "y \<bullet> y = norm y * norm y" for y :: "real^'n"
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  have upper: "enn2real (exit_val k L T (cball 0 r) y)
      \<le> max ((r * r - y \<bullet> y) / real (CARD('n) - k)) 0" for y :: "real^'n"
    by (rule exit_val_ball_upper[OF kn T0' L0])
  consider (out) "r < norm x" | (sph) "norm x = r"
    | (inn) "norm x < r" "x \<noteq> 0" | (ctr) "x = 0"
    by (cases "r < norm x", simp) (cases "norm x = r", simp, cases "x = 0", auto)
  then show ?thesis
  proof cases
    case out
    then have "x \<notin> cball (0 :: real^'n) r" by simp
    then have z: "exit_val k L T (cball 0 r) x = 0"
      by (rule exit_val_zero_outside[OF T0'])
    have "r * r < norm x * norm x"
      by (rule mult_strict_mono) (use out r0 in auto)
    then have "(r * r - x \<bullet> x) / real (CARD('n) - k) < 0"
      unfolding sq using nk0 by (simp add: divide_neg_pos)
    then show ?thesis unfolding z by simp
  next
    case sph
    then have z: "exit_val k L T (cball 0 r) x = 0"
      by (rule exit_val_boundary_zero[OF kn T0 L0])
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
        \<le> enn2real (exit_val k L T (cball 0 r) x)"
      by (rule lower[OF inn(1) inn(2)])
    with upper[of x] nn show ?thesis by simp
  next
    case ctr
    text \<open>Abstract the nat subtraction: \<open>linarith\<close> cannot see through
      \<open>real (CARD('n) - k)\<close>.\<close>
    define nk where "nk = real (CARD('n) - k)"
    have nkp: "0 < nk" unfolding nk_def using kn by simp
    have lower': "\<And>y :: real^'n. norm y < r \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
        (r * r - y \<bullet> y) / nk \<le> enn2real (exit_val k L T (cball 0 r) y)"
      unfolding nk_def by (rule lower)
    have upper': "enn2real (exit_val k L T (cball 0 r) y)
        \<le> max ((r * r - y \<bullet> y) / nk) 0" for y :: "real^'n"
      unfolding nk_def by (rule upper)
    have goalR: "max ((r * r - x \<bullet> x) / nk) 0 = r * r / nk"
      unfolding ctr using nkp r0 by simp
    have le: "enn2real (exit_val k L T (cball 0 r) x) \<le> r * r / nk"
      using upper'[of x] goalR by simp
    have ge: "r * r / nk \<le> enn2real (exit_val k L T (cball 0 r) x)"
    proof (rule ccontr)
      assume "\<not> r * r / nk \<le> enn2real (exit_val k L T (cball 0 r) x)"
      then have lt0: "enn2real (exit_val k L T (cball 0 r) x) < r * r / nk"
        by simp
      define b where "b = (enn2real (exit_val k L T (cball 0 r) x)
          + r * r / nk) / 2"
      have b2: "2 * b = enn2real (exit_val k L T (cball 0 r) x) + r * r / nk"
        unfolding b_def by simp
      have blo: "enn2real (exit_val k L T (cball 0 r) x) < b" using lt0 b2 by linarith
      have bhi: "b < r * r / nk" using lt0 b2 by linarith
      have "exit_val k L T (cball 0 r) x < ennreal b"
        using blo exit_val_ball_fin[OF kn T0' L0] by simp
      then have "eventually (\<lambda>y. exit_val k L T (cball 0 r) y < ennreal b) (nhds x)"
        by (rule exit_val_usc_unconditional[OF T0 L1 Kc])
      then obtain U where opU: "open U" and xU: "x \<in> U"
        and Uy: "\<And>y. y \<in> U \<Longrightarrow> exit_val k L T (cball 0 r) y < ennreal b"
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
      have vylt: "enn2real (exit_val k L T (cball 0 r) y) < b"
        using Uy[OF yU] exit_val_ball_fin[OF kn T0' L0]
        by simp
      have "(r * r - y \<bullet> y) / nk \<le> enn2real (exit_val k L T (cball 0 r) y)"
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

text \<open>The interior lower bound holds at the sharp rate \<open>CARD('n) - k\<close>: for
  \<open>y \<noteq> 0\<close> take the \<open>(CARD('n) - k + 1)\<close>-dimensional subspace \<open>V\<close> spanned by an
  orthonormal family whose first member is \<open>y / |y|\<close>
  (@{thm [source] orthonormal_family_containing}), so that \<open>y \<in> V\<close>, and run the
  subspace-tangential member of @{thm [source] exit_val_ball_lower_sharp} inside
  \<open>V\<close>.  Its growth rate is \<open>dim V - 1 = CARD('n) - k\<close>, the constant of (3.1).

  The hypothesis \<open>r\<^sup>2/(CARD('n) - k) \<le> T\<close> says only that the horizon does not
  bind: the value function of a finite-horizon problem is capped by its horizon
  (@{thm [source] enn2real_paper_v_horizon_cap}), so without it the identity
  would fail at the centre.\<close>

theorem example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and T0: "0 < T" and r0: "0 < r"
    and Tbig: "r * r / real (CARD('n) - k) \<le> T"
  shows "enn2real (exit_val k L T (cball 0 r) x)
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
      \<le> exit_val k L T (cball 0 r) y"
    by (rule exit_val_ball_lower_sharp[OF T0 L1 Kc sub ynz ylt orth mk m2 yfix])
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
      \<le> exit_val k L T (cball 0 r) y"
    using bound unfolding sq rsq cn mineq .
  have fin: "exit_val k L T (cball 0 r) y < \<top>"
    by (rule exit_val_ball_fin[OF kn]) (use T0 L1 in auto)
  have ntop: "exit_val k L T (cball 0 r) y \<noteq> \<top>" using fin by simp
  have "enn2real (ennreal ((r * r - y \<bullet> y) / real (CARD('n) - k)))
      \<le> enn2real (exit_val k L T (cball 0 r) y)"
    by (rule enn2real_mono[OF bound' fin])
  then show "(r * r - y \<bullet> y) / real (CARD('n) - k)
      \<le> enn2real (exit_val k L T (cball 0 r) y)"
    unfolding enn2real_ennreal[OF nn] .
qed

section \<open>The clauses for the value function of Eq. (1.6)\<close>

text \<open>Everything above is stated at a finite horizon.  Since
  @{thm [source] iexit_val_eq_exit_val_ball} identifies the two value
  functions uniformly in the point once the horizon exceeds \<open>r\<^sup>2/(n-k)\<close>, the
  horizon can be chosen inside each proof and disappears from the statements:
  what follows is Theorem 1.1 for the value function of Eq. (1.6) as the paper
  writes it, on \<open>C([0,\<infinity>))\<close>.\<close>

text \<open>On \<open>real^'n\<close> compactness is closedness together with a ball bound, so
  one hypothesis supplies both of the ones the transfer needs.  The radius is
  named only where it appears in a conclusion, which is clause (0).\<close>

lemma compact_cball_bound:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K"
  shows "\<exists>rK. 0 \<le> rK \<and> K \<subseteq> cball 0 rK"
proof -
  obtain a where a: "\<forall>x\<in>K. norm x \<le> a"
    using compact_imp_bounded[OF cK] unfolding bounded_iff by blast
  have "K \<subseteq> cball 0 (max a 0)" using a by (auto simp: dist_norm)
  moreover have "0 \<le> max a 0" by simp
  ultimately show ?thesis by blast
qed

lemma nonbinding_horizon_ex:
  fixes rK :: real
  assumes k: "k < CARD('n::finite)"
  shows "\<exists>T :: real. 0 < T \<and> rK * rK / real (CARD('n) - k) < T
       \<and> 2 * (rK * rK) / real (CARD('n) - k) < T"
proof -
  have nk: "0 < real (CARD('n) - k)" using k by simp
  define B :: real where "B = 2 * (rK * rK) / real (CARD('n) - k)"
  have B0: "0 \<le> B" unfolding B_def using nk by simp
  have le: "rK * rK / real (CARD('n) - k) \<le> B"
    unfolding B_def using nk by (intro divide_right_mono) auto
  show ?thesis
  proof (intro exI[of _ "B + 1"] conjI)
    show "0 < B + 1" using B0 by simp
    show "rK * rK / real (CARD('n) - k) < B + 1" using le by simp
    show "2 * (rK * rK) / real (CARD('n) - k) < B + 1"
      unfolding B_def[symmetric] by simp
  qed
qed

text \<open>\<^bold>\<open>Clause (0): finiteness.\<close>\<close>

theorem iexit_val_real_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L: "1 \<le> L" and cK: "compact K"
    and KB: "K \<subseteq> cball 0 rK" and r0: "0 \<le> rK"
  shows "\<bar>enn2real (iexit_val k L K x)\<bar> \<le> rK * rK / real (CARD('n) - k)"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq
    using L by (intro exit_val_real_bounded[OF kn less_imp_le[OF T0] _ KB r0]) simp
qed

text \<open>\<^bold>\<open>Clause (1): upper semicontinuity.\<close>\<close>

theorem iexit_val_real_usc:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L: "1 \<le> L" and cK: "compact K"
    and lt: "enn2real (iexit_val k L K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (iexit_val k L K y) < c"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq
    by (rule exit_val_real_usc[OF T0 L Kc kn KB lt[unfolded eq]])
qed

text \<open>\<^bold>\<open>Clause (2), subsolution half.\<close>\<close>

theorem iexit_val_visc_subsol:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L: "1 \<le> L" and cK: "compact K"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (iexit_val k L K z))"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq by (rule exit_val_visc_subsol[OF T0 L Kc kn])
qed

text \<open>\<^bold>\<open>Clause (2), supersolution half\<close>, in the form of Definition 3.1(b) for
  the lower semicontinuous envelope.  The hypothesis that the horizon does not
  bind at interior points is discharged by the a priori bound, so it too is
  gone.\<close>

text \<open>\<^bold>\<open>Clause (3): the zero boundary condition of Eq. (1.10)\<close>, in the
  viscosity sense of Definition 3.1, both halves with the boundary gate.\<close>

theorem iexit_val_subsol_bc:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L: "1 \<le> L" and cK: "compact K"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (iexit_val k L K x)})
      (\<lambda>z. enn2real (iexit_val k L K z))"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq by (rule exit_val_subsol_bc[OF T0 L Kc kn])
qed

text \<open>\<^bold>\<open>Clause (4): uniqueness.\<close>\<close>

theorem iexit_val_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env k L K
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_env k L K
        (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
proof -
  have L: "1 \<le> L" using L1 by simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    and T2: "2 * (rK * rK) / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq
    by (rule theorem_1_1_uniqueness_faithful[OF T0 L1 k1 kn cK neK expK KB r0
          T2 usc bnd sub sups xK])
qed

text \<open>\<^bold>\<open>Clauses (3) and (4) with the paper's own envelope.\<close>  Definition 3.1
  reads \<open>u\<^sub>*\<close> within \<open>K\<close>, which is @{const lsc_envK}; the clauses above read it
  over balls of \<open>real^'n\<close>.  The two differ only on \<open>K - interior K\<close>, and there
  the difference is real: on a cube with \<open>k = 2\<close> the value function is positive
  on the open two-dimensional faces, so its liminf within \<open>K\<close> is positive
  there while its liminf over balls of \<open>real^'n\<close> is \<open>0\<close>.  Both clauses are
  therefore restated, not derived by a weakening.\<close>

theorem exit_val_supersol_bc_K:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and KB: "K \<subseteq> cball 0 rK"
    and Tbig: "2 * (rK * rK) / real (CARD('n) - k) < T"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
          lsc_envK K (\<lambda>z. enn2real (exit_val k L T K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (exit_val k L T K z)))"
proof -
  define v where "v = (\<lambda>z :: real^'n. enn2real (exit_val k L T K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by (rule exit_val_real_nonneg)
  have gate: "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} = interior K"
  proof
    show "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} \<subseteq> interior K"
    proof
      fix y assume y: "y \<in> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      show "y \<in> interior K"
      proof (cases "y \<in> interior K")
        case True then show ?thesis .
      next
        case False
        then have yK: "y \<in> K" and neg: "lsc_envK K v y < 0" using y by auto
        have "0 \<le> lsc_envK K v y" by (rule lsc_envK_ge[OF v0 yK])
        then show ?thesis using neg by linarith
      qed
    qed
    show "interior K \<subseteq> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      by blast
  qed
  have cap: "lsc_env v y < T / 2" for y :: "real^'n"
    unfolding v_def by (rule exit_val_cap_inert[OF kn _ _ KB Tbig]) (use L1 T0 in auto)
  have main: "visc_supersol_env k L K (interior K) (lsc_envK K v)"
    unfolding v_def
    by (rule exit_val_supersol_envK[OF T0 L1 k1 kn Kc])
      (use cap in \<open>simp add: v_def\<close>)
  show ?thesis using main unfolding v_def[symmetric] gate .
qed

theorem iexit_val_supersol_bc_K:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)))"
proof -
  have L: "1 \<le> L" using L1 by simp
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  obtain T :: real where T0: "0 < T"
    and T1: "rK * rK / real (CARD('n) - k) < T"
    and T2: "2 * (rK * rK) / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L K y = exit_val k L T K y" for y
    by (rule iexit_val_eq_exit_val_ball[OF kn L Kc KB T1])
  show ?thesis unfolding eq
    by (rule exit_val_supersol_bc_K[OF T0 L1 k1 kn Kc KB T2])
qed

text \<open>The interior clause on its own, which is Definition 3.1(b) for
  \<^const>\<open>iexit_val\<close> with the paper's envelope: the boundary gate is empty,
  since the value function is nonnegative and so is its liminf within \<open>K\<close>.\<close>

theorem iexit_val_supersol_lsc_K:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  shows "visc_supersol_env k L K (interior K)
      (lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)))"
proof -
  define v where "v = (\<lambda>z :: real^'n. enn2real (iexit_val k L K z))"
  have v0: "0 \<le> v y" for y unfolding v_def by simp
  have gate: "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} = interior K"
  proof
    show "interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0} \<subseteq> interior K"
    proof
      fix y assume y: "y \<in> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      show "y \<in> interior K"
      proof (cases "y \<in> interior K")
        case True then show ?thesis .
      next
        case False
        then have yK: "y \<in> K" and neg: "lsc_envK K v y < 0" using y by auto
        have "0 \<le> lsc_envK K v y" by (rule lsc_envK_ge[OF v0 yK])
        then show ?thesis using neg by linarith
      qed
    qed
    show "interior K \<subseteq> interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}"
      by blast
  qed
  have main: "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding v_def by (rule iexit_val_supersol_bc_K[OF kn L1 k1 cK])
  show ?thesis using main unfolding v_def[symmetric] gate .
qed

theorem iexit_val_uniqueness_K:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env k L K
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sups: "visc_supersol_env k L K
        (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and xK: "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have Bu: "u y \<le> Bd" if "y \<in> K" for y
    using bnd[OF that] by (simp add: abs_le_iff)
  have iK: "interior K \<subseteq> K" by (rule interior_subset)
  define ubar where "ubar = Kext K u"
  have eqK: "ubar y = u y" if "y \<in> K" for y
    unfolding ubar_def by (rule Kext_eq_on_K[OF Kc neK Bu usc that])
  have bnd': "\<bar>ubar y\<bar> \<le> Bd" for y
    unfolding ubar_def by (rule Kext_bounded[OF Kc neK bnd])
  have usc': "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> ubar y < c" if lt: "ubar z < c" for c z
  proof -
    have lt': "Kext K u z < c" using lt unfolding ubar_def .
    have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c"
      by (rule Kext_usc[OF Kc neK Bu lt'])
    then show ?thesis unfolding ubar_def .
  qed
  have lscK: "lsc_env ubar y = lsc_envK K u y" if "y \<in> K" for y
    unfolding ubar_def by (rule lsc_env_Kext[OF Kc neK bnd usc that])
  have gate1: "{z \<in> K - interior K. 0 < ubar z}
      = {z \<in> K - interior K. 0 < u z}"
    using eqK by auto
  have gate2: "{z \<in> K - interior K. lsc_env ubar z < 0}
      = {z \<in> K - interior K. lsc_envK K u z < 0}"
    using lscK by auto
  have sub': "visc_subsol_env k L K
      (interior K \<union> {z \<in> K - interior K. 0 < ubar z}) ubar"
    unfolding gate1 by (rule visc_subsol_env_cong[OF _ _ sub]) (use eqK iK in auto)
  have sups': "visc_supersol_env k L K
      (interior K \<union> {z \<in> K - interior K. lsc_env ubar z < 0}) (lsc_env ubar)"
    unfolding gate2
    by (rule visc_supersol_env_cong[OF _ _ sups]) (use lscK iK in auto)
  have "ubar x = enn2real (iexit_val k L K x)"
    by (rule iexit_val_uniqueness[OF kn L1 k1 cK neK expK usc' bnd' sub' sups' xK])
  then show ?thesis using eqK[OF xK] by simp
qed

text \<open>\<^bold>\<open>Example 3.1\<close>, in closed form and with no horizon left in it.\<close>

theorem example_3_1_uncapped:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L: "1 \<le> L" and r0: "0 < r"
  shows "enn2real (iexit_val k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof -
  obtain T :: real where T0: "0 < T"
    and T1: "r * r / real (CARD('n) - k) < T"
    using nonbinding_horizon_ex[OF kn] by blast
  have eq: "iexit_val k L (cball 0 r) y = exit_val k L T (cball 0 r) y" for y :: "real^'n"
    by (rule iexit_val_eq_exit_val_ball[OF kn L closed_cball subset_refl T1])
  show ?thesis unfolding eq
    by (rule example_3_1[OF k1 kn L T0 r0 less_imp_le[OF T1]])
qed

(*<*)
end
(*>*)
