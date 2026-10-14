section \<open>The subspace-tangential field for Example 3.1, general \<open>k\<close>\<close>

(*<*)
theory Value_Function_Tangential_Field
  imports
    Value_Function_Supersolution_Case_1 "Relative_Arbitrage_Equation.Subspace_Tangential_Field"
begin

(*>*)

section \<open>The subspace-tangential field for Example 3.1, general \<open>k\<close>\<close>

text \<open>The tangential projector field around a centre \<open>y\<^sub>0\<close>, with the ambient
  identity replaced by the orthogonal projector onto a subspace containing
  the start.  The companion input of Case 2, that the usc envelope passes
  \<open>\<ge> 1\<close> through limits in \<open>(p, M)\<close>, is
  @{thm [source] ell_op_usc_ge_one_limit}.  Clamped away from \<open>y\<^sub>0\<close>, the
  field is an admissible volatility that kills the radial direction exactly,
  so the squared distance to \<open>y\<^sub>0\<close> moves at a deterministic rate; this is
  the positivity input for the second horn of the Case-2 dichotomy, and for
  Example 3.1's lower bound.\<close>

theorem tanpU_sq_sconstraint:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and u :: "real^'n"
  assumes orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and u1: "norm u \<le> 1" and ufix: "projmat b m *v u = u"
    and mk: "CARD('n) - k \<le> m - 1" and L1: "1 \<le> L"
  shows "tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u)
      \<in> sconstraint k L"
proof -
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  have tsym: "transpose (tanpU (projmat b m) u) = tanpU (projmat b m) u"
    by (rule tanpU_sym[OF Psym])
  have sq: "tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u)
      = tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u)"
    unfolding tsym by (rule tanpU_sq[OF Psym Pidem ufix u1])
  have n1: "norm (sqrt (2 - u \<bullet> u) *\<^sub>R u) \<le> 1" by (rule tanpU_sq_norm_le[OF u1])
  have f1: "projmat b m *v (sqrt (2 - u \<bullet> u) *\<^sub>R u) = sqrt (2 - u \<bullet> u) *\<^sub>R u"
    by (simp add: matrix_vector_mult_scaleR ufix)
  have "tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u) \<in> feasible k L 0"
    by (rule tanpU_feasible[OF orth n1 f1 mk L1])
  then show ?thesis unfolding sq using feasible_subset_sconstraint by blast
qed


text \<open>The exact growth identity for the subspace-tangential field around a
  centre \<open>y\<^sub>0\<close>, for general \<open>k\<close>: inside the region where the projection of
  \<open>z - y\<^sub>0\<close> onto \<open>V = span (b ` {..<m})\<close> is longer than the clamp \<open>\<rho>\<close>, the
  squared distance from \<open>y\<^sub>0\<close> grows at the exact rate \<open>m - 1\<close>.  Taking
  \<open>m = CARD('n)\<close> (so that the projector is the identity) gives the
  sphere-tangential field and the rate \<open>CARD('n) - 1\<close>; taking
  \<open>m = CARD('n) - k + 1\<close> gives the rate \<open>real (CARD('n) - k)\<close> that
  Example 3.1 asks for.

  The conclusion pins both the full norm and the projected norm, and they
  coincide: the two Euler slots carry the quadratics \<open>|P (z - y\<^sub>0)|\<^sup>2\<close>
  (lower) and \<open>|z - y\<^sub>0|\<^sup>2\<close> (upper), and \<open>|P w| \<le> |w|\<close> squeezes them
  together.  That is what makes the region's inner barrier --- stated in the
  projected norm, as \<open>tanpU_kill_proj\<close> demands --- a barrier for a quantity
  that only grows.\<close>

theorem subspace_tangential_exact_growth:
  fixes b :: "nat \<Rightarrow> real^'n::finite" and x y\<^sub>0 :: "real^'n" and \<rho> rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and rho0: "0 < \<rho>"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and mk: "CARD('n) - k \<le> m - 1"
    and xfix: "projmat b m *v (x - y\<^sub>0) = x - y\<^sub>0"
  shows "\<exists>P \<in> exit_class k L T x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s)
          \<in> {w. \<rho> < norm (projmat b m *v (w - y\<^sub>0))} \<inter> ball y\<^sub>0 rB) \<longrightarrow>
      (norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2
          = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)
        \<and> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)"
proof -
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  define RO where
    "RO = {w :: real^'n. \<rho> < norm (projmat b m *v (w - y\<^sub>0))} \<inter> ball y\<^sub>0 rB"
  define SF where
    "SF = (\<lambda>z. tanpU (projmat b m) (uvecV (projmat b m) \<rho> (z - y\<^sub>0)))"
  define Rn where "Rn = rB + norm (y\<^sub>0 - x)"
  have shc: "continuous_on UNIV (\<lambda>z :: real^'n. z - y\<^sub>0)"
    by (intro continuous_intros)
  have SFc: "continuous_on UNIV SF"
    unfolding SF_def by (rule continuous_on_compose2[OF tanpUV_cont[OF rho0] shc]) simp
  have mvc: "continuous_on UNIV (\<lambda>w :: real^'n. projmat b m *v (w - y\<^sub>0))"
    by (rule continuous_on_compose2[OF _ shc, of UNIV])
      (simp_all add: linear_continuous_on linear_linear)
  have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    unfolding SF_def
    by (rule tanpU_sq_sconstraint[OF orth uvecV_norm_le[OF rho0]
          uvecV_fix[OF Pidem] mk L1])
  have ROo: "open RO"
  proof -
    have "open {w :: real^'n. \<rho> < norm (projmat b m *v (w - y\<^sub>0))}"
      by (rule open_Collect_less[OF continuous_on_const continuous_on_norm[OF mvc]])
    then show ?thesis unfolding RO_def by (intro open_Int open_ball)
  qed
  have ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
  proof -
    fix z :: "real^'n" assume "z \<in> RO"
    then have "norm (z - y\<^sub>0) < rB"
      unfolding RO_def by (simp add: dist_norm norm_minus_commute)
    moreover have "norm (z - x) \<le> norm (z - y\<^sub>0) + norm (y\<^sub>0 - x)"
      using norm_triangle_ineq[of "z - y\<^sub>0" "y\<^sub>0 - x"] by simp
    ultimately show "norm (z - x) \<le> Rn" unfolding Rn_def by linarith
  qed
  have farRO: "\<rho> \<le> norm (projmat b m *v (z - y\<^sub>0))" if z: "z \<in> RO" for z
    using z unfolding RO_def by auto
  have unitRO: "norm (uvecV (projmat b m) \<rho> (z - y\<^sub>0)) = 1" if z: "z \<in> RO" for z
    by (rule uvecV_unit[OF rho0 farRO[OF z]])
  have uuRO: "uvecV (projmat b m) \<rho> (z - y\<^sub>0) \<bullet> uvecV (projmat b m) \<rho> (z - y\<^sub>0) = 1"
    if z: "z \<in> RO" for z
    using unitRO[OF z] by (simp add: dot_square_norm)
  have tsym: "transpose (SF z) = SF z" for z
    unfolding SF_def by (rule tanpU_sym[OF Psym])
  \<comment> \<open>slot 1: the quadratic \<open>|P (z - y\<^sub>0)|\<^sup>2\<close>, whose kill is \<open>tanpU_kill_proj\<close>\<close>
  have kill1: "transpose (SF z) *v (2 *\<^sub>R (x - y\<^sub>0)
      + ((2::real) *\<^sub>R projmat b m) *v (z - x)) = 0" if z: "z \<in> RO" for z
  proof -
    have zx: "z - x = (z - y\<^sub>0) - (x - y\<^sub>0)" by simp
    have Pzx: "projmat b m *v (z - x) = projmat b m *v (z - y\<^sub>0) - (x - y\<^sub>0)"
      unfolding zx matrix_vector_mult_diff_distrib[of _ "z - y\<^sub>0" "x - y\<^sub>0"] xfix ..
    have arg: "2 *\<^sub>R (x - y\<^sub>0) + ((2::real) *\<^sub>R projmat b m) *v (z - x)
        = 2 *\<^sub>R (projmat b m *v (z - y\<^sub>0))"
      unfolding scaleR_matrix_vector_assoc[symmetric] Pzx scaleR_add_right[symmetric] by simp
    have k0: "SF z *v (projmat b m *v (z - y\<^sub>0)) = 0"
      unfolding SF_def by (rule tanpU_kill_proj[OF rho0 farRO[OF z] Pidem])
    show ?thesis unfolding arg tsym by (simp add: matrix_vector_mult_scaleR k0)
  qed
  \<comment> \<open>slot 2: the quadratic \<open>-|z - y\<^sub>0|\<^sup>2\<close>, whose kill is \<open>tanpU_kill\<close>\<close>
  have kill2: "transpose (SF z) *v ((-2) *\<^sub>R (x - y\<^sub>0)
      + ((-2::real) *\<^sub>R mat 1) *v (z - x)) = 0" if z: "z \<in> RO" for z
  proof -
    have arg: "(-2) *\<^sub>R (x - y\<^sub>0) + ((-2::real) *\<^sub>R mat 1) *v (z - x)
        = (-2) *\<^sub>R (z - y\<^sub>0)"
      unfolding scaleR_matrix_vector_assoc[symmetric] by (simp add: algebra_simps)
    have k0: "SF z *v (z - y\<^sub>0) = 0"
      unfolding SF_def by (rule tanpU_kill[OF Psym Pidem rho0 farRO[OF z]])
    show ?thesis unfolding arg tsym matrix_vector_mult_scaleR k0 by simp
  qed
  have sqRO: "SF z ** transpose (SF z)
      = tanpU (projmat b m) (uvecV (projmat b m) \<rho> (z - y\<^sub>0))"
    if z: "z \<in> RO" for z
  proof -
    define u where "u = uvecV (projmat b m) \<rho> (z - y\<^sub>0)"
    have uu: "u \<bullet> u = 1" unfolding u_def by (rule uuRO[OF z])
    have ufix: "projmat b m *v u = u"
      unfolding u_def by (rule uvecV_fix[OF Pidem])
    have u1: "norm u \<le> 1" unfolding u_def by (rule uvecV_norm_le[OF rho0])
    have "SF z ** transpose (SF z)
        = tanpU (projmat b m) u ** tanpU (projmat b m) u"
      unfolding SF_def u_def tanpU_sym[OF Psym] by (rule refl)
    also have "\<dots> = tanpU (projmat b m) (sqrt (2 - u \<bullet> u) *\<^sub>R u)"
      by (rule tanpU_sq[OF Psym Pidem ufix u1])
    also have "\<dots> = tanpU (projmat b m) u" unfolding uu by simp
    finally show ?thesis unfolding u_def .
  qed
  have trSF: "trace (SF z ** transpose (SF z)) = real m - 1" if z: "z \<in> RO" for z
  proof -
    have "trace (SF z ** transpose (SF z))
        = trace (projmat b m)
          - uvecV (projmat b m) \<rho> (z - y\<^sub>0) \<bullet> uvecV (projmat b m) \<rho> (z - y\<^sub>0)"
      unfolding sqRO[OF z] by (rule tanpU_trace)
    also have "\<dots> = real m - 1"
      by (simp only: projmat_trace[OF orth] uuRO[OF z])
    finally show ?thesis .
  qed
  have trRO: "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
      = c' * (real m - 1)"
    if z: "z \<in> RO" for z c'
    by (simp add: scalar_matrix_assoc[symmetric] trace_scaleR trSF[OF z])
  have trP: "trace (((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z)))
      = 2 * (real m - 1)" if z: "z \<in> RO" for z
  proof -
    have ab: "projmat b m ** (SF z ** transpose (SF z))
        = SF z ** transpose (SF z)"
      unfolding sqRO[OF z]
      by (rule tanpU_absorb[OF Pidem uvecV_fix[OF Pidem]])
    show ?thesis
      by (simp add: scalar_matrix_assoc[symmetric] ab trace_scaleR trSF[OF z])
  qed
  have sym1: "transpose ((2::real) *\<^sub>R projmat b m)
      = (2::real) *\<^sub>R projmat b m"
    using Psym by (simp add: transpose_def vec_eq_iff)
  have sym2: "transpose ((-2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (-2::real) *\<^sub>R mat 1"
    by (simp add: transpose_def vec_eq_iff mat_def)
  have marg1: "\<And>z. z \<in> RO \<Longrightarrow> 2 * (real m - 1)
      \<le> trace (((2::real) *\<^sub>R projmat b m) ** (SF z ** transpose (SF z)))"
    using trP by simp
  have marg2: "\<And>z. z \<in> RO \<Longrightarrow> - 2 * (real m - 1)
      \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
    using trRO[of _ "-2"] by simp
  have L0: "0 \<le> L" using L1 by simp
  obtain P where P: "P \<in> covariation_class (sconstraint k L) T x"
    and AE2: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * (2 * (real m - 1)) / 2
        \<le> (2 *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((2::real) *\<^sub>R projmat b m) *v (fst (\<omega> t) - x))))
      \<and> (t * (- 2 * (real m - 1)) / 2
        \<le> ((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))"
    by (rule bexE[OF eulerp_limit_good2_region[OF T0 sconstraint_bounds[OF L0] closed_sconstraint
        sconstraint_convex SFc SFs sym1 sym2 ROo ROb kill1 marg1 kill2 marg2]])
  show ?thesis
  proof (intro bexI[OF _ P[folded exit_class_eq_covariation]])
    show "AE \<omega> in P. \<forall>t.
        0 < t \<longrightarrow> t \<le> T \<longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (projmat b m *v (w - y\<^sub>0))} \<inter> ball y\<^sub>0 rB)
        \<longrightarrow> (norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2
              = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)
          \<and> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)"
      using AE2
    proof (eventually_elim)
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix t assume t0: "0 < t" and tT: "t \<le> T"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (projmat b m *v (w - y\<^sub>0))} \<inter> ball y\<^sub>0 rB"
        have inb': "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
          using inb unfolding RO_def by blast
        define a where "a = x - y\<^sub>0"
        define d where "d = fst (\<omega> t) - x"
        have g1: "t * (2 * (real m - 1)) / 2
            \<le> (2 *\<^sub>R a) \<bullet> d + (1/2) * (d \<bullet> (((2::real) *\<^sub>R projmat b m) *v d))"
          and g2: "t * (- 2 * (real m - 1)) / 2
            \<le> ((-2) *\<^sub>R a) \<bullet> d + (1/2) * (d \<bullet> (((-2::real) *\<^sub>R mat 1) *v d))"
          using elim t0 tT inb' unfolding a_def d_def by blast+
        have e3: "d \<bullet> (((2::real) *\<^sub>R projmat b m) *v d) = 2 * (d \<bullet> (projmat b m *v d))"
          by (simp add: scaleR_matrix_vector_assoc[symmetric])
        have negmv: "\<And>A :: real^'n^'n. (- A) *v d = - (A *v d)"
          by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
        have e4: "d \<bullet> (((-2::real) *\<^sub>R mat 1) *v d) = - 2 * (d \<bullet> d)"
          by (simp add: negmv scaleR_matrix_vector_assoc[symmetric])
        have id1: "t * (2 * (real m - 1)) / 2 = t * (real m - 1)" by simp
        have id2: "t * (- 2 * (real m - 1)) / 2 = - (t * (real m - 1))"
          by (simp add: field_simps)
        have g1': "t * (real m - 1) \<le> 2 * (a \<bullet> d) + d \<bullet> (projmat b m *v d)"
          using g1 unfolding id1 e3 by simp
        have g2': "2 * (a \<bullet> d) + d \<bullet> d \<le> t * (real m - 1)"
          using g2 unfolding id2 e4 by simp
        have Pa: "projmat b m *v a = a" unfolding a_def by (rule xfix)
        have aPd: "a \<bullet> (projmat b m *v d) = a \<bullet> d"
          using inner_transpose_matrix[of a "projmat b m" d] unfolding Psym Pa .
        have dPd: "(projmat b m *v d) \<bullet> (projmat b m *v d)
            = d \<bullet> (projmat b m *v d)"
          by (rule proj_quadform_self[unfolded is_proj_def, OF conjI[OF Psym Pidem], symmetric])
        have ft: "fst (\<omega> t) - y\<^sub>0 = a + d" unfolding a_def d_def by simp
        have projsplit: "(norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2
            = (norm a)\<^sup>2 + (2 * (a \<bullet> d) + d \<bullet> (projmat b m *v d))"
          unfolding ft matrix_vector_right_distrib Pa power2_norm_eq_inner
          using aPd dPd by (simp add: inner_add_left inner_add_right inner_commute)
        have split: "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm a)\<^sup>2 + (2 * (a \<bullet> d) + d \<bullet> d)"
          unfolding ft power2_norm_eq_inner
          by (simp add: inner_add_left inner_add_right inner_commute)
        have ple: "(norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2
            \<le> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2"
          by (intro power_mono is_proj_norm_le[unfolded is_proj_def, OF conjI[OF Psym Pidem]]) simp
        show "(norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2
              = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)
            \<and> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)"
          using g1' g2' ple unfolding projsplit split a_def[symmetric] by linarith
      qed
    qed
  qed
qed

subsection \<open>Deterministic confinement and the ball lower bound\<close>

text \<open>Paths of the tangential member cannot leave the annulus around \<open>y\<^sub>0\<close>
  before the deterministic time \<open>(rB\<^sup>2 - |x-y\<^sub>0|\<^sup>2)/(m-1)\<close>: the inner
  boundary is unreachable because the squared distance only grows, and
  reaching the outer sphere pins the time exactly.  Feeding the
  DPP @{thm [source] exit_val_dpp_ge_const_time} at a constant time
  \<open>cc\<close> before that and before \<open>T\<close> turns confinement into the lower bound
  \<open>v(x) \<ge> cc + min \<beta> (T - cc)\<close>, where \<open>\<beta>\<close> bounds the value on the ball
  from below.\<close>

theorem exit_val_ball_lower_gen:
  fixes K :: "(real^'n::finite) set" and x y\<^sub>0 :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T cc \<beta> :: real
  assumes T0: "0 < T" and L1: "1 \<le> L"
    and Kc: "closed K" and sub: "cball y\<^sub>0 rB \<subseteq> K"
    and xy: "x \<noteq> y\<^sub>0" and xin: "norm (x - y\<^sub>0) < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and mk: "CARD('n) - k \<le> m - 1" and m2: "2 \<le> m"
    and xfix: "projmat b m *v (x - y\<^sub>0) = x - y\<^sub>0"
    and cc0: "0 < cc" and ccT: "cc < T"
    and ccdf: "cc < (rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (real m - 1)"
    and vlow: "\<And>w. w \<in> ball y\<^sub>0 rB \<Longrightarrow> \<beta> \<le> enn2real (exit_val k L T K w)"
  shows "ennreal (cc + min \<beta> (T - cc)) \<le> exit_val k L T K x"
proof -
  define \<rho>\<^sub>0 where "\<rho>\<^sub>0 = norm (x - y\<^sub>0)"
  define \<rho> where "\<rho> = \<rho>\<^sub>0 / 2"
  define cn where "cn = real m - 1"
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2) / cn"
  let ?RO = "{w :: real^'n. \<rho> < norm (projmat b m *v (w - y\<^sub>0))} \<inter> ball y\<^sub>0 rB"
  have r00: "0 < \<rho>\<^sub>0" unfolding \<rho>\<^sub>0_def using xy by simp
  have rho0: "0 < \<rho>" unfolding \<rho>_def using r00 by simp
  have cn0: "0 < cn" unfolding cn_def using m2 by simp
  have rr: "\<rho>\<^sub>0 < rB" using xin unfolding \<rho>\<^sub>0_def .
  have rB0: "0 < rB" using r00 rr by linarith
  have ccdf': "cc < \<delta>f" using ccdf unfolding \<delta>f_def cn_def \<rho>\<^sub>0_def .
  have cc0': "0 \<le> cc" using cc0 by linarith
  have shc: "continuous_on UNIV (\<lambda>z :: real^'n. z - y\<^sub>0)"
    by (intro continuous_intros)
  have mvc: "continuous_on UNIV (\<lambda>w :: real^'n. projmat b m *v (w - y\<^sub>0))"
    by (rule continuous_on_compose2[OF _ shc, of UNIV])
      (simp_all add: linear_continuous_on linear_linear)
  have Fpc: "continuous_on UNIV (\<lambda>w :: real^'n. (norm (projmat b m *v (w - y\<^sub>0)))\<^sup>2)"
    by (intro continuous_intros mvc)
  have Fnc: "continuous_on UNIV (\<lambda>w :: real^'n. (norm (w - y\<^sub>0))\<^sup>2)"
    by (intro continuous_intros)
  obtain P where P: "P \<in> exit_class k L T x"
    and AEg: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<longrightarrow>
      (norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)
        \<and> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * (real m - 1)"
    using subspace_tangential_exact_growth[OF T0 L1 rho0 orth mk xfix, where rB = rB]
    by blast
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF P])
  have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have start: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule covariation_class_start[OF P[unfolded exit_class_eq_covariation]])
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  have AEfun: "AE \<omega> in P. cc + min \<beta> (T - cc)
      \<le> pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0)"
    using AEg start sp
  proof (eventually_elim)
    case (elim \<omega>)
    have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using elim(3) by (simp add: spaceP)
    have x0: "fst (\<omega> 0) = x" using elim(2) by blast
    have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      by (rule path_sets_fst_continuous[OF setsP])
        (use elim(3) in simp)
    have growp: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (projmat b m *v (fst (\<omega> t) - y\<^sub>0)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + t * cn"
      unfolding cn_def \<rho>\<^sub>0_def using elim(1) by blast
    have grown: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + t * cn"
      unfolding cn_def \<rho>\<^sub>0_def using elim(1) by blast
    have xRO: "x \<in> ?RO"
      using rho0 rr r00 xfix unfolding \<rho>_def \<rho>\<^sub>0_def
      by (auto simp: dist_norm norm_minus_commute)
    have ROopen: "open ?RO"
    proof -
      have "open {w :: real^'n. \<rho> < norm (projmat b m *v (w - y\<^sub>0))}"
        by (rule open_Collect_less[OF continuous_on_const continuous_on_norm[OF mvc]])
      then show ?thesis by (intro open_Int open_ball)
    qed
    have contc: "continuous_on {0..cc} (\<lambda>t. fst (\<omega> t))"
      by (rule continuous_on_subset[OF cont]) (use ccT in auto)
    \<comment> \<open>the path stays in the annulus strictly before \<open>cc\<close>\<close>
    have IN: "fst (\<omega> s) \<in> ?RO" if s0: "0 \<le> s" and sc: "s < cc" for s
    proof -
      define e where "e = pexit cc ?RO (\<lambda>t. fst (\<omega> t))"
      have eup: "e \<le> cc" unfolding e_def by (rule pexit_le_T[OF cc0'])
      have before: "fst (\<omega> u) \<in> ?RO"
        if u0: "0 \<le> u" and ue: "u < e" for u
      proof (rule ccontr)
        assume nb: "fst (\<omega> u) \<notin> ?RO"
        have uc: "u \<le> cc" using ue eup by linarith
        have "pexit cc ?RO (\<lambda>t. fst (\<omega> t)) \<le> u"
          by (rule pexit_le_of_mem[OF cc0' u0 uc]) (use nb in simp)
        then show False using ue unfolding e_def by linarith
      qed
      have ecc: "e = cc"
      proof (rule ccontr)
        assume "e \<noteq> cc"
        then have elt: "e < cc" using eup by linarith
        have Xe: "fst (\<omega> e) \<notin> ?RO"
          using pexit_mem_of_less_T[OF cc0' ROopen contc]
          using elt unfolding e_def by simp
        have e0': "0 < e"
        proof (rule ccontr)
          assume "\<not> 0 < e"
          moreover have "0 \<le> e"
            unfolding e_def by (rule pexit_nonneg[OF cc0'])
          ultimately have "e = 0" by linarith
          then show False using Xe x0 xRO by simp
        qed
        have eT': "e \<le> T" using elt ccT by linarith
        have esqp: "(norm (projmat b m *v (fst (\<omega> e) - y\<^sub>0)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + e * cn"
          by (rule radial_sq_upto_gen[OF wm Fpc growp e0' eT' before])
        have esqn: "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + e * cn"
          by (rule radial_sq_upto_gen[OF wm Fnc grown e0' eT' before])
        have dichot: "norm (projmat b m *v (fst (\<omega> e) - y\<^sub>0)) \<le> \<rho>
            \<or> rB \<le> norm (fst (\<omega> e) - y\<^sub>0)"
          using Xe by (auto simp: dist_norm norm_minus_commute)
        show False
        proof (cases rule: disjE[OF dichot])
          case 1
          have "(norm (projmat b m *v (fst (\<omega> e) - y\<^sub>0)))\<^sup>2 \<le> \<rho>\<^sup>2"
            using 1 rho0 by (intro power_mono) simp_all
          moreover have "\<rho>\<^sup>2 < \<rho>\<^sub>0\<^sup>2"
            unfolding \<rho>_def using r00 by (simp add: power_divide)
          moreover have "\<rho>\<^sub>0\<^sup>2 \<le> (norm (projmat b m *v (fst (\<omega> e) - y\<^sub>0)))\<^sup>2"
            unfolding esqp using e0' cn0 by simp
          ultimately show False by linarith
        next
          case 2
          have "rB\<^sup>2 \<le> (norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2"
            using 2 rB0 by (intro power_mono) simp_all
          then have "rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2 \<le> e * cn" unfolding esqn by linarith
          then have "\<delta>f \<le> e"
            unfolding \<delta>f_def using cn0 by (simp add: pos_divide_le_eq)
          then show False using elt ccdf' by linarith
        qed
      qed
      show ?thesis using before[OF s0] sc unfolding ecc by simp
    qed
    \<comment> \<open>hence in the ball through \<open>cc\<close>, including the endpoint\<close>
    have inB: "fst (\<omega> s) \<in> ball y\<^sub>0 rB"
      if s0: "0 \<le> s" and sc: "s \<le> cc" for s
    proof (cases "s < cc")
      case True
      show ?thesis using IN[OF s0 True] by blast
    next
      case False
      then have seq: "s = cc" using sc by linarith
      have csq: "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + cc * cn"
      proof (rule radial_sq_upto_gen[OF wm Fnc grown cc0])
        show "cc \<le> T" using ccT by linarith
        show "\<And>s. 0 \<le> s \<Longrightarrow> s < cc \<Longrightarrow> fst (\<omega> s) \<in> ?RO" by (rule IN)
      qed
      have "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2 < rB\<^sup>2"
      proof -
        have "cc * cn < \<delta>f * cn"
          using ccdf' cn0 by (intro mult_strict_right_mono)
        also have "\<delta>f * cn = rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2"
          unfolding \<delta>f_def using cn0 by simp
        finally show ?thesis unfolding csq by linarith
      qed
      then have "norm (fst (\<omega> cc) - y\<^sub>0) < rB"
        using rB0 by (metis power2_le_imp_le linorder_not_less nless_le)
      then show ?thesis unfolding seq by (simp add: dist_norm norm_minus_commute)
    qed
    have inK: "fst (\<omega> s) \<in> K" if s0: "0 \<le> s" and sc: "s \<le> cc" for s
      using inB[OF s0 sc] sub ball_subset_cball by blast
    have pex: "pexit cc K (\<lambda>t. fst (\<omega> t)) = cc"
      by (rule pexit_eq_of_stays[OF cc0']) (use inK in simp)
    have XccK: "fst (\<omega> cc) \<in> K" using inK[of cc] cc0 by simp
    have XccB: "fst (\<omega> cc) \<in> ball y\<^sub>0 rB" using inB[of cc] cc0 by simp
    have cap: "enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))
        = min (enn2real (exit_val k L T K (fst (\<omega> cc)))) (T - cc)"
      by (rule enn2real_paper_v_horizon_cap[OF _ _ L1 Kc]) (use ccT cc0 in auto)
    show ?case
      using pex XccK cap vlow[OF XccB] by (simp add: min_def)
  qed
  show ?thesis
    by (rule exit_val_dpp_ge_const_time[OF _ L1 Kc
          path_stopping_time_const[OF cc0' less_imp_le[OF ccT]] borel_measurable_const P AEfun])
      (use cc0 ccT in linarith)
qed

text \<open>With \<open>m = CARD('n)\<close> the projector is the identity, the field is
  sphere-tangential and the rate is \<open>CARD('n) - 1\<close>; at
  \<open>cc = min (T/2) (\<delta>/2)\<close> this is the (non-sharp) ball bound that the
  dichotomy of Case 2 uses.\<close>

theorem exit_val_ball_lower_plus:
  fixes K :: "(real^'n::finite) set" and y\<^sub>0 x :: "real^'n"
    and rB T \<beta> :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and Kc: "closed K" and sub: "cball y\<^sub>0 rB \<subseteq> K"
    and xy: "x \<noteq> y\<^sub>0" and xin: "norm (x - y\<^sub>0) < rB"
    and b0: "0 \<le> \<beta>"
    and vlow: "\<And>w. w \<in> ball y\<^sub>0 rB \<Longrightarrow>
      \<beta> \<le> enn2real (exit_val k L T K w)"
  shows "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min \<beta> (T / 2))
      \<le> exit_val k L T K x"
proof -
  define D where "D = rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2"
  define cc where "cc = min (T / 2) (D / (2 * (real CARD('n) - 1)))"
  have uu: "sgn (x - y\<^sub>0) \<bullet> sgn (x - y\<^sub>0) = 1"
    using xy by (simp add: dot_square_norm norm_sgn)
  obtain bb :: "nat \<Rightarrow> real^'n"
    where orth: "\<forall>i < CARD('n). \<forall>j < CARD('n). bb i \<bullet> bb j = (if i = j then 1 else 0)"
    using orthonormal_family_containing[OF uu order.refl] by auto
  have orth': "\<And>i j. i < CARD('n) \<Longrightarrow> j < CARD('n) \<Longrightarrow>
      bb i \<bullet> bb j = (if i = j then 1 else 0)"
    using orth by blast
  have cn0: "0 < real CARD('n) - 1" using k1 kn by linarith
  have D0: "0 < D"
    unfolding D_def using xin by (intro diff_gt_0_iff_gt[THEN iffD2] power_strict_mono) auto
  have cc0: "0 < cc" unfolding cc_def using T0 D0 cn0 by simp
  have ccT: "cc < T" unfolding cc_def using T0 by simp
  have "D / (2 * (real CARD('n) - 1)) < D / (real CARD('n) - 1)"
    using D0 cn0 by (intro divide_strict_left_mono) auto
  then have ccdf: "cc < D / (real CARD('n) - 1)"
    unfolding cc_def by (rule le_less_trans[OF min.cobounded2])
  have main: "ennreal (cc + min \<beta> (T - cc)) \<le> exit_val k L T K x"
    by (rule exit_val_ball_lower_gen[OF T0 L1 Kc sub xy xin orth' _ _
          projmat_full_id[OF orth'] cc0 ccT ccdf[unfolded D_def] vlow])
      (use k1 kn in auto)
  have ccT2: "cc \<le> T / 2" unfolding cc_def by (rule min.cobounded1)
  have le: "ennreal (cc + min \<beta> (T / 2)) \<le> ennreal (cc + min \<beta> (T - cc))"
    using ccT2 by (intro ennreal_leI add_left_mono min.mono) simp_all
  show ?thesis using order_trans[OF le main] unfolding cc_def D_def .
qed


(*<*)
end
(*>*)
