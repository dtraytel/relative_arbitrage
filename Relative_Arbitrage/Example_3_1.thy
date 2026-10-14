section \<open>Example 3.1: the value function on a ball\<close>

(*<*)
theory Example_3_1
  imports
    Value_Function_Tangential_Field Exit_Class_Infinite
begin

(*>*)

text \<open>Example 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>: on the ball of radius \<open>r\<close>
  the value function is \<open>max ((r\<^sup>2 - |x|\<^sup>2)/(n - k)) 0\<close>.  The lower bound
  inside the ball comes from the subspace-tangential member of the class,
  which grows the squared distance to the centre at the deterministic rate
  \<open>m - 1\<close>; the upper bound and the other cases from the bounds of the
  value function already proved.  The closed form is proved for an abstract
  constraint set, for the paper's set at a horizon past \<open>r\<^sup>2/(n - k)\<close>, and
  for the value function of Eq. (1.6) on the half-line.\<close>

subsection \<open>The sharp ball lower bound at rate \<open>m - 1\<close>\<close>

text \<open>For any closed convex \<open>S\<close> with bounds \<open>B\<close>, \<open>D\<close> that contains the
  tangential rates of the subspace \<open>span (b ` {..<m})\<close>, the value at a point
  of that subspace is at least the deterministic time the tangential member
  needs to reach the sphere.  The paper's set contains them for
  \<open>m \<ge> n - k + 1\<close> (@{thm [source] tanpU_sq_sconstraint}).\<close>

theorem covariation_val_ball_lower_subspace:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T cc :: real
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and tan: "\<And>u. norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
    and cc0: "0 < cc" and ccT: "cc < T"
    and ccdf: "cc < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  shows "ennreal cc \<le> covariation_val S T K x"
proof -
  have "ennreal (cc + min 0 (T - cc)) \<le> covariation_val S T K x"
    by (rule covariation_val_ball_lower_gen[where y\<^sub>0 = 0 and \<beta> = 0,
          OF T0 B0 B D0 D Sc Sv tan Kc sub xnz _ orth m2 _ cc0 ccT])
      (use xin xfix ccdf in simp_all)
  then show ?thesis using ccT by simp
qed

text \<open>Letting \<open>cc \<longrightarrow> min T \<delta>\<close> removes the last slack.  This is the sharp
  interior lower bound Example 3.1 asks for: at rate \<open>m - 1\<close>, with no factor
  \<open>2\<close> and no \<open>T/2\<close> cap.\<close>

corollary covariation_val_ball_lower_sharp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T :: real
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and tan: "\<And>u. norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
  shows "ennreal (min T ((rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)))
      \<le> covariation_val S T K x"
proof -
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  define c0 where "c0 = min T \<delta>f"
  have r00: "0 < norm x" using xnz by simp
  have rB0: "0 < rB" using r00 xin by linarith
  have cn0: "0 < real m - 1"
  proof -
    have "(2::real) \<le> real m"
      using m2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis by linarith
  qed
  have sq_lt: "(norm x)\<^sup>2 < rB\<^sup>2"
    using r00 xin by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have c00: "0 < c0" unfolding c0_def using T0 df0 by simp
  define ccs where "ccs = (\<lambda>j :: nat. c0 - c0 / (2 * real (Suc j)))"
  have ccl: "0 < ccs j" for j
  proof -
    have "c0 / (2 * real (Suc j)) \<le> c0 / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> c0" using c00 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding ccs_def using c00 by linarith
  qed
  have ccu: "ccs j < c0" for j
  proof -
    have "0 < c0 / (2 * real (Suc j))" using c00 by simp
    then show ?thesis unfolding ccs_def by linarith
  qed
  have lim: "ccs \<longlonglongrightarrow> c0"
  proof -
    have eq: "(\<lambda>j. (c0 / 2) * inverse (real (Suc j)))
        = (\<lambda>j. c0 / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (c0 / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (c0 / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. c0 / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. c0 - c0 / (2 * real (Suc j))) \<longlonglongrightarrow> c0 - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding ccs_def by simp
  qed
  have le: "ennreal (ccs j) \<le> covariation_val S T K x" for j
  proof -
    have cT: "ccs j < T" using ccu[of j] unfolding c0_def by simp
    have cd: "ccs j < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
      using ccu[of j] unfolding c0_def \<delta>f_def[symmetric] by simp
    show ?thesis
      by (rule covariation_val_ball_lower_subspace[OF T0 B0 B D0 D Sc Sv tan Kc sub xnz xin orth
            m2 xfix ccl cT cd])
  qed
  have "(\<lambda>j. ennreal (ccs j)) \<longlonglongrightarrow> ennreal c0"
    by (rule tendsto_ennrealI[OF lim])
  then have "ennreal c0 \<le> covariation_val S T K x"
    by (rule tendsto_upperbound) (use le in auto)
  then show ?thesis unfolding c0_def \<delta>f_def .
qed

subsection \<open>Example 3.1 from the interior lower bound\<close>

text \<open>Everything of Example 3.1 except the interior lower bound at nonzero
  points.  Four cases: outside the ball the value is \<open>0\<close>, since a path starting
  outside \<open>K\<close> has exit time \<open>0\<close> (\<open>covariation_val_zero_outside\<close>); on the sphere,
  \<open>covariation_val_boundary_zero\<close>; strictly inside and nonzero, the hypothesis against
  \<open>covariation_val_le_ball_bound\<close>; and at the centre by upper semicontinuity, rather
  than by running the tangential field from \<open>0\<close>, where the clamp sits.\<close>

lemma covariation_val_ball_upper:
  fixes r :: real and y :: "real^'n::finite"
  assumes T0: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
  shows "enn2real (covariation_val S T (cball 0 r) y) \<le> max ((r * r - y \<bullet> y) / \<theta>) 0"
proof -
  have le: "covariation_val S T (cball 0 r) y \<le> ennreal ((r * r - y \<bullet> y) / \<theta>)"
    by (rule covariation_val_le_ball_bound[OF T0 B0 B th0 th order_refl])
  have "enn2real (covariation_val S T (cball 0 r) y)
      \<le> enn2real (ennreal ((r * r - y \<bullet> y) / \<theta>))"
    by (rule enn2real_mono[OF le]) simp
  also have "\<dots> \<le> max ((r * r - y \<bullet> y) / \<theta>) 0"
    by (cases "0 \<le> (r * r - y \<bullet> y) / \<theta>")
      (simp_all add: ennreal_neg)
  finally show ?thesis .
qed

theorem example_3_1_from_lower:
  fixes r :: real and x :: "real^'n::finite" and \<sigma> :: "real^'n^'n"
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and r0: "0 < r"
    and lower: "\<And>y :: real^'n. norm y < r \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
        (r * r - y \<bullet> y) / \<theta>
          \<le> enn2real (covariation_val S T (cball 0 r) y)"
  shows "enn2real (covariation_val S T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / \<theta>) 0"
proof -
  have nk0: "0 < \<theta>" by (rule th0)
  have T0': "0 \<le> T" using T0 by simp
  have ne: "covariation_class S T (0 :: real^'n) \<noteq> {}"
    by (rule covariation_class_nonempty[OF T0' Sc SST])
  have fin: "covariation_val S T (cball 0 r) y < \<top>" for y
    using covariation_val_neq_top[OF T0'] by (simp add: less_top)
  have Kc: "closed (cball (0 :: real^'n) r)" by simp
  have sq: "y \<bullet> y = norm y * norm y" for y :: "real^'n"
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  have upper: "enn2real (covariation_val S T (cball 0 r) y)
      \<le> max ((r * r - y \<bullet> y) / \<theta>) 0" for y :: "real^'n"
    by (rule covariation_val_ball_upper[OF T0' B0 B th0 th])
  consider (out) "r < norm x" | (sph) "norm x = r"
    | (inn) "norm x < r" "x \<noteq> 0" | (ctr) "x = 0"
    by (cases "r < norm x", simp) (cases "norm x = r", simp, cases "x = 0", auto)
  then show ?thesis
  proof cases
    case out
    then have "x \<notin> cball (0 :: real^'n) r" by simp
    then have z: "covariation_val S T (cball 0 r) x = 0"
      by (rule covariation_val_zero_outside[OF T0'])
    have "r * r < norm x * norm x"
      by (rule mult_strict_mono) (use out r0 in auto)
    then have "(r * r - x \<bullet> x) / \<theta> < 0"
      unfolding sq using nk0 by (simp add: divide_neg_pos)
    then show ?thesis unfolding z by simp
  next
    case sph
    have z: "covariation_val S T (cball 0 r) x = 0"
      by (rule covariation_val_boundary_zero[OF T0 B0 B th0 th sph])
    have "x \<bullet> x = r * r" unfolding sq sph by (rule refl)
    then show ?thesis unfolding z by simp
  next
    case inn
    have nn: "0 \<le> (r * r - x \<bullet> x) / \<theta>"
    proof -
      have "norm x * norm x \<le> r * r"
        by (rule mult_mono) (use inn(1) r0 in auto)
      then show ?thesis unfolding sq using nk0 by simp
    qed
    have "(r * r - x \<bullet> x) / \<theta>
        \<le> enn2real (covariation_val S T (cball 0 r) x)"
      by (rule lower[OF inn(1) inn(2)])
    with upper[of x] nn show ?thesis by simp
  next
    case ctr
    define nk where "nk = \<theta>"
    have nkp: "0 < nk" unfolding nk_def by (rule th0)
    have lower': "\<And>y :: real^'n. norm y < r \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
        (r * r - y \<bullet> y) / nk \<le> enn2real (covariation_val S T (cball 0 r) y)"
      unfolding nk_def by (rule lower)
    have upper': "enn2real (covariation_val S T (cball 0 r) y)
        \<le> max ((r * r - y \<bullet> y) / nk) 0" for y :: "real^'n"
      unfolding nk_def by (rule upper)
    have goalR: "max ((r * r - x \<bullet> x) / nk) 0 = r * r / nk"
      unfolding ctr using nkp r0 by simp
    have le: "enn2real (covariation_val S T (cball 0 r) x) \<le> r * r / nk"
      using upper'[of x] goalR by simp
    have ge: "r * r / nk \<le> enn2real (covariation_val S T (cball 0 r) x)"
    proof (rule ccontr)
      assume "\<not> r * r / nk \<le> enn2real (covariation_val S T (cball 0 r) x)"
      then have lt0: "enn2real (covariation_val S T (cball 0 r) x) < r * r / nk"
        by simp
      define b where "b = (enn2real (covariation_val S T (cball 0 r) x)
          + r * r / nk) / 2"
      have b2: "2 * b = enn2real (covariation_val S T (cball 0 r) x) + r * r / nk"
        unfolding b_def by simp
      have blo: "enn2real (covariation_val S T (cball 0 r) x) < b" using lt0 b2 by linarith
      have bhi: "b < r * r / nk" using lt0 b2 by linarith
      have ltb: "covariation_val S T (cball 0 r) x < ennreal b"
        using blo fin[of x] by simp
      have "eventually (\<lambda>y. covariation_val S T (cball 0 r) y < ennreal b) (nhds x)"
        by (rule covariation_val_usc[OF T0 B0 B D0 D Sc Kc ne ltb])
      then obtain U where opU: "open U" and xU: "x \<in> U"
        and Uy: "\<And>y. y \<in> U \<Longrightarrow> covariation_val S T (cball 0 r) y < ennreal b"
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
      have vylt: "enn2real (covariation_val S T (cball 0 r) y) < b"
        using Uy[OF yU] fin[of y]
        by simp
      have "(r * r - y \<bullet> y) / nk \<le> enn2real (covariation_val S T (cball 0 r) y)"
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
  subspace-tangential member of @{thm [source] covariation_val_ball_lower_sharp} inside
  \<open>V\<close>.  Its growth rate is \<open>dim V - 1 = CARD('n) - k\<close>, the constant of (3.1).

  The hypothesis \<open>r\<^sup>2/(CARD('n) - k) \<le> T\<close> says only that the horizon does not
  bind: the value function of a finite-horizon problem is capped by its horizon
  (@{thm [source] enn2real_covariation_val_horizon_cap}), so without it the identity
  would fail at the centre.\<close>

theorem covariation_val_example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and m2: "2 \<le> m" and mn: "m \<le> CARD('n)"
    and tan: "\<And>b u. (\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)) \<Longrightarrow>
      norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> real m - 1 \<le> trace a"
    and r0: "0 < r"
    and Tbig: "r * r / (real m - 1) \<le> T"
  shows "enn2real (covariation_val S T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / (real m - 1)) 0"
proof -
  have m0: "0 < m" using m2 by simp
  have cn0: "0 < real m - 1"
  proof -
    have "(2::real) \<le> real m" using m2 by simp
    then show ?thesis by linarith
  qed
  obtain i :: 'n where True by blast
  have u0: "axis i (1::real) \<bullet> axis i 1 = 1" by simp
  obtain bb :: "nat \<Rightarrow> real^'n"
    where orth0: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> bb i \<bullet> bb j = (if i = j then 1 else 0)"
    using orthonormal_family_containing[OF u0 mn m0] by blast
  have SST: "tanpU (projmat bb m) 0 ** transpose (tanpU (projmat bb m) 0) \<in> S"
    by (rule tan[OF orth0]) simp_all
  have lower: "(r * r - y \<bullet> y) / (real m - 1) \<le> enn2real (covariation_val S T (cball 0 r) y)"
    if ylt: "norm y < r" and ynz: "y \<noteq> 0" for y :: "real^'n"
  proof -
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
        by (rule matrix_vector_mult_scaleR)
      also have "\<dots> = norm y *\<^sub>R b 0"
        by (simp add: projmat_fix[OF orth m0])
      also have "\<dots> = y" by (rule yb[symmetric])
      finally show ?thesis .
    qed
    have Kc: "closed (cball (0 :: real^'n) r)" by simp
    have sub: "cball (0 :: real^'n) r \<subseteq> cball 0 r" by simp
    have tanb: "\<And>u. norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
        tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
      by (rule tan[OF orth])
    have bound: "ennreal (min T ((r\<^sup>2 - (norm y)\<^sup>2) / (real m - 1)))
        \<le> covariation_val S T (cball 0 r) y"
      by (rule covariation_val_ball_lower_sharp[OF T0 B0 B D0 D Sc Sv tanb Kc sub ynz ylt orth m2 yfix])
    have sq: "(norm y)\<^sup>2 = y \<bullet> y" by (simp add: dot_square_norm)
    have rsq: "r\<^sup>2 = r * r" by (simp add: power2_eq_square)
    have nn: "0 \<le> (r * r - y \<bullet> y) / (real m - 1)"
    proof -
      have "norm y * norm y \<le> r * r"
        by (rule mult_mono) (use ylt r0 in auto)
      then have "y \<bullet> y \<le> r * r"
        unfolding sq[symmetric] by (simp add: power2_eq_square)
      then show ?thesis using cn0 by simp
    qed
    have dle: "(r * r - y \<bullet> y) / (real m - 1) \<le> T"
    proof -
      have "(r * r - y \<bullet> y) / (real m - 1)
          \<le> (r * r) / (real m - 1)"
        using cn0 by (intro divide_right_mono) simp_all
      then show ?thesis using Tbig by (rule order_trans)  qed
    have mineq: "min T ((r * r - y \<bullet> y) / (real m - 1))
        = (r * r - y \<bullet> y) / (real m - 1)"
      using dle by simp
    have bound': "ennreal ((r * r - y \<bullet> y) / (real m - 1))
        \<le> covariation_val S T (cball 0 r) y"
      using bound unfolding sq rsq mineq .
    have fin: "covariation_val S T (cball 0 r) y < \<top>"
      using covariation_val_neq_top[of T] T0 by (simp add: less_top)
    have "enn2real (ennreal ((r * r - y \<bullet> y) / (real m - 1)))
        \<le> enn2real (covariation_val S T (cball 0 r) y)"
      by (rule enn2real_mono[OF bound' fin])
    then show ?thesis
      unfolding enn2real_ennreal[OF nn] .
  qed
  show ?thesis
    by (rule example_3_1_from_lower[OF T0 B0 B D0 D Sc SST cn0 th r0 lower])
qed

text \<open>The paper's set: \<open>m = n - k + 1\<close>, whose tangential rates lie in
  \<open>sconstraint k L\<close> (@{thm [source] tanpU_sq_sconstraint}) and whose rate
  \<open>m - 1 = n - k\<close> is the least trace there (@{thm [source] sconstraint_trace_ge}).\<close>

theorem example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and T0: "0 < T" and r0: "0 < r"
    and Tbig: "r * r / real (CARD('n) - k) \<le> T"
  shows "enn2real (exit_val k L T (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof -
  define m where "m = CARD('n) - k + 1"
  have m2: "2 \<le> m" unfolding m_def using kn by simp
  have mn: "m \<le> CARD('n)" unfolding m_def using k1 kn by simp
  have mk: "CARD('n) - k \<le> m - 1" unfolding m_def by simp
  have cn: "real m - 1 = real (CARD('n) - k)" unfolding m_def by simp
  have th: "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> real m - 1 \<le> trace a"
    unfolding cn by (rule sconstraint_trace_ge[OF kn])
  have Tbig': "r * r / (real m - 1) \<le> T" unfolding cn by (rule Tbig)
  show ?thesis
    unfolding exit_val_eq_covariation_val cn[symmetric]
    by (rule covariation_val_example_3_1[OF T0 sconstraint_bounds[OF order_trans[OF zero_le_one L1]]
          closed_sconstraint sconstraint_convex m2 mn tanpU_sq_sconstraint[OF _ _ _ mk L1] th r0 Tbig'])
qed

subsection \<open>Example 3.1 on the half-line\<close>

text \<open>\<^bold>\<open>Example 3.1\<close>, in closed form and with no horizon left in it, for the
  same abstract \<open>S\<close>.\<close>

theorem icovariation_val_example_3_1:
  fixes r :: real and x :: "real^'n::finite"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and m2: "2 \<le> m" and mn: "m \<le> CARD('n)"
    and tan: "\<And>b u. (\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)) \<Longrightarrow>
      norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> real m - 1 \<le> trace a"
    and r0: "0 < r"
  shows "enn2real (icovariation_val S (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / (real m - 1)) 0"
proof -
  have m0: "0 < m" using m2 by simp
  have cn0: "0 < real m - 1"
  proof -
    have "(2::real) \<le> real m" using m2 by simp
    then show ?thesis by linarith
  qed
  obtain i :: 'n where True by blast
  have u0: "axis i (1::real) \<bullet> axis i 1 = 1" by simp
  obtain bb :: "nat \<Rightarrow> real^'n"
    where orth0: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> bb i \<bullet> bb j = (if i = j then 1 else 0)"
    using orthonormal_family_containing[OF u0 mn m0] by blast
  have SST: "tanpU (projmat bb m) 0 ** transpose (tanpU (projmat bb m) 0) \<in> S"
    by (rule tan[OF orth0]) simp_all
  obtain T where T0: "0 < T" and T1: "r * r / (real m - 1) < T"
    and T2: "2 * (r * r) / (real m - 1) < T"
    and eq: "icovariation_val S (cball (0 :: real^'n) r) = covariation_val S T (cball 0 r)"
    by (rule icovariation_val_eq_covariation_val_horizon[OF Sc Sv SST B0 B cn0 th closed_cball
          subset_refl])
  show ?thesis unfolding eq
    by (rule covariation_val_example_3_1[OF T0 B0 B D0 D Sc Sv m2 mn tan th r0 less_imp_le[OF T1]])
qed

text \<open>For the paper's set it is the finite-horizon Example 3.1 at a horizon past
  \<open>r\<^sup>2/(n-k)\<close>.\<close>

theorem example_3_1_uncapped:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L: "1 \<le> L" and r0: "0 < r"
  shows "enn2real (iexit_val k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
proof -
  obtain T :: real where T0: "0 < T"
    and T1: "r * r / real (CARD('n) - k) < T" and "2 * (r * r) / real (CARD('n) - k) < T"
    and eq: "iexit_val k L (cball (0 :: real^'n) r) = exit_val k L T (cball 0 r)"
    by (rule iexit_val_eq_exit_val_horizon[where rK = r, OF kn L closed_cball subset_refl])
  show ?thesis unfolding eq
    by (rule example_3_1[OF k1 kn L T0 r0 less_imp_le[OF T1]])
qed

(*<*)
end
(*>*)
