section \<open>From dyadic moduli to a H\"older bound\<close>

(*<*)
theory Holder_Interpolation
  imports Modulus_Tails
begin

(*>*)

text \<open>
  The bridge from \<open>modulus_of_good_path\<close> (@{theory Continuous_Path_Spaces.Modulus_Tails}) to the compact
  H\"older balls of \<open>Path_Space\<close>: a path whose modulus at every dyadic scale
  \<open>1/2^m\<close>, \<open>m \<ge> n\<close>, is bounded by \<open>E * 2 powr (-g m)\<close> satisfies a global
  H\"older-\<open>g\<close> bound with a constant explicit in \<open>(E, g, n, T)\<close>. Small gaps use
  the matching dyadic level; large gaps telescope over an arithmetic grid of
  mesh below \<open>1/2^n\<close>.
\<close>
subsection \<open>The matching dyadic level of a small gap\<close>

lemma exists_dyadic_level:
  fixes d :: real
  assumes d0: "0 < d" and dn: "d < 1 / 2 ^ n"
  obtains m where "n \<le> m" and "1 / 2 ^ Suc m \<le> d" and "d < 1 / 2 ^ m"
proof -
  have ex: "\<exists>k. 1 / 2 ^ Suc k \<le> d"
  proof -
    obtain B where B: "((1::real)/2) ^ B < d"
      using reals_power_lt_ex[OF d0, of "2"] by auto
    have h: "(2::real) ^ B \<le> 2 ^ Suc B" by simp
    have "(1::real) / 2 ^ Suc B \<le> 1 / 2 ^ B"
      using h by (intro divide_left_mono) simp_all
    hence "(1::real) / 2 ^ Suc B \<le> (1/2) ^ B"
      by (simp add: power_one_over)
    with B show ?thesis by (intro exI[of _ B]) linarith
  qed
  define m where "m = (LEAST k. 1 / 2 ^ Suc k \<le> d)"
  have Sm: "1 / 2 ^ Suc m \<le> d"
    unfolding m_def by (rule LeastI_ex[OF ex])
  have not_below: "\<not> 1 / 2 ^ Suc k \<le> d" if "k < m" for k
    unfolding m_def by (rule not_less_Least[OF that[unfolded m_def]])
  have hi: "d < 1 / 2 ^ m"
  proof (cases m)
    case 0
    have "d < 1 / 2 ^ n" by (rule dn)
    also have "1 / 2 ^ n \<le> (1::real)" by simp
    finally show ?thesis unfolding 0 by simp
  next
    case (Suc m')
    have "\<not> 1 / 2 ^ Suc m' \<le> d"
      by (rule not_below) (simp add: Suc)
    thus ?thesis unfolding Suc by simp
  qed
  have nm: "n \<le> m"
  proof (rule ccontr)
    assume "\<not> n \<le> m"
    hence "Suc m \<le> n" by simp
    hence h2: "(2::real) ^ Suc m \<le> 2 ^ n"
      by (intro power_increasing) simp_all
    hence "(1::real) / 2 ^ n \<le> 1 / 2 ^ Suc m"
      by (intro divide_left_mono) simp_all
    with Sm dn show False by linarith
  qed
  show thesis by (rule that[OF nm Sm hi])
qed

subsection \<open>Telescoping over an arithmetic grid\<close>

lemma telescope_grid:
  fixes f :: "real \<Rightarrow> real" and u v :: real and N :: nat
  assumes N: "0 < N"
    and per: "\<And>i. i < N \<Longrightarrow>
      \<bar>f (u + real (Suc i) * (v - u) / real N)
         - f (u + real i * (v - u) / real N)\<bar> \<le> b"
  shows "\<bar>f v - f u\<bar> \<le> real N * b"
proof -
  define p where "p = (\<lambda>i. f (u + real i * (v - u) / real N))"
  have p0: "p 0 = f u" unfolding p_def by simp
  have pN: "p N = f v"
  proof -
    have "u + real N * (v - u) / real N = v" using N by simp
    thus ?thesis unfolding p_def by simp
  qed
  have tel: "(\<Sum>i<N. p (Suc i) - p i) = p N - p 0"
    by (rule sum_lessThan_telescope)
  have "\<bar>f v - f u\<bar> = \<bar>\<Sum>i<N. p (Suc i) - p i\<bar>"
    unfolding tel p0 pN by (rule refl)
  also have "\<dots> \<le> (\<Sum>i<N. \<bar>p (Suc i) - p i\<bar>)"
    by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>i<N. b)"
  proof (rule sum_mono)
    fix i assume "i \<in> {..<N}"
    thus "\<bar>p (Suc i) - p i\<bar> \<le> b" unfolding p_def by (intro per) simp
  qed
  also have "\<dots> = real N * b" by simp
  finally show ?thesis .
qed

subsection \<open>The interpolation theorem\<close>

theorem holder_of_dyadic_moduli:
  fixes f :: "real \<Rightarrow> real" and T E g :: real and n :: nat
  assumes T: "0 \<le> T" and g0: "0 < g" and g1: "g \<le> 1" and E0: "0 \<le> E"
    and H: "\<And>m u v. n \<le> m \<Longrightarrow> u \<in> {0..T} \<Longrightarrow> v \<in> {0..T} \<Longrightarrow>
              \<bar>u - v\<bar> < 1 / 2 ^ m \<Longrightarrow> \<bar>f u - f v\<bar> \<le> E * 2 powr (- g * real m)"
    and u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
  shows "\<bar>f u - f v\<bar>
      \<le> (E * 2 powr g
          + 2 * E * 2 ^ n * 2 powr (- g * real n) * max 1 (T powr (1 - g)))
         * \<bar>u - v\<bar> powr g"
    (is "_ \<le> ?c * _")
proof -
  have c2nn: "0 \<le> 2 * E * 2 ^ n * 2 powr (- g * real n) * max 1 (T powr (1 - g))"
    using E0 by (intro mult_nonneg_nonneg) simp_all
  have c1nn: "0 \<le> E * 2 powr g" using E0 by simp
  text \<open>The large-gap case, for an ordered pair.\<close>
  have main: "\<bar>f a - f b\<bar> \<le> ?c * \<bar>a - b\<bar> powr g"
    if ab1: "a \<le> b" and ab2: "a \<in> {0..T}" and ab3: "b \<in> {0..T}"
      and ab4: "1 / 2 ^ n \<le> b - a" for a b
  proof -
    define d where "d = b - a"
    have twon: "(0::real) < 1 / 2 ^ n" by simp
    have d0: "0 < d" unfolding d_def using ab4 twon by linarith
    have dT: "d \<le> T" unfolding d_def using ab2 ab3 by auto
    define N where "N = nat \<lfloor>d * 2 ^ n\<rfloor> + 1"
    have N1: "1 \<le> d * 2 ^ n"
    proof -
      have "(1 / 2 ^ n) * 2 ^ n \<le> d * 2 ^ n"
        using ab4 unfolding d_def by (intro mult_right_mono) simp_all
      thus ?thesis by simp
    qed
    have fl0: "0 \<le> \<lfloor>d * 2 ^ n\<rfloor>" using N1 by simp
    have rN: "real N = real_of_int \<lfloor>d * 2 ^ n\<rfloor> + 1"
      unfolding N_def using fl0 by simp
    have lt: "d * 2 ^ n < real_of_int \<lfloor>d * 2 ^ n\<rfloor> + 1"
      using floor_correct[of "d * 2 ^ n"] by simp
    have Nf: "d * 2 ^ n < real N" unfolding rN by (rule lt)
    have Nle: "real N \<le> 2 * (d * 2 ^ n)"
    proof -
      have "real_of_int \<lfloor>d * 2 ^ n\<rfloor> \<le> d * 2 ^ n" by (rule of_int_floor_le)
      with rN N1 show ?thesis by linarith
    qed
    have Npos: "0 < N" unfolding N_def by simp
    have rNpos: "0 < real N" using Npos by simp
    have mesh: "d / real N < 1 / 2 ^ n"
    proof -
      have h1: "d < real N / 2 ^ n"
        using divide_strict_right_mono[OF Nf, of "2 ^ n"] by simp
      have e: "1 / 2 ^ n * real N = real N / 2 ^ n" by simp
      have "d < 1 / 2 ^ n * real N" unfolding e by (rule h1)
      thus ?thesis by (simp add: pos_divide_less_eq[OF rNpos])
    qed
    have grid_mem: "a + real i * (b - a) / real N \<in> {0..T}" if "i \<le> N" for i
    proof -
      have nn: "0 \<le> real i * (b - a) / real N"
        unfolding d_def[symmetric]
        using d0 rNpos by (intro divide_nonneg_pos mult_nonneg_nonneg) simp_all
      have "real i * d \<le> real N * d"
        using that d0 by (intro mult_right_mono) simp_all
      hence "real i * d / real N \<le> real N * d / real N"
        by (intro divide_right_mono) simp_all
      hence ub: "real i * (b - a) / real N \<le> b - a"
        unfolding d_def[symmetric] using rNpos by simp
      show ?thesis using nn ub ab2 ab3 by auto
    qed
    have gap: "(a + real (Suc i) * (b - a) / real N)
        - (a + real i * (b - a) / real N) = d / real N" for i
    proof -
      have "(a + real (Suc i) * (b - a) / real N)
          - (a + real i * (b - a) / real N)
          = (real (Suc i) * (b - a) - real i * (b - a)) / real N"
        by (simp add: diff_divide_distrib)
      also have "real (Suc i) * (b - a) - real i * (b - a) = b - a"
        by (simp add: algebra_simps)
      finally show ?thesis unfolding d_def by simp
    qed
    have per: "\<bar>f (a + real (Suc i) * (b - a) / real N)
        - f (a + real i * (b - a) / real N)\<bar> \<le> E * 2 powr (- g * real n)"
      if i: "i < N" for i
    proof -
      have m1: "a + real (Suc i) * (b - a) / real N \<in> {0..T}"
        by (rule grid_mem) (use i in simp)
      have m2: "a + real i * (b - a) / real N \<in> {0..T}"
        by (rule grid_mem) (use i in simp)
      have dnn: "0 \<le> d / real N" using d0 rNpos by simp
      have "\<bar>(a + real (Suc i) * (b - a) / real N)
          - (a + real i * (b - a) / real N)\<bar> = d / real N"
        unfolding gap by (rule abs_of_nonneg[OF dnn])
      hence gp: "\<bar>(a + real (Suc i) * (b - a) / real N)
          - (a + real i * (b - a) / real N)\<bar> < 1 / 2 ^ n"
        using mesh by simp
      show ?thesis by (rule H[OF order.refl m1 m2 gp])
    qed
    have t1: "\<bar>f b - f a\<bar> \<le> real N * (E * 2 powr (- g * real n))"
      by (rule telescope_grid[of N f, OF Npos per])
    have pw0: "0 \<le> E * 2 powr (- g * real n)" using E0 by simp
    have t2: "real N * (E * 2 powr (- g * real n))
        \<le> 2 * (d * 2 ^ n) * (E * 2 powr (- g * real n))"
      by (intro mult_right_mono Nle pw0)
    have t3: "2 * (d * 2 ^ n) * (E * 2 powr (- g * real n))
        = (2 * E * 2 ^ n * 2 powr (- g * real n)) * d"
      by (simp add: algebra_simps)
    have dbound: "d \<le> max 1 (T powr (1 - g)) * d powr g"
    proof -
      have s1: "(1 - g) + g = (1::real)" by simp
      have s2: "d powr ((1 - g) + g) = d powr (1 - g) * d powr g"
        by (rule powr_add)
      have s3: "d powr 1 = d powr (1 - g) * d powr g"
        using s2 unfolding s1 .
      have split: "d = d powr (1 - g) * d powr g"
        using s3 d0 by simp
      have pb: "d powr (1 - g) \<le> max 1 (T powr (1 - g))"
      proof (cases "d \<le> 1")
        case True
        have "d powr (1 - g) \<le> 1"
          using True g1 d0 by (intro powr_le1) simp_all
        thus ?thesis by simp
      next
        case False
        have "d powr (1 - g) \<le> T powr (1 - g)"
          using g1 d0 dT by (intro powr_mono2) simp_all
        thus ?thesis by simp
      qed
      have "d powr (1 - g) * d powr g \<le> max 1 (T powr (1 - g)) * d powr g"
        by (intro mult_right_mono pb) simp
      thus ?thesis using split by linarith
    qed
    have c2f: "0 \<le> 2 * E * 2 ^ n * 2 powr (- g * real n)"
      using E0 by (intro mult_nonneg_nonneg) simp_all
    have t4: "(2 * E * 2 ^ n * 2 powr (- g * real n)) * d
        \<le> (2 * E * 2 ^ n * 2 powr (- g * real n))
           * (max 1 (T powr (1 - g)) * d powr g)"
      by (intro mult_left_mono dbound c2f)
    have t5: "(2 * E * 2 ^ n * 2 powr (- g * real n))
           * (max 1 (T powr (1 - g)) * d powr g)
        = (2 * E * 2 ^ n * 2 powr (- g * real n) * max 1 (T powr (1 - g)))
          * d powr g"
      by (simp add: algebra_simps)
    have t6: "(2 * E * 2 ^ n * 2 powr (- g * real n) * max 1 (T powr (1 - g)))
          * d powr g \<le> ?c * d powr g"
      by (intro mult_right_mono) (use c1nn in simp_all)
    have absd: "\<bar>a - b\<bar> = d" unfolding d_def using ab1 by simp
    have "\<bar>f a - f b\<bar> = \<bar>f b - f a\<bar>" by (rule abs_minus_commute)
    with t1 t2 t3 t4 t5 t6 show ?thesis unfolding absd by linarith
  qed
  consider (eq) "u = v" | (small) "u \<noteq> v" "\<bar>u - v\<bar> < 1 / 2 ^ n"
    | (big) "u \<noteq> v" "1 / 2 ^ n \<le> \<bar>u - v\<bar>" by force
  then show ?thesis
  proof cases
    case eq
    thus ?thesis using c1nn c2nn by simp
  next
    case small
    have d0: "0 < \<bar>u - v\<bar>" using small(1) by simp
    obtain m where nm: "n \<le> m" and lo: "1 / 2 ^ Suc m \<le> \<bar>u - v\<bar>"
      and hi: "\<bar>u - v\<bar> < 1 / 2 ^ m"
      by (rule exists_dyadic_level[OF d0 small(2)])
    have step1: "\<bar>f u - f v\<bar> \<le> E * 2 powr (- g * real m)"
      by (rule H[OF nm u v hi])
    have expeq: "g + (- g * real (Suc m)) = - g * real m"
      by (simp add: algebra_simps)
    have e1: "2 powr (- g * real m) = 2 powr g * 2 powr (- g * real (Suc m))"
      using powr_add[of 2 g "- g * real (Suc m)"] expeq by simp
    have A: "((1::real)/2) ^ Suc m = 2 powr (- real (Suc m))"
    proof -
      have p1: "2 powr (- real (Suc m)) = 1 / ((2::real) powr real (Suc m))"
        by (rule powr_minus_divide)
      have p2: "(2::real) powr real (Suc m) = 2 ^ Suc m"
        by (rule powr_realpow) simp
      have p3: "((1::real)/2) ^ Suc m = 1 / 2 ^ Suc m"
        by (simp add: power_one_over)
      show ?thesis unfolding p3 p1 p2 by (rule refl)
    qed
    have B: "((2::real) powr (- real (Suc m))) powr g
        = 2 powr (- real (Suc m) * g)"
      by (rule powr_powr)
    have e2: "(((1::real)/2) ^ Suc m) powr g = 2 powr (- g * real (Suc m))"
      unfolding A B by (simp add: algebra_simps)
    have prod_eq: "E * 2 powr (- g * real m)
        = E * 2 powr g * ((((1::real)/2) ^ Suc m) powr g)"
      unfolding e1 e2 by (simp add: algebra_simps)
    have step2: "\<bar>f u - f v\<bar>
        \<le> E * 2 powr g * ((((1::real)/2) ^ Suc m) powr g)"
      using step1 unfolding prod_eq .
    have lo': "((1::real)/2) ^ Suc m \<le> \<bar>u - v\<bar>"
      using lo by (simp add: power_one_over)
    have e3: "(((1::real)/2) ^ Suc m) powr g \<le> \<bar>u - v\<bar> powr g"
      by (intro powr_mono2 less_imp_le[OF g0] lo') simp
    have step3: "E * 2 powr g * ((((1::real)/2) ^ Suc m) powr g)
        \<le> E * 2 powr g * \<bar>u - v\<bar> powr g"
      by (intro mult_left_mono e3 c1nn)
    have step4: "E * 2 powr g * \<bar>u - v\<bar> powr g \<le> ?c * \<bar>u - v\<bar> powr g"
      by (intro mult_right_mono) (use c2nn in simp_all)
    from step2 step3 step4 show ?thesis by linarith
  next
    case big
    show ?thesis
    proof (cases "u \<le> v")
      case True
      have "1 / 2 ^ n \<le> v - u" using big(2) True by simp
      from main[OF True u v this] show ?thesis .
    next
      case False
      hence vu: "v \<le> u" by simp
      have "1 / 2 ^ n \<le> u - v" using big(2) False by simp
      from main[OF vu v u this] show ?thesis
        by (simp add: abs_minus_commute)
    qed
  qed
qed


subsection \<open>A Lipschitz bound is a Holder bound on a bounded interval\<close>

text \<open>Pair tightness needs no matrix-valued Kolmogorov criterion: the
  \<open>X\<close>-side carries a stochastic Hoelder estimate (\<open>Path_Tightness\<close>), the
  \<open>Y\<close>-side the deterministic Lipschitz modulus of \<open>diffquot_lipschitz\<close>,
  and on a bounded horizon a Lipschitz bound is itself Hoelder-\<open>ga\<close>.
  Adding the two via \<open>norm_Pair_le\<close> puts the pair path in a single
  Hoelder ball of the product type, where \<open>compactin_path_holder_ball\<close>
  applies since products of
  \<open>polish_space\<close>/\<open>real_normed_vector\<close>/\<open>heine_borel\<close> spaces are again
  such.\<close>

lemma lipschitz_imp_holder_bound:
  fixes s t :: real
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and B: "0 \<le> B"
    and st: "s \<in> {0..T}" "t \<in> {0..T}"
  shows "B * \<bar>t - s\<bar> \<le> B * T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
proof (cases "t = s")
  case True
  then show ?thesis using B ga T by simp
next
  case False
  then have d: "0 < \<bar>t - s\<bar>" by simp
  have dT: "\<bar>t - s\<bar> \<le> T" using st by auto
  have "\<bar>t - s\<bar> = \<bar>t - s\<bar> powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    using d by (simp flip: powr_add)
  also have "\<dots> \<le> T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    using d dT ga by (intro mult_right_mono powr_mono2) auto
  finally have "\<bar>t - s\<bar> \<le> T powr (1 - ga) * \<bar>t - s\<bar> powr ga" .
  then show ?thesis
    using B by (simp add: mult_left_mono mult.assoc)
qed

(*<*)
end
(*>*)
