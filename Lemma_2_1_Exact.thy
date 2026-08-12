(*
  Title:   Lemma_2_1_Exact.thy
  Content: Lemma 2.1 of arXiv:2512.17702 in its exact form, i.e. with the
           convex hull rather than its closure.

  Relative_Arbitrage_Convexity proves  conv B_k <= A_k <= closure (conv B_k),
  so A_k is the CLOSED convex hull of B_k.  The paper states equality with
  the convex hull itself.  Here we close that gap.

  Plan, three pieces:

  P1  Capped trace bound.  For a in A_k with orthonormal eigenbasis B and
      eigenvalues lambda_u = u . (a u),  sum_u min(lambda_u,1) >= n-k.
      This needs only  Pi_proj a m <= trace (a ** P)  for the spectral
      projection P onto the small-eigenvalue coordinates -- immediate since
      Pi_proj is an infimum.  In particular we do NOT need the identity
      "Pi_m = sum of the m smallest eigenvalues".

  P2  Hypersimplex decomposition, carried out directly on matrices: a
      combination sum_u c_u (u u^T) with coefficients in [0,1] summing to
      n-k lies in conv B_k.  Birkhoff-style swap induction on the number of
      coefficients that are not already 0 or 1.

  P3  Assemble: cap the eigenvalues at 1, rescale so the sum is exactly
      n-k, decompose with P2, and add the nonnegative remainder back using
      suff_volatile_augment.
*)

theory Lemma_2_1_Exact
  imports Relative_Arbitrage_Convexity
begin

unbundle inner_syntax

section \<open>Preliminaries on orthonormal families\<close>

lemma onormal_subset:
  assumes "onormal B" and "S \<subseteq> B"
  shows "onormal S"
  using assms unfolding onormal_def
  by (auto elim: pairwise_subset intro: finite_subset)

lemma onormal_finite:
  assumes "onormal B"
  shows "finite B"
  using assms by (simp add: onormal_def)

text \<open>An orthonormal spanning family is a basis, so it has \<open>n\<close> elements.
  \<open>symmetric_eigenbasis\<close> supplies \<open>span B = UNIV\<close> but not the cardinality,
  which \<open>Pi_constraint_capped_trace\<close> needs.\<close>

lemma onormal_span_card:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B" and sp: "span B = UNIV"
  shows "card B = CARD('n)"
proof -
  have nz: "0 \<notin> B"
    using B by (auto simp: onormal_def)
  have ind: "independent B"
    using B nz by (intro pairwise_orthogonal_independent) (auto simp: onormal_def)
  have "card B = dim B"
    using ind by (simp add: dim_eq_card_independent)
  also have "dim B = dim (UNIV :: (real^'n) set)"
    using sp dim_span[of B] by simp
  also have "\<dots> = CARD('n)"
    by simp
  finally show ?thesis .
qed


section \<open>P2: the hypersimplex decomposition\<close>

text \<open>Base case of the swap induction: if every coefficient is already \<open>0\<close>
  or \<open>1\<close>, the combination is the spectral projection onto the coefficient-\<open>1\<close>
  coordinates, of which there are exactly \<open>n - k\<close>, so it is a generator.\<close>

lemma diag_integral_suff_volatile:
  fixes B :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes B: "onormal B"
    and c01: "\<And>u. u \<in> B \<Longrightarrow> c u \<in> {0, 1}"
    and csum: "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
proof -
  have finB: "finite B"
    using B by (simp add: onormal_def)
  define T where "T = {u \<in> B. c u = 1}"
  have T_sub: "T \<subseteq> B"
    by (auto simp: T_def)
  have zero_off: "c u = 0" if "u \<in> B - T" for u
    using that c01 by (auto simp: T_def)
  have sum_eq: "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) = (\<Sum>u\<in>T. outer_prod u u)"
  proof -
    have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) = (\<Sum>u\<in>T. c u *\<^sub>R outer_prod u u)"
      by (rule sum.mono_neutral_right[OF finB T_sub]) (simp add: zero_off)
    also have "\<dots> = (\<Sum>u\<in>T. outer_prod u u)"
      by (rule sum.cong[OF refl]) (simp add: T_def)
    finally show ?thesis .
  qed
  have cardT: "card T = CARD('n) - k"
  proof -
    have "(\<Sum>u\<in>B. c u) = (\<Sum>u\<in>T. c u)"
      by (rule sum.mono_neutral_right[OF finB T_sub]) (simp add: zero_off)
    also have "\<dots> = real (card T)"
      by (simp add: T_def)
    finally show ?thesis
      using csum by simp
  qed
  show ?thesis
    unfolding sum_eq
    by (rule onormal_sum_suff_volatile[OF onormal_subset[OF B T_sub] cardT])
qed


text \<open>Moving mass \<open>s\<close> from coordinate \<open>j\<close> to coordinate \<open>i\<close>.  Both swapped
  configurations of the induction step are of this form, so the arithmetic is
  done once.\<close>

definition shift :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real)" where
  "shift c i j s =
     (\<lambda>u. if u = i then c u + s else if u = j then c u - s else c u)"

lemma shift_i [simp]: "i \<noteq> j \<Longrightarrow> shift c i j s i = c i + s"
  by (simp add: shift_def)

lemma shift_j [simp]: "i \<noteq> j \<Longrightarrow> shift c i j s j = c j - s"
  by (simp add: shift_def)

lemma shift_other: "u \<noteq> i \<Longrightarrow> u \<noteq> j \<Longrightarrow> shift c i j s u = c u"
  by (simp add: shift_def)

lemma sum_shift:
  assumes fin: "finite B" and ij: "i \<in> B" "j \<in> B" "i \<noteq> j"
  shows "(\<Sum>u\<in>B. shift c i j s u) = (\<Sum>u\<in>B. c u)"
proof -
  have "(\<Sum>u\<in>B. shift c i j s u - c u) = (\<Sum>u\<in>{i, j}. shift c i j s u - c u)"
    by (rule sum.mono_neutral_right[OF fin]) (use ij in \<open>auto simp: shift_other\<close>)
  also have "\<dots> = 0"
    using ij(3) by simp
  finally have "(\<Sum>u\<in>B. shift c i j s u - c u) = 0" .
  then show ?thesis
    by (simp add: sum_subtractf)
qed

text \<open>The original coefficients are the convex combination, with weights
  \<open>d/(e+d)\<close> and \<open>e/(e+d)\<close>, of the two shifted ones.\<close>

lemma shift_convex_combination:
  assumes e: "0 < e" and d: "0 < d" and ij: "i \<noteq> j"
  shows "c u = (d / (e + d)) * shift c i j e u
             + (e / (e + d)) * shift c i j (- d) u"
proof -
  have ed: "e + d \<noteq> 0"
    using e d by simp
  have cancel: "(x * (e + d)) / (e + d) = x" for x
    using ed by simp
  have up: "(d / (e + d)) * (x + e) + (e / (e + d)) * (x - d) = x" for x
  proof -
    have "(d / (e + d)) * (x + e) + (e / (e + d)) * (x - d)
        = (d * (x + e) + e * (x - d)) / (e + d)"
      by (simp add: add_divide_distrib)
    also have "\<dots> = (x * (e + d)) / (e + d)"
      by (simp add: algebra_simps)
    also have "\<dots> = x"
      by (rule cancel)
    finally show ?thesis .
  qed
  have down: "(d / (e + d)) * (x - e) + (e / (e + d)) * (x + d) = x" for x
  proof -
    have "(d / (e + d)) * (x - e) + (e / (e + d)) * (x + d)
        = (d * (x - e) + e * (x + d)) / (e + d)"
      by (simp add: add_divide_distrib)
    also have "\<dots> = (x * (e + d)) / (e + d)"
      by (simp add: algebra_simps)
    also have "\<dots> = x"
      by (rule cancel)
    finally show ?thesis .
  qed
  have same: "(d / (e + d)) * x + (e / (e + d)) * x = x" for x
  proof -
    have "(d / (e + d)) * x + (e / (e + d)) * x
        = (d * x + e * x) / (e + d)"
      by (simp add: add_divide_distrib)
    also have "\<dots> = (x * (e + d)) / (e + d)"
      by (simp add: algebra_simps)
    also have "\<dots> = x"
      by (rule cancel)
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "u = i")
    case True
    then show ?thesis
      using ij up[of "c i"] by simp
  next
    case ni: False
    show ?thesis
    proof (cases "u = j")
      case True
      then show ?thesis
        using ij down[of "c j"] by simp
    next
      case nj: False
      show ?thesis
        using ni nj same[of "c u"] by (simp add: shift_other)
    qed
  qed
qed


text \<open>If one coefficient is strictly between \<open>0\<close> and \<open>1\<close> then so is a second
  one: otherwise the total would be that coefficient plus an integer, forcing
  it to be an integer itself.\<close>

lemma two_fractional:
  fixes B :: "'a set" and c :: "'a \<Rightarrow> real"
  assumes fin: "finite B" and i: "i \<in> B" and fi: "c i \<notin> {0, 1}"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and isum: "(\<Sum>u\<in>B. c u) = real (N :: nat)"
  shows "\<exists>j \<in> B. j \<noteq> i \<and> c j \<notin> {0, 1}"
proof (rule ccontr)
  assume "\<not> (\<exists>j \<in> B. j \<noteq> i \<and> c j \<notin> {0, 1})"
  then have all01: "c u \<in> {0, 1}" if "u \<in> B" "u \<noteq> i" for u
    using that by blast
  define D where "D = B - {i}"
  have finD: "finite D"
    using fin by (simp add: D_def)
  define M where "M = card {u \<in> D. c u = 1}"
  have sumD: "(\<Sum>u\<in>D. c u) = real M"
  proof -
    have "(\<Sum>u\<in>D. c u) = (\<Sum>u\<in>{u \<in> D. c u = 1}. c u)"
      by (rule sum.mono_neutral_right[OF finD])
        (use all01 in \<open>auto simp: D_def\<close>)
    also have "\<dots> = real M"
      by (simp add: M_def)
    finally show ?thesis .
  qed
  have "(\<Sum>u\<in>B. c u) = c i + (\<Sum>u\<in>D. c u)"
    unfolding D_def using fin i by (simp add: sum.remove)
  then have ci_eq: "c i = real N - real M"
    using isum sumD by simp
  have "0 < c i" and "c i < 1"
    using fi c0[OF i] c1[OF i] by auto
  then have "real M < real N" and "real N < real M + 1"
    using ci_eq by simp_all
  then have "M < N" and "N < M + 1"
    by simp_all
  then show False
    by simp
qed

text \<open>The swap induction.  The measure is the number of coefficients that are
  not yet \<open>0\<close> or \<open>1\<close>; each swap makes at least one of the two chosen
  coordinates integral without disturbing the others, and the original
  coefficients are a convex combination of the two swapped ones.\<close>

lemma diag_in_convex_hull_aux:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B"
  shows "\<And>c. card {u \<in> B. c u \<notin> {0, 1}} \<le> N \<Longrightarrow>
      (\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u) \<Longrightarrow> (\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1) \<Longrightarrow>
      (\<Sum>u\<in>B. c u) = real (CARD('n) - k) \<Longrightarrow>
      (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (induct N)
  case 0
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  from 0(1) have "{u \<in> B. c u \<notin> {0, 1}} = {}"
    using finB by auto
  then have "c u \<in> {0, 1}" if "u \<in> B" for u
    using that by blast
  then have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
    by (intro diag_integral_suff_volatile[OF B _ 0(4)])
  then show ?case
    using hull_subset by (rule rev_subsetD)
next
  case (Suc N)
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  show ?case
  proof (cases "{u \<in> B. c u \<notin> {0, 1}} = {}")
    case True
    then have "c u \<in> {0, 1}" if "u \<in> B" for u
      using that by blast
    then have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
      by (intro diag_integral_suff_volatile[OF B _ Suc(5)])
    then show ?thesis
      using hull_subset by (rule rev_subsetD)
  next
    case False
    then obtain i where i: "i \<in> B" "c i \<notin> {0, 1}"
      by blast
    obtain j where j: "j \<in> B" "j \<noteq> i" "c j \<notin> {0, 1}"
      using two_fractional[OF finB i(1) i(2) Suc(3) Suc(4) Suc(5)] by blast
    have ij: "i \<noteq> j"
      using j(2) by blast
    have ci: "0 < c i" "c i < 1"
      using i(2) Suc(3)[OF i(1)] Suc(4)[OF i(1)] by auto
    have cj: "0 < c j" "c j < 1"
      using j(3) Suc(3)[OF j(1)] Suc(4)[OF j(1)] by auto
    define e where "e = min (1 - c i) (c j)"
    define d where "d = min (c i) (1 - c j)"
    have e_pos: "0 < e"
      using ci cj by (simp add: e_def)
    have d_pos: "0 < d"
      using ci cj by (simp add: d_def)
    have ed: "0 < e + d"
      using e_pos d_pos by simp

    text \<open>The two swapped coefficient vectors stay in \<open>[0,1]\<close> and keep the sum.\<close>

    have bnds: "0 \<le> shift c i j s u \<and> shift c i j s u \<le> 1"
      if s: "- d \<le> s" "s \<le> e" and u: "u \<in> B" for s u
    proof (cases "u = i")
      case True
      then show ?thesis
        using ij s ci cj by (auto simp: e_def d_def)
    next
      case ni: False
      show ?thesis
      proof (cases "u = j")
        case True
        then show ?thesis
          using ij s ci cj by (auto simp: e_def d_def)
      next
        case nj: False
        then show ?thesis
          using ni Suc(3)[OF u] Suc(4)[OF u] by (simp add: shift_other)
      qed
    qed
    have sums: "(\<Sum>u\<in>B. shift c i j s u) = real (CARD('n) - k)" for s
      using sum_shift[OF finB i(1) j(1) ij] Suc(5) by simp

    text \<open>Each swap makes \<open>i\<close> or \<open>j\<close> integral, so the measure drops.\<close>

    have drop: "card {u \<in> B. shift c i j s u \<notin> {0, 1}} \<le> N"
      if w: "w \<in> {i, j}" "shift c i j s w \<in> {0, 1}" for s w
    proof -
      have fin_frac: "finite {u \<in> B. c u \<notin> {0, 1}}"
        using finB by simp
      have wB: "w \<in> B" and wfrac: "c w \<notin> {0, 1}"
        using w(1) i j by auto
      have sub: "{u \<in> B. shift c i j s u \<notin> {0, 1}}
          \<subseteq> {u \<in> B. c u \<notin> {0, 1}} - {w}"
      proof
        fix v assume v: "v \<in> {u \<in> B. shift c i j s u \<notin> {0, 1}}"
        then have vB: "v \<in> B" and vfrac: "shift c i j s v \<notin> {0, 1}"
          by auto
        have "v \<noteq> w"
          using vfrac w(2) by blast
        moreover have "c v \<notin> {0, 1}"
        proof (cases "v \<in> {i, j}")
          case True
          then show ?thesis using i j by auto
        next
          case Fv: False
          then have "shift c i j s v = c v"
            by (simp add: shift_other)
          then show ?thesis using vfrac by simp
        qed
        ultimately show "v \<in> {u \<in> B. c u \<notin> {0, 1}} - {w}"
          using vB by simp
      qed
      have "card {u \<in> B. shift c i j s u \<notin> {0, 1}}
          \<le> card ({u \<in> B. c u \<notin> {0, 1}} - {w})"
        using fin_frac sub by (intro card_mono) auto
      also have "\<dots> = card {u \<in> B. c u \<notin> {0, 1}} - 1"
        using wB wfrac fin_frac by (simp add: card_Diff_singleton)
      also have "\<dots> \<le> N"
        using Suc(2) by simp
      finally show ?thesis .
    qed

    have bnd_e: "0 \<le> shift c i j e u" "shift c i j e u \<le> 1" if "u \<in> B" for u
      using bnds[of e u] e_pos d_pos that by auto
    have bnd_d: "0 \<le> shift c i j (- d) u" "shift c i j (- d) u \<le> 1"
      if "u \<in> B" for u
      using bnds[of "- d" u] e_pos d_pos that by auto

    have hull1: "(\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    proof (rule Suc(1))
      show "card {u \<in> B. shift c i j e u \<notin> {0, 1}} \<le> N"
      proof (cases "e = 1 - c i")
        case True
        show ?thesis
        proof (rule drop[where s = e and w = i])
          show "i \<in> {i, j}" by simp
          show "shift c i j e i \<in> {0, 1}" using ij True by simp
        qed
      next
        case False
        then have ecj: "e = c j"
          using e_def by linarith
        show ?thesis
        proof (rule drop[where s = e and w = j])
          show "j \<in> {i, j}" by simp
          show "shift c i j e j \<in> {0, 1}" using ij ecj by simp
        qed
      qed
      show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> shift c i j e u"
        by (rule bnd_e)
      show "\<And>u. u \<in> B \<Longrightarrow> shift c i j e u \<le> 1"
        by (rule bnd_e)
      show "(\<Sum>u\<in>B. shift c i j e u) = real (CARD('n) - k)"
        by (rule sums)
    qed
    have hull2: "(\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    proof (rule Suc(1))
      show "card {u \<in> B. shift c i j (- d) u \<notin> {0, 1}} \<le> N"
      proof (cases "d = c i")
        case True
        show ?thesis
        proof (rule drop[where s = "- d" and w = i])
          show "i \<in> {i, j}" by simp
          show "shift c i j (- d) i \<in> {0, 1}" using ij True by simp
        qed
      next
        case False
        then have dcj: "d = 1 - c j"
          using d_def by linarith
        show ?thesis
        proof (rule drop[where s = "- d" and w = j])
          show "j \<in> {i, j}" by simp
          show "shift c i j (- d) j \<in> {0, 1}" using ij dcj by simp
        qed
      qed
      show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> shift c i j (- d) u"
        by (rule bnd_d)
      show "\<And>u. u \<in> B \<Longrightarrow> shift c i j (- d) u \<le> 1"
        by (rule bnd_d)
      show "(\<Sum>u\<in>B. shift c i j (- d) u) = real (CARD('n) - k)"
        by (rule sums)
    qed

    text \<open>Finally, the original combination is the convex combination.\<close>

    have ed': "e + d \<noteq> 0"
      using ed by simp
    have wsum: "d / (e + d) + e / (e + d) = 1"
    proof -
      have "d / (e + d) + e / (e + d) = (d + e) / (e + d)"
        by (rule add_divide_distrib[symmetric])
      also have "\<dots> = (e + d) / (e + d)"
        by (simp add: add.commute)
      also have "\<dots> = 1"
        using ed' by (rule div_self)
      finally show ?thesis .
    qed
    have wnn: "0 \<le> d / (e + d)" "0 \<le> e / (e + d)"
      using ed d_pos e_pos by auto
    have pt: "(d / (e + d)) * shift c i j e u
        + (e / (e + d)) * shift c i j (- d) u = c u" for u
      using shift_convex_combination[OF e_pos d_pos ij, of c u] by simp
    have comb: "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
        = (d / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
        + (e / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)"
    proof -
      have "(d / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
          + (e / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)
          = (\<Sum>u\<in>B. ((d / (e + d)) * shift c i j e u
                    + (e / (e + d)) * shift c i j (- d) u) *\<^sub>R outer_prod u u)"
        by (simp add: scaleR_right.sum sum.distrib[symmetric]
            scaleR_add_left)
      also have "\<dots> = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
        unfolding pt ..
      finally show ?thesis ..
    qed
    show ?thesis
      unfolding comb
      by (rule convexD[OF convex_convex_hull hull1 hull2 wnn(1) wnn(2) wsum])
  qed
qed


text \<open>P2, packaged: the measure is bounded by its own value.\<close>

lemma diag_in_convex_hull:
  fixes B :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes B: "onormal B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
       \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (rule diag_in_convex_hull_aux
    [OF B, where N = "card {u \<in> B. c u \<notin> {0, 1}}"])
  show "card {u \<in> B. c u \<notin> {0, 1}} \<le> card {u \<in> B. c u \<notin> {0, 1}}"
    by simp
  show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
    by (rule c0)
  show "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    by (rule c1)
  show "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
    by (rule csum)
qed

section \<open>P1: the capped trace bound\<close>

text \<open>The trace of \<open>a\<close> against the spectral projection onto a subset of the
  eigenbasis is the sum of the corresponding eigenvalues.\<close>

lemma trace_mult_spectral_proj:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" and S: "S \<subseteq> B"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "trace (a ** (\<Sum>u\<in>S. outer_prod u u)) = (\<Sum>u\<in>S. u \<bullet> (a *v u))"
proof -
  have finS: "finite S"
    using B S by (auto simp: onormal_def elim: finite_subset)
  have "trace (a ** (\<Sum>u\<in>S. outer_prod u u))
      = (\<Sum>u\<in>S. trace (a ** outer_prod u u))"
    by (simp add: matrix_mult_sum_right trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>S. u \<bullet> (a *v u))"
  proof (rule sum.cong[OF refl])
    fix u assume "u \<in> S"
    have "trace (a ** outer_prod u u) = trace (outer_prod (a *v u) u)"
      by (simp add: mult_outer_prod)
    also have "\<dots> = (a *v u) \<bullet> u"
      by simp
    finally show "trace (a ** outer_prod u u) = u \<bullet> (a *v u)"
      by (simp add: inner_commute)
  qed
  finally show ?thesis .
qed

lemma Pi_constraint_capped_trace:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> Pi_constraint k" and k: "k < CARD('n)"
    and B: "onormal B" "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "real (CARD('n) - k) \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
proof -
  have psd_a: "psd a"
    using a by (simp add: Pi_constraint_def)
  have finB: "finite B"
    using B(1) by (simp add: onormal_def)
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_a by (simp add: lam_def psd_def)
  define T where "T = {u \<in> B. 1 \<le> lam u}"
  have T_sub: "T \<subseteq> B"
    by (auto simp: T_def)
  have finT: "finite T"
    using T_sub finB by (rule finite_subset)
  have cardT_le: "card T \<le> CARD('n)"
    using card_mono[OF finB T_sub] B(2) by simp
  have capT: "(\<Sum>u\<in>T. min (lam u) 1) = real (card T)"
    by (simp add: T_def)
  show ?thesis
  proof (cases "CARD('n) - k \<le> card T")
    case True
    have "(\<Sum>u\<in>T. min (lam u) 1) \<le> (\<Sum>u\<in>B. min (lam u) 1)"
      using lam_nn by (intro sum_mono2[OF finB T_sub]) simp
    then have "real (card T) \<le> (\<Sum>u\<in>B. min (lam u) 1)"
      using capT by simp
    moreover have "real (CARD('n) - k) \<le> real (card T)"
      using True by simp
    ultimately show ?thesis
      unfolding lam_def by simp
  next
    case False
    define S where "S = B - T"
    define m where "m = card S"
    have S_sub: "S \<subseteq> B"
      by (auto simp: S_def)
    have onS: "onormal S"
      by (rule onormal_subset[OF B(1) S_sub])
    have cardS: "m = CARD('n) - card T"
      unfolding m_def S_def using finB T_sub B(2)
      by (simp add: card_Diff_subset finT)
    have m_gt: "k < m"
      using False cardS cardT_le k by simp
    have m_le: "m \<le> CARD('n)"
      using cardS by simp
    have "real (m - k) \<le> Pi_proj a m"
      using a m_gt m_le by (simp add: Pi_constraint_def)
    also have "Pi_proj a m \<le> trace (a ** (\<Sum>u\<in>S. outer_prod u u))"
      using onormal_proj(2)[OF onS]
      by (intro Pi_proj_le[OF psd_a onormal_proj(1)[OF onS]]) (simp add: m_def)
    also have "\<dots> = (\<Sum>u\<in>S. lam u)"
      unfolding lam_def by (rule trace_mult_spectral_proj[OF B(1) S_sub eig])
    finally have key: "real (m - k) \<le> (\<Sum>u\<in>S. lam u)" .
    have capS: "(\<Sum>u\<in>S. min (lam u) 1) = (\<Sum>u\<in>S. lam u)"
      by (rule sum.cong[OF refl]) (auto simp: S_def T_def)
    have split: "(\<Sum>u\<in>B. min (lam u) 1)
        = (\<Sum>u\<in>S. min (lam u) 1) + (\<Sum>u\<in>T. min (lam u) 1)"
      unfolding S_def by (rule sum.subset_diff[OF T_sub finB])
    have nat_eq: "CARD('n) - k = card T + (m - k)"
      using cardS m_gt cardT_le by simp
    have "real (CARD('n) - k) = real (card T) + real (m - k)"
      unfolding nat_eq by simp
    also have "\<dots> \<le> (\<Sum>u\<in>T. min (lam u) 1) + (\<Sum>u\<in>S. min (lam u) 1)"
      using key capT capS by simp
    also have "\<dots> = (\<Sum>u\<in>B. min (lam u) 1)"
      using split by simp
    finally show ?thesis
      unfolding lam_def by simp
  qed
qed

section \<open>P3: the exact inclusion\<close>

text \<open>\<open>suff_volatile k\<close> is closed under adding a nonnegative multiple of a
  rank-one projection (\<open>suff_volatile_augment\<close>), and translation commutes with
  taking the convex hull, so the hull is closed under the same operation.\<close>

lemma convex_hull_augment:
  fixes X :: "real^'n::finite^'n"
  assumes X: "X \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    and t: "0 \<le> t"
  shows "X + t *\<^sub>R outer_prod u u
       \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof -
  define z where "z = t *\<^sub>R outer_prod u u"
  have sub: "(\<lambda>y. z + y) ` suff_volatile k
      \<subseteq> (suff_volatile k :: (real^'n^'n) set)"
  proof
    fix Y assume "Y \<in> (\<lambda>y. z + y) ` suff_volatile k"
    then obtain b where b: "b \<in> suff_volatile k" and Y: "Y = z + b"
      by blast
    have "b + t *\<^sub>R outer_prod u u \<in> suff_volatile k"
      by (rule suff_volatile_augment[OF b t])
    then show "Y \<in> suff_volatile k"
      unfolding Y z_def by (simp add: add.commute)
  qed
  have "z + X
      \<in> (\<lambda>y. z + y) ` (convex hull (suff_volatile k :: (real^'n^'n) set))"
    using X by (rule imageI)
  then have "X + z
      \<in> (\<lambda>y. z + y) ` (convex hull (suff_volatile k :: (real^'n^'n) set))"
    by (simp add: add.commute)
  then have "X + z
      \<in> convex hull ((\<lambda>y. z + y) ` (suff_volatile k :: (real^'n^'n) set))"
    by (simp add: convex_hull_translation)
  then have "X + z \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    using hull_mono[OF sub] by blast
  then show ?thesis
    unfolding z_def .
qed

text \<open>Iterating over a finite index set.\<close>

lemma convex_hull_augment_sum:
  fixes X :: "real^'n::finite^'n"
  assumes X: "X \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
  shows "finite S \<Longrightarrow> (\<And>u. u \<in> S \<Longrightarrow> 0 \<le> g u) \<Longrightarrow>
      X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (induct S rule: finite_induct)
  case empty
  show ?case
    using X by simp
next
  case (insert v S)
  have gv: "0 \<le> g v"
    using insert.prems by simp
  have IH: "X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)
      \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    using insert.hyps(3) insert.prems by simp
  have eq: "X + (\<Sum>u\<in>insert v S. g u *\<^sub>R outer_prod u u)
      = (X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)) + g v *\<^sub>R outer_prod v v"
    by (simp add: sum.insert[OF insert.hyps(1,2)] ac_simps)
  show ?case
    unfolding eq by (rule convex_hull_augment[OF IH gv])
qed

text \<open>Lemma 2.1, exact form.  Diagonalise \<open>a\<close>, cap the eigenvalues at \<open>1\<close>,
  rescale the capped vector so that its sum is exactly \<open>n - k\<close> --- possible
  because by P1 the capped sum is at least \<open>n - k\<close> --- decompose that by P2,
  and add the nonnegative remainder back.\<close>

theorem lemma_2_1_exact:
  fixes k :: nat
  assumes k: "k < CARD('n::finite)"
  shows "(Pi_constraint k :: (real^'n^'n) set)
       \<subseteq> convex hull (suff_volatile k)"
proof
  fix a :: "real^'n^'n"
  assume a: "a \<in> Pi_constraint k"
  have psd_a: "psd a"
    using a by (simp add: Pi_constraint_def)
  have sym_a: "transpose a = a"
    using psd_a by (simp add: psd_def)
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym_a] by blast
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_a by (simp add: lam_def psd_def)
  have adecomp: "a = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])

  define cap where "cap = (\<lambda>u :: real^'n. min (lam u) 1)"
  have cap_nn: "0 \<le> cap u" for u
    using lam_nn by (simp add: cap_def)
  have cap_le1: "cap u \<le> 1" for u
    by (simp add: cap_def)
  have cap_le_lam: "cap u \<le> lam u" for u
    by (simp add: cap_def)
  have nk_pos: "0 < real (CARD('n) - k)"
    using k by simp
  have capsum: "real (CARD('n) - k) \<le> (\<Sum>u\<in>B. cap u)"
    unfolding cap_def lam_def
    by (rule Pi_constraint_capped_trace[OF a k B(1) cardB eig])
  have S_pos: "0 < (\<Sum>u\<in>B. cap u)"
    using capsum nk_pos by simp
  have S_ne: "(\<Sum>u\<in>B. cap u) \<noteq> 0"
    using S_pos by simp

  define th where "th = real (CARD('n) - k) / (\<Sum>u\<in>B. cap u)"
  have th_pos: "0 < th"
    unfolding th_def using nk_pos S_pos by simp
  have th_le1: "th \<le> 1"
    unfolding th_def using S_pos capsum by simp
  define nu where "nu = (\<lambda>u :: real^'n. th * cap u)"
  have nu_nn: "0 \<le> nu u" for u
    unfolding nu_def using th_pos cap_nn by simp
  have nu_le1: "nu u \<le> 1" for u
  proof -
    have "th * cap u \<le> 1 * 1"
      using th_pos th_le1 cap_nn cap_le1 by (intro mult_mono) auto
    then show ?thesis
      by (simp add: nu_def)
  qed
  have nu_le_lam: "nu u \<le> lam u" for u
  proof -
    have "th * cap u \<le> 1 * cap u"
      using th_le1 cap_nn by (intro mult_right_mono) auto
    also have "\<dots> = cap u"
      by simp
    also have "cap u \<le> lam u"
      by (rule cap_le_lam)
    finally show ?thesis
      by (simp add: nu_def)
  qed
  have nusum: "(\<Sum>u\<in>B. nu u) = real (CARD('n) - k)"
  proof -
    have "(\<Sum>u\<in>B. nu u) = th * (\<Sum>u\<in>B. cap u)"
      unfolding nu_def by (simp add: sum_distrib_left)
    also have "\<dots> = real (CARD('n) - k)"
      unfolding th_def using S_ne by simp
    finally show ?thesis .
  qed

  have hull_nu: "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
      \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
  proof (rule diag_in_convex_hull[OF B(1)])
    show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> nu u"
      by (rule nu_nn)
    show "\<And>u. u \<in> B \<Longrightarrow> nu u \<le> 1"
      by (rule nu_le1)
    show "(\<Sum>u\<in>B. nu u) = real (CARD('n) - k)"
      by (rule nusum)
  qed

  have rem: "a = (\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
      + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)"
  proof -
    have "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
        + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)
        = (\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u
                 + (lam u - nu u) *\<^sub>R outer_prod u u)"
      by (rule sum.distrib[symmetric])
    also have "\<dots> = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
      by (rule sum.cong[OF refl]) (simp add: scaleR_add_left[symmetric])
    finally have "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
        + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)
        = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)" .
    then show ?thesis
      using adecomp by simp
  qed

  show "a \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    unfolding rem
  proof (rule convex_hull_augment_sum[OF hull_nu finB])
    show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u - nu u"
      using nu_le_lam by simp
  qed
qed

text \<open>Lemma 2.1 of the paper, verbatim: the convex hull of
  \<open>{a \<in> \<bbbS>\<^sup>n\<^sub>+ : \<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>)(a) \<ge> 1}\<close> IS the constraint set \<open>A\<close> of Eq. (2.1) ---
  no closure.\<close>

corollary lemma_2_1_eq:
  fixes k :: nat
  assumes k: "k < CARD('n::finite)"
  shows "convex hull (suff_volatile k :: (real^'n^'n) set) = Pi_constraint k"
  by (rule subset_antisym[OF lemma_2_1_easy lemma_2_1_exact[OF k]])

end
