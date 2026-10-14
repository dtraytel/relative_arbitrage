section \<open>Section 4 for the operator of Eq. (1.9)\<close>

(*<*)
theory Comparison_Instance
  imports
    Comparison_Two_Domain Operator_Envelope_Continuity
begin
(*>*)

text \<open>The operator \<^const>\<open>ell_op\<close> of Eq. (1.9) is a geometric operator in the
  sense of @{theory Relative_Arbitrage_Equation.Geometric_Operator} whenever
  \<open>1 \<le> k < n\<close> and \<open>1 \<le> L\<close>, by Lemma 3.1 and the invariances of display (4.4).
  The comparison chain of the preceding theories then gives Theorems 4.2 and
  4.3 and Proposition 4.1 for Definition 3.1 as the paper states it, with the
  paper's predicates \<^const>\<open>visc_subsol_env2\<close> and \<^const>\<open>visc_supersol_env2\<close>.\<close>

section \<open>The instance\<close>

theorem ell_op_geometric_operator:
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "geometric_operator (ell_op k L :: real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real)"
proof (rule geometric_operator.intro)
  have ne: "\<And>p :: real^'n. feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k L])
  show "ell_op k L p N \<le> ell_op k L p M" if "psd (N - M)"
    for N M :: "real^'n^'n" and p :: "real^'n"
    by (rule ell_op_elliptic_le[OF that ne])
  show "ell_op k L p (t *\<^sub>R M) = t * ell_op k L p M" if "0 < t"
    for t and M :: "real^'n^'n" and p :: "real^'n"
    by (rule ell_op_scaleR_matrix[OF that ne])
  show "ell_op k L (c *\<^sub>R p) M = ell_op k L p M" if "0 < c"
    for c and M :: "real^'n^'n" and p :: "real^'n"
    by (rule ell_op_scale) (use that in simp)
  show "ell_op k L (R *v p) (R ** M ** transpose R) = ell_op k L p M"
    if "orthogonal_matrix R" for R M :: "real^'n^'n" and p :: "real^'n"
    by (rule ell_op_conj_rot[OF that])
  show "\<exists>C. \<forall>(p :: real^'n) (M :: real^'n^'n) \<delta>. 0 \<le> \<delta> \<longrightarrow>
      ell_op k L p M \<le> ell_op k L p (M + \<delta> *\<^sub>R mat 1) + C * \<delta>"
  proof (intro exI allI impI)
    fix p :: "real^'n" and M :: "real^'n^'n" and \<delta> :: real
    assume d: "0 \<le> \<delta>"
    have "ell_op k L p M \<le> ell_op k L p (M + \<delta> *\<^sub>R mat 1) + mgap L M (M + \<delta> *\<^sub>R mat 1)"
      by (rule ell_op_M_gap[OF ne])
    also have "mgap L M (M + \<delta> *\<^sub>R mat 1) = real CARD('n) * L / 2 * \<delta>"
      using mgap_shift_id(1)[OF d, where L = L and M = M] by (simp add: mult.commute)
    finally show "ell_op k L p M
        \<le> ell_op k L p (M + \<delta> *\<^sub>R mat 1) + real CARD('n) * L / 2 * \<delta>" .
  qed
  show "op_lsc (ell_op k L) p M = ereal (ell_op k L p M)"
    if "transpose M = M" "p \<noteq> 0" for M :: "real^'n^'n" and p :: "real^'n"
    unfolding ell_op_lsc_eq_op_lsc[symmetric] by (rule ell_op_lsc_off_zero[OF that L k])
  show "op_usc (ell_op k L) p M = ereal (ell_op k L p M)"
    if "transpose M = M" "p \<noteq> 0" for M :: "real^'n^'n" and p :: "real^'n"
    unfolding ell_op_usc_eq_op_usc[symmetric] by (rule ell_op_usc_off_zero[OF that L k])
  show "op_lsc (ell_op k L) 0 M = ereal (ell_op k L 0 M)" for M :: "real^'n^'n"
    unfolding ell_op_lsc_eq_op_lsc[symmetric] by (rule ell_op_lsc_at_zero[OF k L])
  show "op_usc (ell_op k L) (0 :: real^'n) (0 :: real^'n^'n) < 1"
    unfolding ell_op_usc_eq_op_usc[symmetric] by (rule ell_op_usc_zero_zero_lt_one[OF k L])
  show "\<exists>\<delta>>0. \<delta> < 1 \<and> (\<forall>q :: real^'n. op_usc (ell_op k L) q (0 - \<delta> *\<^sub>R mat 1) < 1)"
  proof (rule ell_op_usc_small_shift_lt_one[OF k L])
    fix \<delta> :: real
    assume "0 < \<delta>" "\<delta> < 1"
      "\<And>q :: real^'n. ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
    then show ?thesis unfolding ell_op_usc_eq_op_usc by blast
  qed
qed

lemmas ell_op_env2_eq_gen =
  visc_subsol_env2_eq_gen visc_supersol_env2_eq_gen ell_op_lsc_eq_op_lsc ell_op_usc_eq_op_usc

section \<open>Definition 3.1: congruence, monotonicity, test classes\<close>

text \<open>These hold for every \<open>k\<close> and \<open>L\<close>; they are the generic facts of
  @{theory Second_Order_Viscosity_Analysis.Viscosity_Solutions} read through the
  bridge equations.\<close>

lemma visc_subsol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_subsol_env2 k L K \<Omega> f1"
  shows "visc_subsol_env2 k L K \<Omega> f2"
  unfolding visc_subsol_env2_eq_gen
  by (rule visc_subsol_gen_cong[OF h[unfolded visc_subsol_env2_eq_gen]])
    (use OK eq in \<open>auto simp: eventually_principal\<close>)

lemma visc_supersol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_supersol_env2 k L K \<Omega> f1"
  shows "visc_supersol_env2 k L K \<Omega> f2"
  unfolding visc_supersol_env2_eq_gen
  by (rule visc_supersol_gen_cong[OF h[unfolded visc_supersol_env2_eq_gen]])
    (use OK eq in \<open>auto simp: eventually_principal\<close>)

lemma visc_supersol_env2_mono:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env2 k L K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_supersol_env2 k L K \<Omega>' u"
  using assms unfolding visc_supersol_env2_def by blast

lemma visc_subsol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_subsol_env k L K \<Omega> u"
  shows "visc_subsol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_subsol_env_def visc_subsol_env2_def by blast

lemma visc_supersol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env k L K \<Omega> u"
  shows "visc_supersol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_supersol_env_def visc_supersol_env2_def by blast

text \<open>Display (4.4) transports a supersolution along a rotation, a dilation
  and a translation; this needs only the two invariances of \<open>F\<^sup>*\<close>, for every
  \<open>k\<close> and \<open>L\<close>.\<close>

theorem visc_supersol_env_affine:
  fixes w :: "real^'n::finite \<Rightarrow> real" and K \<Omega> :: "(real^'n) set"
    and R :: "real^'n^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
    and sup: "visc_supersol_env2 k L K \<Omega> w"
  shows "visc_supersol_env2 k L ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
      ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` \<Omega>)
      (\<lambda>X. c\<^sup>2 * w ((1/c) *\<^sub>R (transpose R *v (X - b))))"
  unfolding visc_supersol_env2_eq_gen
  by (rule visc_supersol_gen_affine[OF ell_op_usc_scale ell_op_usc_conj_rot orth c0
        sup[unfolded visc_supersol_env2_eq_gen]])

section \<open>Theorems 4.2 and 4.3 and Proposition 4.1\<close>

text \<open>Theorem 4.2(a), for upper and lower semicontinuous data on \<open>K\<close>.\<close>

theorem max_principle_usc_lsc:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K (interior K) u"
    and supw: "visc_supersol_env2 k L K (interior K) w"
  shows "\<exists>x \<in> K - interior K. \<forall>y\<in>K. u y - w y \<le> u x - w x"
  by (rule geometric_operator.max_principle_usc_lsc[OF ell_op_geometric_operator[OF kk LL]
        cK neK uscu lscw Bu Bw subu[unfolded ell_op_env2_eq_gen] supw[unfolded ell_op_env2_eq_gen]])

text \<open>The boundary step of Theorem 4.3: a supersolution with the zero
  boundary condition is nonnegative.\<close>

theorem supersol_bc_nonneg:
  fixes w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bw: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. w x < 0}) w"
  shows "\<And>x. x \<in> K \<Longrightarrow> 0 \<le> w x"
  by (rule geometric_operator.supersol_bc_nonneg[OF ell_op_geometric_operator[OF kk LL]
        cK neK lscw Bw sup[unfolded ell_op_env2_eq_gen]])

text \<open>Theorem 4.2(b), the two-domain comparison principle.\<close>

theorem comparison_two_domain:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K K' :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and cK': "compact K'"
    and KK': "K \<subseteq> interior K'"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K' (interior K') w"
    and w0: "\<And>y. y \<in> K' \<Longrightarrow> 0 \<le> w y"
    and x: "x \<in> K"
  shows "u x \<le> w x"
  by (rule geometric_operator.comparison_two_domain[OF ell_op_geometric_operator[OF kk LL]
        cK neK cK' KK' uscu lscw Bu Bw subu[unfolded ell_op_env2_eq_gen]
        supw[unfolded ell_op_env2_eq_gen] w0 x])

text \<open>Theorem 4.3.\<close>

theorem comparison_expandable:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. w x < 0}) w"
    and x: "x \<in> K"
  shows "u x \<le> usc_env w x"
  by (rule geometric_operator.comparison_expandable[OF ell_op_geometric_operator[OF kk LL]
        cK neK expK uscu lscw Bu Bw subu[unfolded ell_op_env2_eq_gen]
        supw[unfolded ell_op_env2_eq_gen] x])

text \<open>Proposition 4.1.\<close>

theorem uniqueness_expandable:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and uscw: "\<And>c z. w z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> w y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and subw: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < w x}) w"
    and supw: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env w x < 0}) (lsc_env w)"
    and x: "x \<in> K"
  shows "u x = w x"
  by (rule geometric_operator.uniqueness_expandable[OF ell_op_geometric_operator[OF kk LL]
        cK neK expK uscu uscw Bu Bw subu[unfolded ell_op_env2_eq_gen]
        supu[unfolded ell_op_env2_eq_gen] subw[unfolded ell_op_env2_eq_gen]
        supw[unfolded ell_op_env2_eq_gen] x])

(*<*)
end
(*>*)
