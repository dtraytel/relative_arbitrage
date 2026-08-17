section \<open>A soft penalty vanishing on the diagonal\<close>

(*<*)
theory Soft_Penalty
  imports Doubling_Of_Variables "Symmetric_Matrix_Spectra.Outer_Products"
begin

(*>*)

text \<open>
  Two concrete penalties for the doubling argument of
  @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}, together
  with their exact second-order expansions.

  The plain quadratic penalty \<open>(\<alpha>/2)\<parallel>x - y\<parallel>\<^sup>2\<close> is the usual
  choice, but it has a defect: its gradient \<open>\<alpha>(x - y)\<close> is the only thing
  the comparison sees, and for a degenerate elliptic operator that is not
  always enough.  What is wanted instead is a penalty that is still
  \<^emph>\<open>coercive\<close> --- so the doubled maximum is attained --- but whose
  gradient does not vanish anywhere off the diagonal, and whose full 2-jet
  \<^emph>\<open>does\<close> vanish on it.

  \<open>soft_pen \<kappa> d = (\<kappa>/2)\<parallel>d\<parallel>\<^sup>2 - \<kappa>(\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1) - 1)\<close>
  is such a penalty: the subtracted square root softens the quadratic near
  the origin, which is where the name comes from.  It grows quadratically at
  infinity, its gradient \<open>\<kappa>(1 - 1/\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1))\<sqdot>d\<close> is nonzero
  for every \<open>d \<noteq> 0\<close>, and gradient and Hessian both vanish at \<open>d = 0\<close>.
  \<open>quartic_pen \<beta> d = (\<beta>/4)(d \<bullet> d)\<^sup>2\<close> is the simpler penalty with the
  same vanishing 2-jet, kept because its expansion is exact rather than
  asymptotic.
\<close>

text \<open>Writing \<open>s = d \<bullet> d\<close> and \<open>t = 2(d \<bullet> h) + h \<bullet> h\<close>, the exact expansion
  \<open>P(d+h) - P(d) = (\<beta>/4)((s+t)\<^sup>2 - s\<^sup>2) = (\<beta>/4)(2st + t\<^sup>2)\<close> gives gradient
  \<open>\<nabla>P(d) = \<beta>(d \<bullet> d) d\<close> and Hessian quadratic form
  \<open>h \<mapsto> \<beta>(d \<bullet> d)(h \<bullet> h) + 2\<beta>(d \<bullet> h)\<^sup>2\<close>, matrix
  \<open>\<beta>((d \<bullet> d) I + 2 d d\<^sup>T)\<close>, with remainder \<open>o(\<parallel>h\<parallel>\<^sup>2)\<close>. Both vanish only at
  \<open>d = 0\<close>, so on the diagonal this penalty contributes the zero 2-jet ---
  the degenerate configuration a comparison argument has to exclude.\<close>

definition quartic_pen :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real" where
  "quartic_pen \<beta> d = (\<beta>/4) * (d \<bullet> d)\<^sup>2"

text \<open>\<open>semiconvex_penalty_gen\<close> reduces the question to exhibiting one
  penalty that is semiconcave with an explicit constant and has vanishing
  gradient and Hessian at \<open>0\<close>. The pure quartic fails semiconcavity;
  \<open>P(d) = (\<kappa>/2)\<parallel>d\<parallel>\<^sup>2 - \<kappa>(\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1) - 1)\<close> has both properties.
  Semiconcavity is free since
  \<open>(\<kappa>/2)\<parallel>d\<parallel>\<^sup>2 - P(d) = \<kappa>(\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1) - 1) = \<kappa>(\<parallel>(d, 1)\<parallel> - 1)\<close>, a norm
  composed with an affine map. The 2-jet at \<open>0\<close> vanishes because
  \<open>\<surd>(s+1) - 1 = s/(\<surd>(s+1)+1)\<close>, so \<open>P(h)/\<parallel>h\<parallel>\<^sup>2 \<rightarrow> 0\<close>: near \<open>0\<close> the penalty
  is \<open>\<approx> (\<kappa>/8)\<parallel>d\<parallel>\<^sup>4\<close>, while far out it grows quadratically.\<close>

definition soft_pen :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real" where
  "soft_pen \<kappa> d = (\<kappa>/2) * (norm d)\<^sup>2 - \<kappa> * (sqrt ((norm d)\<^sup>2 + 1) - 1)"

lemma div_mul_div_cancel_aux:
  fixes k s r :: real
  assumes s: "s \<noteq> 0"
  shows "k * (s / r) / s = k / r"
  using s by (simp add: field_simps)

text \<open>\<open>soft_pen\<close>'s jet at a general \<open>d\<close> needs an exact, not asymptotic,
  expansion. Writing \<open>S = \<surd>(u+\<Delta>)\<close> and \<open>R = \<surd>u\<close>, the conjugate identity
  gives \<open>S - R = \<Delta>/(S+R)\<close>, and identically
  \<open>S - R - \<Delta>/(2R) = -\<Delta>\<^sup>2/(2R(S+R)\<^sup>2)\<close>. So the second-order remainder is a
  quotient, and \<open>o(\<Delta>\<^sup>2)\<close> is just continuity of
  \<open>\<Delta> \<mapsto> 1/(2R(S+R)\<^sup>2)\<close> at \<open>\<Delta> = 0\<close>, where it equals \<open>1/(8R\<^sup>3)\<close>, the
  Taylor coefficient.\<close>

lemma sqrt_diff_exact:
  fixes u D :: real
  assumes uD: "0 \<le> u + D" and u: "0 \<le> u"
    and pos: "0 < sqrt (u + D) + sqrt u"
  shows "sqrt (u + D) - sqrt u = D / (sqrt (u + D) + sqrt u)"
proof -
  have s1: "sqrt (u + D) * sqrt (u + D) = u + D" using uD by simp
  have s2: "sqrt u * sqrt u = u" using u by simp
  have prod: "(sqrt (u + D) - sqrt u) * (sqrt (u + D) + sqrt u) = D"
    using s1 s2 by (simp add: algebra_simps)
  show ?thesis
    using pos prod by (simp add: nonzero_eq_divide_eq)
qed

text \<open>The same identity without the quotient, holding for every \<open>\<Delta>\<close>
  including \<open>0\<close>. The algebraic heart: \<open>(S+R)\<^sup>2 - \<Delta> = 2R(S+R)\<close>, whence
  \<open>\<Delta>/(2R) - \<Delta>\<^sup>2/(2R(S+R)\<^sup>2) = \<Delta>/(S+R) = S - R\<close>.\<close>

lemma sqrt_rhs_aux:
  fixes D R T :: real
  assumes R: "R \<noteq> 0" and T: "T \<noteq> 0" and key: "T\<^sup>2 - D = 2 * R * T"
  shows "D / (2 * R) - D\<^sup>2 / (2 * R * T\<^sup>2) = D / T"
proof -
  have n: "D * T\<^sup>2 - D\<^sup>2 = D * (2 * R * T)"
  proof -
    have "D * T\<^sup>2 - D\<^sup>2 = D * (T\<^sup>2 - D)"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> = D * (2 * R * T)" unfolding key ..
    finally show ?thesis .
  qed
  have "D / (2 * R) - D\<^sup>2 / (2 * R * T\<^sup>2) = (D * T\<^sup>2 - D\<^sup>2) / (2 * R * T\<^sup>2)"
    using R T by (simp add: field_simps)
  also have "\<dots> = (D * (2 * R * T)) / (2 * R * T\<^sup>2)" unfolding n ..
  also have "\<dots> = D / T"
    using R T by (simp add: power2_eq_square field_simps)
  finally show ?thesis .
qed

theorem sqrt_second_order_exact:
  fixes u D :: real
  assumes u: "0 < u" and uD: "0 \<le> u + D"
  shows "sqrt (u + D) - sqrt u
      = D / (2 * sqrt u)
        - D\<^sup>2 / (2 * sqrt u * (sqrt (u + D) + sqrt u)\<^sup>2)"
proof -
  have R: "0 < sqrt u" using u by simp
  have S: "0 \<le> sqrt (u + D)" using uD by simp
  have SR: "0 < sqrt (u + D) + sqrt u" using R S by linarith
  have s1: "sqrt (u + D) * sqrt (u + D) = u + D" using uD by simp
  have s2: "sqrt u * sqrt u = u" using u by simp
  have key: "(sqrt (u + D) + sqrt u)\<^sup>2 - D
      = 2 * sqrt u * (sqrt (u + D) + sqrt u)"
    using s1 s2 by (simp add: power2_eq_square algebra_simps)
  have e: "sqrt (u + D) - sqrt u = D / (sqrt (u + D) + sqrt u)"
    by (rule sqrt_diff_exact) (use uD u SR in linarith)+
  have rhs: "D / (2 * sqrt u)
        - D\<^sup>2 / (2 * sqrt u * (sqrt (u + D) + sqrt u)\<^sup>2)
      = D / (sqrt (u + D) + sqrt u)"
    by (rule sqrt_rhs_aux) (use R SR key in auto)
  show ?thesis unfolding e rhs ..
qed

text \<open>Collecting the expansion into gradient + Hessian + remainder: with
  \<open>a = d \<bullet> h\<close>, \<open>b = h \<bullet> h\<close>, \<open>\<Delta> = 2a + b\<close> and \<open>R = \<surd>(\<parallel>d\<parallel>\<^sup>2+1)\<close>,
  \<open>(\<kappa>/2)\<Delta> - \<kappa>\<Delta>/(2R) = \<kappa>(1 - 1/R) a + (\<kappa>/2)(1 - 1/R) b\<close>, an identity
  giving the gradient and half the Hessian term exactly; the remainder is
  the two quotient terms.\<close>

lemma soft_pen_rem_aux:
  fixes k R a b W :: real
  assumes R: "R \<noteq> 0"
  shows "(k/2) * (2*a + b) - k * ((2*a + b) / (2*R) - W)
        - k * (1 - 1/R) * a
        - (k * (1 - 1/R) * b + k * a\<^sup>2 / R^3) / 2
      = k * W - k * a\<^sup>2 / (2 * R^3)"
  using R by (simp add: field_simps)

text \<open>One input to the remainder limit: \<open>(d \<bullet> h)\<^sup>2/\<parallel>h\<parallel>\<^sup>2\<close> is bounded,
  uniformly in \<open>h\<close>, by \<open>\<parallel>d\<parallel>\<^sup>2\<close> (Cauchy-Schwarz squared), enabling
  \<open>Lim_null_comparison\<close>.\<close>

lemma inner_sq_over_norm_sq_le:
  fixes d h :: "real^'n::finite"
  shows "(d \<bullet> h)\<^sup>2 \<le> (norm d)\<^sup>2 * (norm h)\<^sup>2"
proof -
  have cs: "\<bar>d \<bullet> h\<bar> \<le> norm d * norm h"
    by (rule Cauchy_Schwarz_ineq2)
  have "(\<bar>d \<bullet> h\<bar>)\<^sup>2 \<le> (norm d * norm h)\<^sup>2"
    by (rule power_mono[OF cs]) simp
  then show ?thesis
    by (simp add: power_mult_distrib)
qed

corollary inner_sq_quotient_bounded:
  fixes d h :: "real^'n::finite"
  assumes h: "h \<noteq> 0"
  shows "(d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2 \<le> (norm d)\<^sup>2"
proof -
  have b: "0 < (norm h)\<^sup>2" using h by simp
  show ?thesis
    using inner_sq_over_norm_sq_le[of d h] b
    by (simp add: pos_divide_le_eq)
qed

text \<open>The other input: the denominator \<open>T h = \<surd>(u + \<Delta> h) + R\<close> tends to
  \<open>2R\<close> as \<open>h \<rightarrow> 0\<close>, so \<open>2/(R T\<^sup>2) - 1/(2R\<^sup>3)\<close> vanishes, since
  \<open>R(2R)\<^sup>2 = 4R\<^sup>3\<close>.\<close>

lemma soft_pen_T_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1))
      \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
proof -
  have "((\<lambda>h::real^'n. ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
      \<longlongrightarrow> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> (0::real^'n)) + ((0::real^'n) \<bullet> 0)))
      (at 0)"
    by (intro tendsto_intros)
  then have a: "((\<lambda>h::real^'n. ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
      \<longlongrightarrow> (norm d)\<^sup>2 + 1) (at 0)"
    by simp
  have b: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))))
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule tendsto_real_sqrt[OF a])
  have "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1))
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1) + sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule tendsto_add[OF b tendsto_const])
  then show ?thesis by simp
qed

text \<open>The bracket itself vanishes: \<open>T h \<rightarrow> 2R\<close> gives \<open>R T h\<^sup>2 \<rightarrow> 4R\<^sup>3\<close>, so
  \<open>2/(R T h\<^sup>2) \<rightarrow> 1/(2R\<^sup>3)\<close>, the constant subtracted.\<close>

lemma soft_pen_bracket_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
        - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)) \<longlongrightarrow> 0) (at 0)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" using up by simp
  have Tl: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1)) \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule soft_pen_T_tendsto)
  have Dl: "((\<lambda>h::real^'n. sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2) (at 0)"
    by (intro tendsto_intros Tl)
  have dnz: "sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2 \<noteq> 0"
    using Rp by (simp add: power2_eq_square)
  have Ql: "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      \<longlongrightarrow> 2 / (sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)) (at 0)"
    by (rule tendsto_divide[OF tendsto_const Dl dnz])
  have val: "2 / (sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      = 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
  proof -
    have e: "sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2
        = 4 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
      by (simp add: power2_eq_square power3_eq_cube)
    show ?thesis unfolding e using Rp by (simp add: field_simps)
  qed
  have "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3))
      \<longlongrightarrow> 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)
        - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)) (at 0)"
    by (rule tendsto_diff[OF Ql[unfolded val] tendsto_const])
  then show ?thesis by simp
qed

text \<open>The second summand of the remainder quotient: numerator \<open>\<rightarrow> 0\<close> over
  denominator \<open>\<rightarrow> 8R\<^sup>3 \<noteq> 0\<close>.\<close>

lemma soft_pen_second_summand_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" using up by simp
  have Nl: "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))) \<longlongrightarrow> 0) (at 0)"
  proof -
    have "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h)))
        \<longlongrightarrow> \<kappa> * (4*(d \<bullet> (0::real^'n)) + ((0::real^'n) \<bullet> 0))) (at 0)"
      by (intro tendsto_intros)
    then show ?thesis by simp
  qed
  have Tl: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1)) \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule soft_pen_T_tendsto)
  have Dl: "((\<lambda>h::real^'n. 2 * sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2) (at 0)"
    by (intro tendsto_intros Tl)
  have dnz: "2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2 \<noteq> 0"
    using Rp by (simp add: power2_eq_square)
  have "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      \<longlongrightarrow> 0 / (2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      (at 0)"
    by (rule tendsto_divide[OF Nl Dl dnz])
  then show ?thesis by simp
qed

text \<open>The remainder quotient splits into a bounded factor times a vanishing
  bracket, plus a vanishing summand, via \<open>\<Delta>\<^sup>2 = 4a\<^sup>2 + 4ab + b\<^sup>2\<close>:
  \<open>4a\<^sup>2\<close> carries the bounded factor, and \<open>(4ab + b\<^sup>2)/b\<close> is the second
  summand.\<close>

lemma rem_split_aux:
  fixes k R T a b :: real
  assumes R: "R \<noteq> 0" and T: "T \<noteq> 0" and b: "b \<noteq> 0"
  shows "(k * ((2*a + b)\<^sup>2 / (2 * R * T\<^sup>2)) - k * a\<^sup>2 / (2 * R^3)) / b
      = (a\<^sup>2 / b) * (k * (2/(R*T\<^sup>2) - 1/(2*R^3)))
        + k * (4*a + b) / (2*R*T\<^sup>2)"
  using R T b
  by (simp add: field_simps power2_eq_square power3_eq_cube)

text \<open>\<open>outer_prod\<close> lives in @{theory Symmetric_Matrix_Spectra.Outer_Products}.\<close>

definition soft_hess :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n^'n" where
  "soft_hess \<kappa> d = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R mat 1
      + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) *\<^sub>R outer_prod d d"

text \<open>\<open>soft_pen_jet_form\<close> writes the Hessian as a quadratic expression,
  matched to \<open>soft_hess\<close> by \<open>soft_hess_quadform\<close>, with the gradient
  packaged as \<open>soft_grad\<close>. Writing \<open>R = \<surd>(\<parallel>d\<parallel>\<^sup>2+1) \<ge> 1\<close>: the first
  summand lies in \<open>[0, \<kappa>\<parallel>z\<parallel>\<^sup>2]\<close>, and Cauchy-Schwarz bounds the second by
  \<open>\<kappa>\<parallel>z\<parallel>\<^sup>2\<close>, so the quadratic form is bounded by \<open>2\<kappa>\<parallel>z\<parallel>\<^sup>2\<close>, uniformly in
  \<open>d\<close>.\<close>

definition soft_grad :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n" where
  "soft_grad \<kappa> d = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"

lemma sqrt_norm_sq_add_one_ge_one:
  fixes d :: "real^'n::finite"
  shows "1 \<le> sqrt ((norm d)\<^sup>2 + 1)"
proof -
  have "(1::real) = sqrt 1" by simp
  also have "sqrt (1::real) \<le> sqrt ((norm d)\<^sup>2 + 1)"
    by (rule real_sqrt_le_mono) simp
  finally show ?thesis .
qed

text \<open>The gradient field of \<open>soft_pen \<kappa>\<close> is Lipschitz at an elementary,
  non-sharp constant, obtained algebraically without the mean value
  inequality or a bound on the operator norm of \<open>soft_hess\<close>. Writing
  \<open>R d = \<surd>(\<parallel>d\<parallel>\<^sup>2+1) \<ge> 1\<close>, \<open>R\<close> is 1-Lipschitz:
  \<open>(R x - R y)(R x + R y) = \<parallel>x\<parallel>\<^sup>2 - \<parallel>y\<parallel>\<^sup>2\<close> together with
  \<open>|\<parallel>x\<parallel> - \<parallel>y\<parallel>| \<le> \<parallel>x-y\<parallel>\<close> gives the bound after cancelling the positive
  factor \<open>Rx+Ry\<close>.\<close>

lemma norm_le_soft_R:
  fixes x :: "real^'n::finite"
  shows "norm x \<le> sqrt ((norm x)\<^sup>2 + 1)"
proof -
  have "norm x = sqrt ((norm x)\<^sup>2)" by simp
  also have "\<dots> \<le> sqrt ((norm x)\<^sup>2 + 1)" by (rule real_sqrt_le_mono) simp
  finally show ?thesis .
qed

lemma abs_norm_diff_le:
  fixes x y :: "'a::real_normed_vector"
  shows "\<bar>norm x - norm y\<bar> \<le> norm (x - y)"
proof -
  have a: "norm x - norm y \<le> norm (x - y)" by (rule norm_triangle_ineq2)
  have b: "norm y - norm x \<le> norm (y - x)" by (rule norm_triangle_ineq2)
  have c: "norm (y - x) = norm (x - y)" by (rule norm_minus_commute)
  show ?thesis using a b unfolding c by linarith
qed

lemma soft_R_lipschitz:
  fixes x y :: "real^'n::finite"
  shows "\<bar>sqrt ((norm x)\<^sup>2 + 1) - sqrt ((norm y)\<^sup>2 + 1)\<bar> \<le> norm (x - y)"
proof -
  let ?s = "sqrt ((norm x)\<^sup>2 + 1)"
  let ?t = "sqrt ((norm y)\<^sup>2 + 1)"
  have s1: "1 \<le> ?s" by (rule sqrt_norm_sq_add_one_ge_one)
  have t1: "1 \<le> ?t" by (rule sqrt_norm_sq_add_one_ge_one)
  have sum_pos: "0 < ?s + ?t" using s1 t1 by linarith
  have ssq: "?s * ?s = (norm x)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm x)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  have tsq: "?t * ?t = (norm y)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm y)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  \<comment> \<open>the difference of squares, both ways round\<close>
  have diffsq: "(?s - ?t) * (?s + ?t) = (norm x - norm y) * (norm x + norm y)"
  proof -
    have "(?s - ?t) * (?s + ?t) = ?s * ?s - ?t * ?t"
      by (simp add: algebra_simps)
    also have "\<dots> = (norm x)\<^sup>2 - (norm y)\<^sup>2" unfolding ssq tsq by simp
    also have "\<dots> = (norm x - norm y) * (norm x + norm y)"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have absprod: "\<bar>?s - ?t\<bar> * (?s + ?t)
      = \<bar>norm x - norm y\<bar> * (norm x + norm y)"
  proof -
    have nn: "0 \<le> ?s + ?t" using sum_pos by linarith
    have nn2: "0 \<le> norm x + norm y" by simp
    have "\<bar>?s - ?t\<bar> * (?s + ?t) = \<bar>(?s - ?t) * (?s + ?t)\<bar>"
      using nn by (simp add: abs_mult)
    also have "\<dots> = \<bar>(norm x - norm y) * (norm x + norm y)\<bar>"
      unfolding diffsq ..
    also have "\<dots> = \<bar>norm x - norm y\<bar> * (norm x + norm y)"
      using nn2 by (simp add: abs_mult)
    finally show ?thesis .
  qed
  \<comment> \<open>and now the two elementary bounds\<close>
  have b1: "\<bar>norm x - norm y\<bar> \<le> norm (x - y)" by (rule abs_norm_diff_le)
  have b2: "norm x + norm y \<le> ?s + ?t"
    using norm_le_soft_R[of x] norm_le_soft_R[of y] by linarith
  have chain: "\<bar>?s - ?t\<bar> * (?s + ?t) \<le> norm (x - y) * (?s + ?t)"
  proof -
    have "\<bar>norm x - norm y\<bar> * (norm x + norm y)
        \<le> norm (x - y) * (norm x + norm y)"
      by (rule mult_right_mono[OF b1]) simp
    also have "\<dots> \<le> norm (x - y) * (?s + ?t)"
      by (rule mult_left_mono[OF b2]) simp
    finally show ?thesis unfolding absprod .
  qed
  show ?thesis by (rule mult_right_le_imp_le[OF chain sum_pos])
qed

text \<open>The shrink map \<open>d \<mapsto> d / R d\<close> is 2-Lipschitz: with \<open>s = R x\<close>,
  \<open>t = R y\<close>, clearing denominators gives
  \<open>st(x/s - y/t) = t(x-y) + (t-s)y\<close>, and the \<open>R\<close>-Lipschitz bound with
  \<open>\<parallel>y\<parallel> \<le> t\<close>, \<open>s \<ge> 1\<close> yields the non-sharp constant 2. Since
  \<open>soft_grad \<kappa> d = \<kappa> d - \<kappa>(shrink d)\<close>, \<open>soft_grad \<kappa>\<close> is \<open>3\<kappa>\<close>-Lipschitz.\<close>

definition soft_shrink :: "real^'n::finite \<Rightarrow> real^'n" where
  "soft_shrink d = (1 / sqrt ((norm d)\<^sup>2 + 1)) *\<^sub>R d"

text \<open>At \<open>d = 0\<close> the gradient and Hessian of \<open>soft_pen\<close> both vanish, so a
  diagonal configuration would give the test function the vanishing jet
  \<open>(0,0)\<close> --- the case a comparison argument must exclude.  Off
  the diagonal, for \<open>\<kappa> > 0\<close> the gradient is nonzero since \<open>R d > 1\<close> for
  \<open>d \<noteq> 0\<close>, making \<open>\<kappa>(1 - 1/R d)\<close> strictly positive, the positive lower
  bound \<open>c\<close> needed elsewhere.\<close>

lemma soft_R_gt_one:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0"
  shows "1 < sqrt ((norm d)\<^sup>2 + 1)"
proof -
  have "0 < norm d" using d by simp
  then have "0 < (norm d)\<^sup>2" by simp
  then have "(1::real) < (norm d)\<^sup>2 + 1" by linarith
  then have "sqrt (1::real) < sqrt ((norm d)\<^sup>2 + 1)" by (rule real_sqrt_less_mono)
  then show ?thesis by simp
qed

lemma soft_grad_coeff_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "0 < \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
proof -
  have R: "1 < sqrt ((norm d)\<^sup>2 + 1)" by (rule soft_R_gt_one[OF d])
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) < 1" using R Rp by (simp add: divide_less_eq)
  then have pos: "0 < 1 - 1 / sqrt ((norm d)\<^sup>2 + 1)" by linarith
  show ?thesis by (rule mult_pos_pos[OF k pos])
qed

lemma soft_grad_nonzero:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "soft_grad \<kappa> d \<noteq> 0"
proof -
  have c: "0 < \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
    by (rule soft_grad_coeff_pos[OF d k])
  then have cne: "\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) \<noteq> 0" by linarith
  show ?thesis
    unfolding soft_grad_def using cne d by simp
qed

lemma soft_grad_norm_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "0 < norm (soft_grad \<kappa> d)"
  using soft_grad_nonzero[OF d k] by simp

lemma exists_small_rho_aux:
  fixes B G :: real
  assumes B: "0 < B" and G: "0 < G"
  shows "\<exists>\<rho>. 0 < \<rho> \<and> \<rho> < B \<and> 6 * \<rho> < G"
proof -
  have h1: "0 < B/2" by (rule divide_pos_pos[OF B]) simp
  have h2: "0 < G/12" by (rule divide_pos_pos[OF G]) simp
  have eB: "B = B/2 + B/2" by simp
  have eG: "G = 12 * (G/12)" by simp
  have le1: "min (B/2) (G/12) \<le> B/2" by simp
  have le2: "min (B/2) (G/12) \<le> G/12" by simp
  have p1: "0 < min (B/2) (G/12)" using h1 h2 by simp
  have p2: "min (B/2) (G/12) < B" using le1 h1 eB by linarith
  have p3: "6 * min (B/2) (G/12) < G"
  proof -
    have "6 * min (B/2) (G/12) \<le> 6 * (G/12)"
      by (rule mult_left_mono[OF le2]) simp
    then show ?thesis using h2 eG by linarith
  qed
  show ?thesis using p1 p2 p3 by blast
qed

lemma soft_gap_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0"
  shows "0 < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
proof -
  have R: "1 < sqrt ((norm d)\<^sup>2 + 1)" by (rule soft_R_gt_one[OF d])
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) < 1" using R Rp by (simp add: divide_less_eq)
  then have cpos: "0 < 1 - 1 / sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have dpos: "0 < norm d" using d by simp
  show ?thesis by (rule mult_pos_pos[OF cpos dpos])
qed

lemma soft_rho_exists:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and B: "0 < B"
  shows "\<exists>\<rho>. 0 < \<rho> \<and> \<rho> < B
      \<and> 6 * \<rho> < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
  by (rule exists_small_rho_aux[OF B soft_gap_pos[OF d]])

lemma sqrt_shift_diff_bound:
  fixes s t :: real
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "2 * (sqrt (t + 1) - sqrt (s + 1)) \<le> t - s"
proof -
  have tnn: "0 \<le> t" using s st by linarith
  have a1: "1 \<le> sqrt (t + 1)"
  proof -
    have "(1::real) = sqrt 1" by simp
    also have "sqrt (1::real) \<le> sqrt (t + 1)" by (rule real_sqrt_le_mono) (use tnn in linarith)
    finally show ?thesis .
  qed
  have b1: "1 \<le> sqrt (s + 1)"
  proof -
    have "(1::real) = sqrt 1" by simp
    also have "sqrt (1::real) \<le> sqrt (s + 1)" by (rule real_sqrt_le_mono) (use s in linarith)
    finally show ?thesis .
  qed
  have ab: "sqrt (s + 1) \<le> sqrt (t + 1)" by (rule real_sqrt_le_mono) (use st in linarith)
  have sq: "sqrt (t + 1) * sqrt (t + 1) - sqrt (s + 1) * sqrt (s + 1) = t - s"
  proof -
    have et: "sqrt (t + 1) * sqrt (t + 1) = t + 1"
      using real_sqrt_pow2[of "t + 1"] tnn by (simp add: power2_eq_square)
    have es: "sqrt (s + 1) * sqrt (s + 1) = s + 1"
      using real_sqrt_pow2[of "s + 1"] s by (simp add: power2_eq_square)
    show ?thesis unfolding et es by simp
  qed
  have fact: "(sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))
      = t - s"
  proof -
    have "(sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))
        = sqrt (t + 1) * sqrt (t + 1) - sqrt (s + 1) * sqrt (s + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> = t - s" by (rule sq)
    finally show ?thesis .
  qed
  have dnn: "0 \<le> sqrt (t + 1) - sqrt (s + 1)" using ab by linarith
  have sum2: "2 \<le> sqrt (t + 1) + sqrt (s + 1)" using a1 b1 by linarith
  have "(sqrt (t + 1) - sqrt (s + 1)) * 2
      \<le> (sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))"
    by (rule mult_left_mono[OF sum2 dnn])
  then show ?thesis unfolding fact by (simp add: mult_ac)
qed

text \<open>The bound variables are \<open>a\<close> and \<open>b\<close>, not \<open>s\<close> and \<open>t\<close>: with a variable
  named \<open>s\<close>, \<open>(\<kappa>/2)*s\<close> lexes as the Cartesian scalar-vector product
  token and fails to type-check.\<close>

lemma soft_pen_radial_mono:
  fixes a b :: real
  assumes k: "0 \<le> \<kappa>" and a0: "0 \<le> a" and ab: "a \<le> b"
  shows "(\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)
      \<le> (\<kappa>/2) * b - \<kappa> * (sqrt (b + 1) - 1)"
proof -
  have base: "2 * (sqrt (b + 1) - sqrt (a + 1)) \<le> b - a"
    by (rule sqrt_shift_diff_bound[OF a0 ab])
  have scaled: "\<kappa> * (2 * (sqrt (b + 1) - sqrt (a + 1))) \<le> \<kappa> * (b - a)"
    by (rule mult_left_mono[OF base k])
  have l: "\<kappa> * (2 * (sqrt (b + 1) - sqrt (a + 1)))
      = 2 * (\<kappa> * (sqrt (b + 1) - sqrt (a + 1)))" by (simp add: mult_ac)
  have rr: "\<kappa> * (b - a) = 2 * ((\<kappa>/2) * (b - a))" by simp
  have half: "\<kappa> * (sqrt (b + 1) - sqrt (a + 1)) \<le> (\<kappa>/2) * (b - a)"
    using scaled unfolding l rr by linarith
  have e1: "\<kappa> * (sqrt (b + 1) - sqrt (a + 1))
      = \<kappa> * (sqrt (b + 1) - 1) - \<kappa> * (sqrt (a + 1) - 1)"
    by (simp add: algebra_simps)
  have e2: "(\<kappa>/2) * (b - a) = (\<kappa>/2) * b - (\<kappa>/2) * a"
    by (rule right_diff_distrib)
  show ?thesis using half unfolding e1 e2 by linarith
qed

text \<open>The quadratic penalty bounds \<open>norm(x̂-ŷ)\<close> by dividing
  \<open>(\<alpha>/2)\<parallel>d\<parallel>\<^sup>2 \<le> C\<^sub>0\<close> through by \<open>\<alpha>\<close>; for a general penalty this needs
  coercivity instead (\<open>norm_lt_of_penalty_bound_gen\<close>).  \<open>soft_pen\<close> is
  linear in \<open>\<kappa>\<close>, so at fixed radius \<open>\<beta>\<close> its value eventually beats any
  fixed \<open>C\<^sub>0\<close> as \<open>\<kappa> \<rightarrow> \<infinity>\<close>, parallel to the \<open>\<alpha> \<rightarrow> \<infinity>\<close> mechanism for
  the quadratic case.\<close>

lemma sqrt_lt_half_plus_one:
  fixes c :: real
  assumes c: "0 < c"
  shows "sqrt (2*c + 1) < c + 1"
proof -
  have p: "0 < c + 1" using c by linarith
  have sq: "2*c + 1 < (c + 1)\<^sup>2"
  proof -
    have e: "(c + 1)\<^sup>2 = c\<^sup>2 + 2*c + 1"
      by (simp add: power2_eq_square algebra_simps)
    have "0 < c\<^sup>2" using c by simp
    then show ?thesis unfolding e by linarith
  qed
  have "sqrt (2*c + 1) < sqrt ((c + 1)\<^sup>2)" by (rule real_sqrt_less_mono[OF sq])
  also have "sqrt ((c + 1)\<^sup>2) = c + 1" using p by simp
  finally show ?thesis .
qed

lemma radial_profile_pos:
  fixes a :: real
  assumes k: "0 < \<kappa>" and a: "0 < a"
  shows "0 < (\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)"
proof -
  define c where "c = a/2"
  have cpos: "0 < c" unfolding c_def using a by simp
  have ac: "a = 2*c" unfolding c_def by simp
  have lt: "sqrt (2*c + 1) < c + 1" by (rule sqrt_lt_half_plus_one[OF cpos])
  have gap: "0 < (c + 1) - sqrt (2*c + 1)" using lt by linarith
  have h1: "(\<kappa>/2) * (2*c) = \<kappa> * c" by simp
  have e: "(\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)
      = \<kappa> * ((c + 1) - sqrt (2*c + 1))"
    unfolding ac h1 by (simp add: algebra_simps)
  show ?thesis unfolding e by (rule mult_pos_pos[OF k gap])
qed

lemma soft_pen_kappa_exists:
  fixes \<beta> C\<^sub>0 :: real
  assumes b: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
proof -
  define P where "P = (1/2) * \<beta>\<^sup>2 - 1 * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
  have bsq: "0 < \<beta>\<^sup>2" using b by simp
  have Ppos: "0 < P" unfolding P_def by (rule radial_profile_pos[OF _ bsq]) simp
  have Pne: "P \<noteq> 0" using Ppos by linarith
  \<comment> \<open>generic in the scalar, so simp never sees the quotient defining it\<close>
  have scale: "kk * P = (kk/2) * \<beta>\<^sup>2 - kk * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    for kk :: real
    unfolding P_def by (simp add: algebra_simps)
  define \<kappa> where "\<kappa> = (max 0 C\<^sub>0 + 1) / P"
  have numpos: "0 < max 0 C\<^sub>0 + 1" by simp
  have kpos: "0 < \<kappa>" unfolding \<kappa>_def by (rule divide_pos_pos[OF numpos Ppos])
  have prod: "\<kappa> * P = max 0 C\<^sub>0 + 1" unfolding \<kappa>_def using Pne by simp
  have "C\<^sub>0 < max 0 C\<^sub>0 + 1" by simp
  then have lt: "C\<^sub>0 < \<kappa> * P" using prod by linarith
  have final: "C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    using lt unfolding scale[of \<kappa>] .
  from kpos final show ?thesis by blast
qed


(*<*)
end
(*>*)
