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

text \<open>the jet form below writes the Hessian as a quadratic expression,
  matched to \<open>soft_hess\<close> by the quadratic-form reading of the Hessian, with the gradient
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



section \<open>The soft penalty's jet, Hessian and gradient field\<close>

lemma quartic_grad_derivative:
  fixes x y :: "real^'n::finite" and C :: real
  shows "((\<lambda>z. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h)) (at y)"
proof -
  have d: "((\<lambda>z. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. (4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h)) (at y)"
    by (auto intro!: derivative_eq_intros simp: inner_commute)
  have eq: "(\<lambda>h. (4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h)
      = (\<lambda>h. ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h)"
  proof (rule ext)
    fix h :: "real^'n"
    have "((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h
        = (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (mat 1 *v h)
          + (8 * C) *\<^sub>R (outer_prod (y - x) (y - x) *v h)"
      by (simp add: matrix_vector_mult_add_rdistrib
          scaleR_matrix_vector_assoc[symmetric])
    also have "\<dots> = (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h
          + (8 * C) *\<^sub>R (((y - x) \<bullet> h) *\<^sub>R (y - x))"
      by (simp add: op_matvec)
    finally show "(4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h
        = ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h"
      by simp
  qed
  show ?thesis using d unfolding eq .
qed

lemma soft_pen_gap:
  fixes d :: "real^'n::finite"
  shows "(\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d
      = \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) - \<kappa>"
proof -
  have n: "norm ((d, 1) :: (real^'n) \<times> real) = sqrt ((norm d)\<^sup>2 + 1)"
    by (simp add: norm_Pair)
  show ?thesis unfolding soft_pen_def n by (simp add: algebra_simps)
qed

theorem soft_pen_semiconcave:
  fixes \<kappa> :: real
  assumes k: "0 \<le> \<kappa>"
  shows "convex_on UNIV (\<lambda>d::real^'n::finite. (\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d)"
proof -
  have e: "(\<lambda>d::real^'n. (\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d)
      = (\<lambda>d::real^'n. \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) + (- \<kappa>))"
  proof (rule ext)
    fix d :: "real^'n"
    show "(\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d
        = \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) + (- \<kappa>)"
      using soft_pen_gap[of \<kappa> d] by simp
  qed
  have c1: "convex_on UNIV (\<lambda>d::real^'n. norm ((d, 1) :: (real^'n) \<times> real))"
    by (rule convex_on_norm_lift)
  have c2: "convex_on UNIV (\<lambda>d::real^'n. \<kappa> * norm ((d, 1) :: (real^'n) \<times> real))"
    by (rule convex_on_cmul[OF k c1])
  have c3: "convex_on UNIV (\<lambda>d::real^'n. - \<kappa>)"
    by (simp add: convex_on_const)
  show ?thesis unfolding e by (rule convex_on_add[OF c2 c3])
qed

text \<open>\<open>div_mul_div_cancel_aux\<close> lives in \<open>Soft_Penalty\<close>.\<close>

lemma soft_pen_quotient:
  fixes h :: "real^'n::finite"
  assumes h: "h \<noteq> 0"
  shows "soft_pen \<kappa> h / (norm h)\<^sup>2
      = \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
proof -
  have s0: "0 < (norm h)\<^sup>2" using h by simp
  have r: "0 < sqrt ((norm h)\<^sup>2 + 1) + 1"
  proof -
    have "0 \<le> sqrt ((norm h)\<^sup>2 + 1)" by simp
    then show ?thesis by linarith
  qed
  have sq: "sqrt ((norm h)\<^sup>2 + 1) * sqrt ((norm h)\<^sup>2 + 1) = (norm h)\<^sup>2 + 1"
    using s0 by simp
  have id: "sqrt ((norm h)\<^sup>2 + 1) - 1
      = (norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
  proof -
    have "(sqrt ((norm h)\<^sup>2 + 1) - 1) * (sqrt ((norm h)\<^sup>2 + 1) + 1)
        = (norm h)\<^sup>2"
      using sq by (simp add: algebra_simps)
    then show ?thesis using r by (simp add: field_simps)
  qed
  have "soft_pen \<kappa> h / (norm h)\<^sup>2
      = ((\<kappa>/2) * (norm h)\<^sup>2
          - \<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2"
    unfolding soft_pen_def id ..
  also have "\<dots> = ((\<kappa>/2) * (norm h)\<^sup>2) / (norm h)\<^sup>2
      - (\<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2"
    by (rule diff_divide_distrib)
  also have "((\<kappa>/2) * (norm h)\<^sup>2) / (norm h)\<^sup>2 = \<kappa>/2"
    using s0 by simp
  also have "(\<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2
      = \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
    by (rule div_mul_div_cancel_aux) (use s0 in linarith)
  finally show ?thesis .
qed

theorem soft_pen_vanishing_jet_at_zero:
  fixes \<kappa> :: real
  shows "((\<lambda>h::real^'n::finite. (soft_pen \<kappa> (0 + h) - soft_pen \<kappa> 0)
      / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have z: "soft_pen \<kappa> 0 = 0" by (simp add: soft_pen_def)
  have nz0: "\<forall>\<^sub>F h in at (0::real^'n). h \<noteq> 0"
    by (simp add: eventually_at_filter)
  have ev: "\<forall>\<^sub>F h in at (0::real^'n).
      \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)
        = (soft_pen \<kappa> (0 + h) - soft_pen \<kappa> 0) / (norm h)\<^sup>2"
    using nz0
  proof eventually_elim
    case (elim h)
    then show ?case unfolding z using soft_pen_quotient[OF elim] by simp
  qed
  have lim: "((\<lambda>h::real^'n. \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1))
      \<longlongrightarrow> \<kappa>/2 - \<kappa> / (sqrt ((norm (0::real^'n))\<^sup>2 + 1) + 1)) (at 0)"
    by (intro tendsto_intros) simp
  have val: "\<kappa>/2 - \<kappa> / (sqrt ((norm (0::real^'n))\<^sup>2 + 1) + 1) = 0"
    by simp
  show ?thesis
    by (rule Lim_transform_eventually[OF lim[unfolded val] ev])
qed

subsection \<open>Second-order expansion of the square root\<close>

text \<open>\<open>sqrt_diff_exact\<close>, \<open>sqrt_rhs_aux\<close>, \<open>sqrt_second_order_exact\<close> live in \<open>Soft_Penalty\<close>.\<close>

text \<open>\<open>soft_pen\<close>'s increment expands exactly: the quadratic part expands
  exactly, and the square-root part follows from \<open>sqrt_second_order_exact\<close>
  at \<open>u = \<parallel>d\<parallel>\<^sup>2 + 1\<close>, \<open>\<Delta> = 2(d \<bullet> h) + h \<bullet> h\<close>. The gradient is
  \<open>\<kappa>(1 - 1/R) d\<close> and the Hessian form is
  \<open>\<kappa>(1 - 1/R)(h \<bullet> h) + \<kappa>(d \<bullet> h)\<^sup>2/R\<^sup>3\<close>, both vanishing at \<open>d = 0\<close> where
  \<open>R = 1\<close>.\<close>

theorem soft_pen_expand:
  fixes d h :: "real^'n::finite"
  shows "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      = (\<kappa>/2) * (2*(d \<bullet> h) + (h \<bullet> h))
        - \<kappa> * ((2*(d \<bullet> h) + (h \<bullet> h)) / (2 * sqrt ((norm d)\<^sup>2 + 1))
            - (2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
              / (2 * sqrt ((norm d)\<^sup>2 + 1)
                  * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                     + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))"
proof -
  have u: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have D: "(norm (d + h))\<^sup>2 = (norm d)\<^sup>2 + (2*(d \<bullet> h) + (h \<bullet> h))"
    by (simp add: power2_norm_eq_inner
        inner_commute algebra_simps)
  have uD: "0 \<le> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))"
  proof -
    have e: "((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))
        = (norm (d + h))\<^sup>2 + 1"
      using D by simp
    show ?thesis unfolding e
      by (rule add_nonneg_nonneg[OF zero_le_power2 zero_le_one])
  qed
  have ex: "sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        - sqrt ((norm d)\<^sup>2 + 1)
      = (2*(d \<bullet> h) + (h \<bullet> h)) / (2 * sqrt ((norm d)\<^sup>2 + 1))
        - (2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
          / (2 * sqrt ((norm d)\<^sup>2 + 1)
              * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                 + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)"
    by (rule sqrt_second_order_exact[OF u uD])
  have split: "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      = (\<kappa>/2) * (2*(d \<bullet> h) + (h \<bullet> h))
        - \<kappa> * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
               - sqrt ((norm d)\<^sup>2 + 1))"
    unfolding soft_pen_def using D by (simp add: algebra_simps)
  show ?thesis unfolding split ex ..
qed

text \<open>\<open>soft_pen_rem_aux\<close> lives in \<open>Soft_Penalty\<close>.\<close>

theorem soft_pen_rem:
  fixes d h :: "real^'n::finite"
  shows "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
        - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
        - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
            + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2
      = \<kappa> * ((2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
              / (2 * sqrt ((norm d)\<^sup>2 + 1)
                  * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                     + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
        - \<kappa> * (d \<bullet> h)\<^sup>2 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have R: "sqrt ((norm d)\<^sup>2 + 1) \<noteq> 0" using up by simp
  show ?thesis
    unfolding soft_pen_expand
    by (rule soft_pen_rem_aux[OF R])
qed

text \<open>\<open>inner_sq_over_norm_sq_le\<close>, \<open>inner_sq_quotient_bounded\<close>, \<open>soft_pen_T_tendsto\<close>, \<open>soft_pen_bracket_tendsto\<close>, \<open>soft_pen_second_summand_tendsto\<close>, \<open>rem_split_aux\<close> live in \<open>Soft_Penalty\<close>.\<close>

text \<open>The jet assembles the analysis above via \<open>soft_pen_rem\<close> and
  \<open>rem_split_aux\<close>, killing the first summand by \<open>Lim_null_comparison\<close> and
  adding the second. Stated with the Hessian as a quadratic form;
  converting it to the matrix \<open>\<kappa>(1 - 1/R) I + (\<kappa>/R\<^sup>3) d d\<^sup>T\<close> is a separate
  step.\<close>

theorem soft_pen_jet_form:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
      - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
          + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
proof -
  let ?R = "sqrt ((norm d)\<^sup>2 + 1)"
  let ?T = "\<lambda>h::real^'n.
      sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))) + sqrt ((norm d)\<^sup>2 + 1)"
  let ?Br = "\<lambda>h::real^'n.
      2 / (sqrt ((norm d)\<^sup>2 + 1)
            * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
               + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
  let ?Sc = "\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)"
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < ?R" using up by simp
  have Rnz: "?R \<noteq> 0" using Rp by linarith
  have uDh: "0 \<le> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))" for h :: "real^'n"
  proof -
    have D: "(norm (d + h))\<^sup>2 = (norm d)\<^sup>2 + (2*(d \<bullet> h) + (h \<bullet> h))"
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    have e: "((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)) = (norm (d + h))\<^sup>2 + 1"
      using D by simp
    show ?thesis unfolding e
      by (rule add_nonneg_nonneg[OF zero_le_power2 zero_le_one])
  qed
  have Tnz: "?T h \<noteq> 0" for h :: "real^'n"
  proof -
    have "0 \<le> sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))"
      using uDh[of h] by simp
    then show ?thesis using Rp by linarith
  qed
  have nz0: "\<forall>\<^sub>F h in at (0::real^'n). h \<noteq> 0"
    by (simp add: eventually_at_filter)
  have gl: "((\<lambda>h::real^'n. (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>) \<longlongrightarrow> 0) (at 0)"
  proof -
    have "((\<lambda>h::real^'n. \<kappa> * ?Br h) \<longlongrightarrow> \<kappa> * 0) (at 0)"
      by (rule tendsto_mult[OF tendsto_const soft_pen_bracket_tendsto])
    then have "((\<lambda>h::real^'n. \<bar>\<kappa> * ?Br h\<bar>) \<longlongrightarrow> \<bar>\<kappa> * 0\<bar>) (at 0)"
      by (rule tendsto_rabs)
    then have "((\<lambda>h::real^'n. (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>)
        \<longlongrightarrow> (norm d)\<^sup>2 * \<bar>\<kappa> * 0\<bar>) (at 0)"
      by (rule tendsto_mult[OF tendsto_const])
    then show ?thesis by simp
  qed
  have cmp: "\<forall>\<^sub>F h in at (0::real^'n).
      norm (((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
        \<le> (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>"
    using nz0
  proof eventually_elim
    case (elim h)
    have nn: "0 \<le> (d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2" by simp
    have bd: "(d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2 \<le> (norm d)\<^sup>2"
      by (rule inner_sq_quotient_bounded[OF elim])
    have "norm (((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
        = ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * \<bar>\<kappa> * ?Br h\<bar>"
      using nn by (simp add: abs_mult)
    also have "\<dots> \<le> (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>"
      by (rule mult_right_mono[OF bd]) simp
    finally show ?case .
  qed
  have first: "((\<lambda>h::real^'n. ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
      \<longlongrightarrow> 0) (at 0)"
    by (rule Lim_null_comparison[OF cmp gl])
  have second: "((\<lambda>h::real^'n. ?Sc h) \<longlongrightarrow> 0) (at 0)"
    by (rule soft_pen_second_summand_tendsto)
  have sum0: "((\<lambda>h::real^'n.
      ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h) + ?Sc h) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF first second] by simp
  have ev: "\<forall>\<^sub>F h in at (0::real^'n).
      ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h) + ?Sc h
      = (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
          - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
          - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
              + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2)
        / (norm h)\<^sup>2"
    using nz0
  proof eventually_elim
    case (elim h)
    then have bnz: "h \<bullet> h \<noteq> 0" by simp
    have nb: "(norm h)\<^sup>2 = h \<bullet> h" by (simp add: power2_norm_eq_inner)
    show ?case
      unfolding soft_pen_rem nb
      by (rule rem_split_aux[symmetric, OF Rnz Tnz bnz])
  qed
  show ?thesis by (rule Lim_transform_eventually[OF sum0 ev])
qed

subsection \<open>The soft penalty's Hessian as a matrix\<close>

text \<open>The chain consumes \<open>h \<bullet> (Z *v h)\<close> as a matrix,
  \<open>Z = \<kappa>(1 - 1/R) I + (\<kappa>/R\<^sup>3) d d\<^sup>T\<close>; symmetry, needed by the general
  \<open>psd\<close> chain but not by the quadratic case where \<open>Z = \<alpha> I\<close> is symmetric
  for free, is an entrywise computation.\<close>

text \<open>\<open>soft_hess\<close> lives in \<open>Soft_Penalty\<close>.\<close>

lemma soft_hess_entry:
  fixes d :: "real^'n::finite"
  shows "soft_hess \<kappa> d $ i $ j
      = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) * (if i = j then 1 else 0)
        + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ i * d $ j)"
  by (simp add: soft_hess_def mat_def outer_prod_def)

lemma soft_hess_sym:
  fixes d :: "real^'n::finite"
  shows "transpose (soft_hess \<kappa> d) = soft_hess \<kappa> d"
proof -
  have "transpose (soft_hess \<kappa> d) $ i $ j = soft_hess \<kappa> d $ i $ j" for i j
  proof -
    have "transpose (soft_hess \<kappa> d) $ i $ j = soft_hess \<kappa> d $ j $ i"
      by (simp add: transpose_def)
    also have "\<dots> = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)))
            * (if j = i then 1 else 0)
          + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ j * d $ i)"
      by (rule soft_hess_entry)
    also have "\<dots> = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)))
            * (if i = j then 1 else 0)
          + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ i * d $ j)"
      by (simp add: mult.commute eq_commute)
    also have "\<dots> = soft_hess \<kappa> d $ i $ j"
      by (rule soft_hess_entry[symmetric])
    finally show ?thesis .
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma soft_hess_quadform:
  fixes d h :: "real^'n::finite"
  shows "h \<bullet> (soft_hess \<kappa> d *v h)
      = \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
        + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
proof -
  let ?A = "\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
  let ?B = "\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
  have s1: "(\<Sum>j\<in>UNIV. ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
      = ?A * (h $ i * h $ i)" for i
  proof -
    have "(\<Sum>j\<in>UNIV. ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
        = (\<Sum>j\<in>UNIV. if j = i then ?A * (h $ i * h $ j) else 0)"
      by (rule sum.cong) auto
    also have "\<dots> = ?A * (h $ i * h $ i)" by simp
    finally show ?thesis .
  qed
  have "h \<bullet> (soft_hess \<kappa> d *v h)
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. h $ i * (soft_hess \<kappa> d $ i $ j * h $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        ?A * (h $ i * ((if i = j then 1 else 0) * h $ j))
      + ?B * ((h $ i * d $ i) * (d $ j * h $ j)))"
    by (simp add: soft_hess_entry algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV.
          ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
      + (\<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j))))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>i\<in>UNIV. ?A * (h $ i * h $ i))
      + (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))"
    by (simp add: s1 sum.distrib)
  also have "(\<Sum>i\<in>UNIV. ?A * (h $ i * h $ i)) = ?A * (h \<bullet> h)"
    by (simp add: inner_vec_def sum_distrib_left)
  also have "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))
      = ?B * ((\<Sum>i\<in>UNIV. h $ i * d $ i) * (\<Sum>j\<in>UNIV. d $ j * h $ j))"
  proof -
    have a: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))
        = ?B * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (h $ i * d $ i) * (d $ j * h $ j))"
      by (simp add: sum_distrib_left)
    have b: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (h $ i * d $ i) * (d $ j * h $ j))
        = (\<Sum>i\<in>UNIV. h $ i * d $ i) * (\<Sum>j\<in>UNIV. d $ j * h $ j)"
      by (rule sum_product[symmetric])
    show ?thesis unfolding a b ..
  qed
  also have "(\<Sum>i\<in>UNIV. h $ i * d $ i) = d \<bullet> h"
    by (simp add: inner_vec_def mult.commute)
  also have "(\<Sum>j\<in>UNIV. d $ j * h $ j) = d \<bullet> h"
    by (simp add: inner_vec_def)
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

subsection \<open>The gradient field of \<open>soft_pen\<close>, and the two uniform bounds\<close>

text \<open>\<open>soft_grad\<close> lives in \<open>Soft_Penalty\<close>.\<close>

lemma soft_grad_inner:
  fixes d h :: "real^'n::finite"
  shows "soft_grad \<kappa> d \<bullet> h = \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)"
  unfolding soft_grad_def by simp

theorem soft_pen_jet_field:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      - soft_grad \<kappa> d \<bullet> h - (h \<bullet> (soft_hess \<kappa> d *v h))/2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
  using soft_pen_jet_form[where \<kappa> = \<kappa> and d = d]
  unfolding soft_grad_inner soft_hess_quadform .

text \<open>\<open>sqrt_norm_sq_add_one_ge_one\<close> lives in \<open>Soft_Penalty\<close>.\<close>

lemma soft_hess_quadform_bounds:
  fixes d z :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "0 \<le> z \<bullet> (soft_hess \<kappa> d *v z)"
    and "z \<bullet> (soft_hess \<kappa> d *v z) \<le> (2*\<kappa>) * (norm z)\<^sup>2"
proof -
  let ?R = "sqrt ((norm d)\<^sup>2 + 1)"
  have R1: "1 \<le> ?R" by (rule sqrt_norm_sq_add_one_ge_one)
  have Rp: "0 < ?R" using R1 by linarith
  have inv: "0 < 1 / ?R" using Rp by simp
  have invle: "1 / ?R \<le> 1" using R1 Rp by (simp add: divide_le_eq_1)
  have A0: "0 \<le> \<kappa> * (1 - 1 / ?R)"
    by (rule mult_nonneg_nonneg[OF k]) (use invle in linarith)
  have A1: "\<kappa> * (1 - 1 / ?R) \<le> \<kappa>"
    using mult_left_mono[OF _ k, of "1 - 1/?R" 1] inv by simp
  have zz: "z \<bullet> z = (norm z)\<^sup>2" by (simp add: power2_norm_eq_inner)
  have nz: "0 \<le> (norm z)\<^sup>2" by simp
  \<comment> \<open>the first summand\<close>
  have f0: "0 \<le> \<kappa> * (1 - 1 / ?R) * (z \<bullet> z)"
    unfolding zz by (rule mult_nonneg_nonneg[OF A0 nz])
  have f1: "\<kappa> * (1 - 1 / ?R) * (z \<bullet> z) \<le> \<kappa> * (norm z)\<^sup>2"
    unfolding zz by (rule mult_right_mono[OF A1 nz])
  \<comment> \<open>the second summand: Cauchy-Schwarz, then @{term "(norm d)\<^sup>2 \<le> ?R\<^sup>2"}\<close>
  have Rne: "?R \<noteq> 0" using Rp by linarith
  have R2: "?R * ?R = (norm d)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm d)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  have cs: "(d \<bullet> z)\<^sup>2 \<le> (norm d)\<^sup>2 * (norm z)\<^sup>2"
  proof -
    have "(d \<bullet> z)\<^sup>2 = \<bar>d \<bullet> z\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> (norm d * norm z)\<^sup>2"
      by (rule power_mono[OF Cauchy_Schwarz_ineq2[of d z]]) simp
    also have "\<dots> = (norm d)\<^sup>2 * (norm z)\<^sup>2" by (simp add: power_mult_distrib)
    finally show ?thesis .
  qed
  have dR: "(norm d)\<^sup>2 \<le> ?R * ?R" unfolding R2 by simp
  have cs2: "(d \<bullet> z)\<^sup>2 \<le> (?R * ?R) * (norm z)\<^sup>2"
    using cs mult_right_mono[OF dR nz] by linarith
  have cube: "?R ^ 3 = ?R * ?R * ?R" by (simp add: power3_eq_cube)
  have cubep: "0 < ?R ^ 3" using Rp by simp
  have s0: "0 \<le> \<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3"
    by (rule divide_nonneg_pos[OF mult_nonneg_nonneg[OF k] cubep]) simp
  have cancel: "a * (b * b * c) / (b * b * b) = a * c / b"
    if "b \<noteq> 0" for a b c :: real
    using that by (simp add: field_simps)
  have s1: "\<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3 \<le> \<kappa> * (norm z)\<^sup>2"
  proof -
    have "\<kappa> * (d \<bullet> z)\<^sup>2 \<le> \<kappa> * ((?R * ?R) * (norm z)\<^sup>2)"
      by (rule mult_left_mono[OF cs2 k])
    then have "\<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3 \<le> (\<kappa> * ((?R * ?R) * (norm z)\<^sup>2)) / ?R ^ 3"
      by (rule divide_right_mono) (use cubep in linarith)
    also have "(\<kappa> * ((?R * ?R) * (norm z)\<^sup>2)) / ?R ^ 3 = (\<kappa> * (norm z)\<^sup>2) / ?R"
      unfolding cube by (rule cancel[OF Rne])
    also have "(\<kappa> * (norm z)\<^sup>2) / ?R \<le> \<kappa> * (norm z)\<^sup>2"
    proof -
      have nn: "0 \<le> \<kappa> * (norm z)\<^sup>2" by (rule mult_nonneg_nonneg[OF k nz])
      have "\<kappa> * (norm z)\<^sup>2 * 1 \<le> \<kappa> * (norm z)\<^sup>2 * ?R"
        by (rule mult_left_mono[OF R1 nn])
      then show ?thesis using Rp by (simp add: divide_le_eq)
    qed
    finally show ?thesis .
  qed
  have expand: "z \<bullet> (soft_hess \<kappa> d *v z)
      = \<kappa> * (1 - 1 / ?R) * (z \<bullet> z) + \<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3"
    by (rule soft_hess_quadform)
  show "0 \<le> z \<bullet> (soft_hess \<kappa> d *v z)" unfolding expand using f0 s0 by linarith
  show "z \<bullet> (soft_hess \<kappa> d *v z) \<le> (2*\<kappa>) * (norm z)\<^sup>2"
    unfolding expand using f1 s1 by linarith
qed

lemma soft_hess_bound:
  fixes d z :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "\<bar>z \<bullet> (soft_hess \<kappa> d *v z)\<bar> \<le> (2*\<kappa>) * (norm z)\<^sup>2"
  using soft_hess_quadform_bounds[OF k, of z d] by linarith

subsection \<open>\<open>soft_grad\<close> is Lipschitz, at a non-sharp elementary constant\<close>

text \<open>\<open>norm_le_soft_R\<close>, \<open>abs_norm_diff_le\<close>, \<open>soft_R_lipschitz\<close>, \<open>soft_shrink\<close> live in \<open>Soft_Penalty\<close>.\<close>

lemma soft_grad_split:
  fixes d :: "real^'n::finite"
  shows "soft_grad \<kappa> d = \<kappa> *\<^sub>R d - \<kappa> *\<^sub>R soft_shrink d"
proof -
  have "soft_grad \<kappa> d = (\<kappa> - \<kappa> * (1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"
    unfolding soft_grad_def by (simp add: algebra_simps)
  also have "\<dots> = \<kappa> *\<^sub>R d - (\<kappa> * (1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"
    by (rule scaleR_left_diff_distrib)
  also have "\<dots> = \<kappa> *\<^sub>R d - \<kappa> *\<^sub>R ((1 / sqrt ((norm d)\<^sup>2 + 1)) *\<^sub>R d)"
    by simp
  finally show ?thesis unfolding soft_shrink_def .
qed

lemma soft_shrink_lipschitz:
  fixes x y :: "real^'n::finite"
  shows "norm (soft_shrink x - soft_shrink y) \<le> 2 * norm (x - y)"
proof -
  let ?s = "sqrt ((norm x)\<^sup>2 + 1)"
  let ?t = "sqrt ((norm y)\<^sup>2 + 1)"
  let ?D = "norm (soft_shrink x - soft_shrink y)"
  have s1: "1 \<le> ?s" by (rule sqrt_norm_sq_add_one_ge_one)
  have t1: "1 \<le> ?t" by (rule sqrt_norm_sq_add_one_ge_one)
  have sp: "0 < ?s" using s1 by linarith
  have tp: "0 < ?t" using t1 by linarith
  have stp: "0 < ?s * ?t" using sp tp by (rule mult_pos_pos)
  \<comment> \<open>clear the denominators\<close>
  have key: "(?s * ?t) *\<^sub>R (soft_shrink x - soft_shrink y) = ?t *\<^sub>R x - ?s *\<^sub>R y"
  proof -
    have "(?s * ?t) *\<^sub>R ((1/?s) *\<^sub>R x - (1/?t) *\<^sub>R y)
        = (?s * ?t) *\<^sub>R ((1/?s) *\<^sub>R x) - (?s * ?t) *\<^sub>R ((1/?t) *\<^sub>R y)"
      by (rule scaleR_right_diff_distrib)
    also have "\<dots> = ((?s * ?t) * (1/?s)) *\<^sub>R x - ((?s * ?t) * (1/?t)) *\<^sub>R y"
      by simp
    also have "\<dots> = ?t *\<^sub>R x - ?s *\<^sub>R y" using sp tp by simp
    finally show ?thesis unfolding soft_shrink_def .
  qed
  have decomp: "?t *\<^sub>R x - ?s *\<^sub>R y = ?t *\<^sub>R (x - y) + (?t - ?s) *\<^sub>R y"
    by (simp add:
          algebra_simps)
  \<comment> \<open>the triangle estimate\<close>
  have tri: "norm (?t *\<^sub>R (x - y) + (?t - ?s) *\<^sub>R y)
      \<le> norm (?t *\<^sub>R (x - y)) + norm ((?t - ?s) *\<^sub>R y)"
    by (rule norm_triangle_ineq)
  have e1: "norm (?t *\<^sub>R (x - y)) = ?t * norm (x - y)" using tp by simp
  have e2: "norm ((?t - ?s) *\<^sub>R y) = \<bar>?t - ?s\<bar> * norm y" by simp
  have absb: "\<bar>?t - ?s\<bar> \<le> norm (x - y)"
  proof -
    have "\<bar>?s - ?t\<bar> \<le> norm (x - y)" by (rule soft_R_lipschitz)
    then show ?thesis by (simp add: abs_minus_commute)
  qed
  have ny: "norm y \<le> ?t" by (rule norm_le_soft_R)
  have prod: "\<bar>?t - ?s\<bar> * norm y \<le> ?t * norm (x - y)"
  proof -
    have "\<bar>?t - ?s\<bar> * norm y \<le> norm (x - y) * norm y"
      by (rule mult_right_mono[OF absb]) simp
    also have "\<dots> \<le> norm (x - y) * ?t" by (rule mult_left_mono[OF ny]) simp
    also have "norm (x - y) * ?t = ?t * norm (x - y)" by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have bound: "norm (?t *\<^sub>R x - ?s *\<^sub>R y) \<le> 2 * (?t * norm (x - y))"
    unfolding decomp using tri e1 e2 prod by linarith
  \<comment> \<open>and cancel\<close>
  have step: "(?s * ?t) * ?D \<le> 2 * (?t * norm (x - y))"
  proof -
    have "(?s * ?t) * ?D = norm ((?s * ?t) *\<^sub>R (soft_shrink x - soft_shrink y))"
      using stp by simp
    also have "\<dots> = norm (?t *\<^sub>R x - ?s *\<^sub>R y)" unfolding key ..
    also have "\<dots> \<le> 2 * (?t * norm (x - y))" by (rule bound)
    finally show ?thesis .
  qed
  have r1: "(?s * ?t) * ?D = ?t * (?s * ?D)" by (simp add: mult_ac)
  have r2: "2 * (?t * norm (x - y)) = ?t * (2 * norm (x - y))"
    by (simp add: mult_ac)
  have cancel: "?t * (?s * ?D) \<le> ?t * (2 * norm (x - y))"
    using step unfolding r1 r2 .
  have sN: "?s * ?D \<le> 2 * norm (x - y)"
    by (rule mult_left_le_imp_le[OF cancel tp])
  have grow: "?D \<le> ?s * ?D"
  proof -
    have "1 * ?D \<le> ?s * ?D" by (rule mult_right_mono[OF s1]) simp
    then show ?thesis by simp
  qed
  show ?thesis using grow sN by linarith
qed

theorem soft_grad_lipschitz:
  fixes x y :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "norm (soft_grad \<kappa> x - soft_grad \<kappa> y) \<le> (3*\<kappa>) * norm (x - y)"
proof -
  let ?S = "soft_shrink x - soft_shrink y"
  have split: "soft_grad \<kappa> x - soft_grad \<kappa> y = \<kappa> *\<^sub>R (x - y) - \<kappa> *\<^sub>R ?S"
    unfolding soft_grad_split
    by (simp add: algebra_simps)
  have tri: "norm (\<kappa> *\<^sub>R (x - y) - \<kappa> *\<^sub>R ?S)
      \<le> norm (\<kappa> *\<^sub>R (x - y)) + norm (\<kappa> *\<^sub>R ?S)"
    by (rule norm_triangle_ineq4)
  have e1: "norm (\<kappa> *\<^sub>R (x - y)) = \<kappa> * norm (x - y)" using k by simp
  have e2: "norm (\<kappa> *\<^sub>R ?S) = \<kappa> * norm ?S" using k by simp
  have sh: "\<kappa> * norm ?S \<le> \<kappa> * (2 * norm (x - y))"
    by (rule mult_left_mono[OF soft_shrink_lipschitz k])
  have exp: "(3*\<kappa>) * norm (x - y) = \<kappa> * norm (x - y) + \<kappa> * (2 * norm (x - y))"
    by (simp add: algebra_simps)
  show ?thesis unfolding split exp using tri e1 e2 sh by linarith
qed

subsection \<open>The diagonal dichotomy for \<open>soft_pen\<close>\<close>

text \<open>\<open>soft_R_gt_one\<close>, \<open>soft_grad_coeff_pos\<close>, \<open>soft_grad_nonzero\<close>, \<open>soft_grad_norm_pos\<close> live in \<open>Soft_Penalty\<close>.\<close>

text \<open>Taking \<open>c\<close> to be the actual gradient norm at the maximiser cancels
  \<open>\<kappa>\<close> from \<open>(3\<kappa>)(2\<rho>) < \<parallel>soft_grad \<kappa> d\<parallel>\<close>, reducing to
  \<open>6\<rho> < (1 - 1/R d) \<parallel>d\<parallel>\<close>. Since every other constraint on \<open>\<rho>\<close> in the
  chain is an upper bound, such a \<open>\<rho>\<close> always exists.\<close>

lemma soft_grad_norm_eq:
  fixes d :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "norm (soft_grad \<kappa> d)
      = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) * norm d"
proof -
  have R1: "1 \<le> sqrt ((norm d)\<^sup>2 + 1)" by (rule sqrt_norm_sq_add_one_ge_one)
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) \<le> 1" using R1 Rp by (simp add: divide_le_eq_1)
  then have nn: "0 \<le> \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
    by (intro mult_nonneg_nonneg[OF k]) linarith
  show ?thesis unfolding soft_grad_def using nn by simp
qed

lemma soft_rsmall_of_rho:
  fixes d :: "real^'n::finite"
  assumes k: "0 < \<kappa>"
    and small: "6 * \<rho> < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
  shows "(3*\<kappa>) * (2*\<rho>) < norm (soft_grad \<kappa> d)"
proof -
  have knn: "0 \<le> \<kappa>" using k by linarith
  have eq: "norm (soft_grad \<kappa> d)
      = \<kappa> * ((1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d)"
    unfolding soft_grad_norm_eq[OF knn] by (simp add: mult_ac)
  have "\<kappa> * (6 * \<rho>) < \<kappa> * ((1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d)"
    by (rule mult_strict_left_mono[OF small k])
  moreover have "(3*\<kappa>) * (2*\<rho>) = \<kappa> * (6 * \<rho>)" by (simp add: mult_ac)
  ultimately show ?thesis unfolding eq by linarith
qed

text \<open>\<open>exists_small_rho_aux\<close>, \<open>soft_gap_pos\<close>, \<open>soft_rho_exists\<close> live in \<open>Soft_Penalty\<close>.\<close>

subsection \<open>Jensen's semiconvexity input, for a general penalty\<close>

text \<open>\<open>doubled_functional_semiconvex\<close> transcribed for a general penalty
  \<open>Pn\<close>, replacing the quadratic-specific semiconvexity step by the
  hypothesis \<open>sc\<close>; the doubled constant becomes \<open>1/\<epsilon> + 1/\<epsilon> + 2\<kappa>\<close>,
  matching the quadratic case at \<open>\<kappa> = \<alpha>\<close>.\<close>

lemma soft_pen_zero: "soft_pen \<kappa> (0 :: real^'n::finite) = 0"
  unfolding soft_pen_def by simp

text \<open>\<open>sqrt_shift_diff_bound\<close>, \<open>soft_pen_radial_mono\<close> live in \<open>Soft_Penalty\<close>.\<close>

lemma soft_pen_mono_norm:
  fixes x y :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and le: "norm x \<le> norm y"
  shows "soft_pen \<kappa> x \<le> soft_pen \<kappa> y"
proof -
  have s: "0 \<le> (norm x)\<^sup>2" by simp
  have st: "(norm x)\<^sup>2 \<le> (norm y)\<^sup>2" by (rule power_mono[OF le]) simp
  show ?thesis
    unfolding soft_pen_def by (rule soft_pen_radial_mono[OF k s st])
qed

lemma soft_pen_nonneg:
  fixes d :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "0 \<le> soft_pen \<kappa> d"
proof -
  have "norm (0 :: real^'n) \<le> norm d" by simp
  then have "soft_pen \<kappa> (0 :: real^'n) \<le> soft_pen \<kappa> d"
    by (rule soft_pen_mono_norm[OF k])
  then show ?thesis unfolding soft_pen_zero .
qed

lemma soft_pen_little_o:
  "((\<lambda>h::real^'n::finite. soft_pen \<kappa> h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  using soft_pen_vanishing_jet_at_zero[where \<kappa> = \<kappa>]
  unfolding soft_pen_zero by simp

text \<open>A diagonal maximiser's increment bound is exactly the one-sided
  hypothesis \<open>supersol_no_vanishing_jet_onesided\<close> consumes.\<close>

lemma diagonal_increment_onesided:
  fixes B :: "real^'n::finite \<Rightarrow> real"
  assumes dom: "\<forall>\<^sub>F hh in at 0. B (p + hh) - B p \<le> soft_pen \<kappa> hh"
    and c: "0 < c"
  shows "\<forall>\<^sub>F hh in at 0. (B (p + hh) - B p) / (norm hh)\<^sup>2 < c"
  by (rule onesided_of_dominated[OF dom soft_pen_little_o c])

lemma soft_pen_neg:
  fixes d :: "real^'n::finite"
  shows "soft_pen \<kappa> (- d) = soft_pen \<kappa> d"
  unfolding soft_pen_def by simp

text \<open>\<open>diagonal_max_increments\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

lemma diagonal_max_increment_soft:
  fixes A B :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + B y - soft_pen \<kappa> (x - y) \<le> A p + B p - soft_pen \<kappa> (p - p)"
    and pK: "p \<in> K" and hK: "p + h \<in> K"
  shows "B (p + h) - B p \<le> soft_pen \<kappa> h"
proof -
  have base: "B (p + h) - B p \<le> soft_pen \<kappa> (p - (p + h))"
    by (rule diagonal_max_increments(1)[OF mx soft_pen_zero pK hK])
  have e: "p - (p + h) = - h" by simp
  have "B (p + h) - B p \<le> soft_pen \<kappa> (- h)" using base unfolding e .
  then show ?thesis unfolding soft_pen_neg .
qed

text \<open>\<open>gap_split_aux\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


subsection \<open>Coercivity of \<open>soft_pen\<close>: recovering the norm bound\<close>

text \<open>\<open>sqrt_lt_half_plus_one\<close>, \<open>radial_profile_pos\<close> live in \<open>Soft_Penalty\<close>.\<close>

lemma soft_pen_ge_radial:
  fixes x :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and bnn: "0 \<le> \<beta>" and b: "\<beta> \<le> norm x"
  shows "(\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1) \<le> soft_pen \<kappa> x"
proof -
  have a0: "0 \<le> \<beta>\<^sup>2" by simp
  have ab: "\<beta>\<^sup>2 \<le> (norm x)\<^sup>2" by (rule power_mono[OF b bnn])
  show ?thesis
    unfolding soft_pen_def by (rule soft_pen_radial_mono[OF k a0 ab])
qed

text \<open>The packaged coercivity, in the shape \<open>norm_lt_of_penalty_bound_gen\<close>
  consumes: hypothesis \<open>big\<close> says \<open>\<kappa>\<close> is large enough that the penalty at
  radius \<open>\<beta>\<close> exceeds \<open>C\<^sub>0\<close>, and such \<open>\<kappa>\<close> always exists since the radial
  profile is strictly positive and linear in \<open>\<kappa>\<close> (\<open>soft_pen_kappa_exists\<close>).\<close>

lemma soft_pen_coercive_outside:
  fixes x :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and bnn: "0 \<le> \<beta>"
    and big: "C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    and b: "\<beta> \<le> norm x"
  shows "C\<^sub>0 < soft_pen \<kappa> x"
  using big soft_pen_ge_radial[OF k bnn b] by linarith

text \<open>\<open>soft_pen_kappa_exists\<close> lives in \<open>Soft_Penalty\<close>.\<close>

text \<open>The \<open>y\<close>-side of the two-domain interface: at the maximiser the penalty
  is bounded by the range, so a large enough \<open>\<kappa>\<^sub>P\<close> pins \<open>y^h\<close> to \<open>x^h\<close>;
  \<open>x^h\<close> is near \<open>K\<close>, and \<open>two_domain_gap\<close> keeps \<open>K\<close> a positive distance
  from \<open>\<partial>K'\<close>.  Composing the three gives the \<open>fary\<close> hypothesis, needed
  only on the \<open>y\<close>-side.\<close>

lemma pin_of_penalty_bound:
  fixes A Bfun :: "real^'n::finite \<Rightarrow> real" and xh yh :: "real^'n"
  assumes k: "0 \<le> \<kappa>\<^sub>P" and bnn: "0 \<le> \<beta>"
    and Aub: "\<And>x. A x \<le> Bu" and Bnp: "\<And>y. Bfun y \<le> 0"
    and Mnn: "0 \<le> M"
    and mx: "M \<le> A xh + Bfun yh - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and big: "Bu < (\<kappa>\<^sub>P/2)*\<beta>\<^sup>2 - \<kappa>\<^sub>P*(sqrt (\<beta>\<^sup>2 + 1) - 1)"
  shows "norm (xh - yh) < \<beta>"
proof (rule ccontr)
  assume "\<not> norm (xh - yh) < \<beta>"
  then have b: "\<beta> \<le> norm (xh - yh)" by linarith
  have lo: "Bu < soft_pen \<kappa>\<^sub>P (xh - yh)"
    by (rule soft_pen_coercive_outside[OF k bnn big b])
  have hi: "soft_pen \<kappa>\<^sub>P (xh - yh) \<le> Bu"
    using mx Aub[of xh] Bnp[of yh] Mnn by linarith
  from lo hi show False by linarith
qed

text \<open>\<open>fary_of_pin\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>Continuity of \<open>soft_pen\<close> is the single hypothesis
  \<open>doubling_maximiser_exists_gen\<close> needs about the penalty.  \<open>sqrt\<close> is
  total in Isabelle, so no positivity side condition is needed.\<close>

lemma soft_pen_continuous:
  "continuous_on UNIV (soft_pen \<kappa> :: real^'n::finite \<Rightarrow> real)"
  unfolding soft_pen_def by (intro continuous_intros)

theorem doubling_maximiser_exists_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - soft_pen \<kappa> (x - y)
        \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
  by (rule doubling_maximiser_exists_gen[OF cK neK cu cw soft_pen_continuous])

text \<open>The sup-convolution form matches the \<open>mxKK\<close> hypothesis of
  \<open>comparison_from_localised_maximiser_soft\<close>, a transcription of
  \<open>doubling_maximiser_supconv\<close> with continuity of the two sup-convolutions
  free from \<open>supconv_continuous\<close>.\<close>

corollary doubling_maximiser_supconv_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa> (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa> (xh - yh)"
proof -
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu e] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw e] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  have "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) - soft_pen \<kappa> (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh - (- supconv (- w) \<epsilon> yh)
        - soft_pen \<kappa> (xh - yh)"
    by (rule doubling_maximiser_exists_soft[OF cK neK cA cB])
  then show ?thesis by simp
qed

subsection \<open>The \<open>\<kappa> \<rightarrow> \<infinity>\<close> step for \<open>soft_pen\<close>: the maximiser closes up\<close>

text \<open>The \<open>soft_pen\<close> analogue of \<open>doubling_dist_bound\<close>: the penalty at radius
  \<open>\<beta>\<close> grows linearly in \<open>\<kappa>\<close> and eventually exceeds the fixed \<open>C\<^sub>0\<close>,
  forcing the maximiser inside radius \<open>\<beta>\<close>.  The quantifier order matters:
  \<open>\<beta>\<close> is given first, \<open>\<kappa>\<close> chosen afterwards, so the statement produces
  \<open>\<kappa>\<close> and the maximiser together.\<close>

lemma doubling_near_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - soft_pen \<kappa> (x - y)
          \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
    and k: "0 \<le> \<kappa>"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
    and bnn: "0 \<le> \<beta>"
    and big: "C - (u z - w z) < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
  shows "dist xh yh < \<beta>"
proof -
  have pb: "soft_pen \<kappa> (xh - yh) \<le> C - (u z - w z)"
    by (rule doubling_penalty_bound_gen[OF mx soft_pen_zero xh yh z bnd])
  have coer: "C - (u z - w z) < soft_pen \<kappa> x" if "\<beta> \<le> norm x"
    for x :: "real^'n"
    by (rule soft_pen_coercive_outside[OF k bnn big that])
  \<comment> \<open>pin every argument: \<open>?Pn ?d\<close> is higher-order and admits several unifiers\<close>
  have "norm (xh - yh) < \<beta>"
    by (rule norm_lt_of_penalty_bound_gen
        [where Pn = "soft_pen \<kappa>" and d = "xh - yh"
           and C = "C - (u z - w z)" and \<beta> = \<beta>,
         OF pb coer])
  then show ?thesis by (simp add: dist_norm)
qed

theorem doubling_close_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and z: "z \<in> K"
    and bnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> u x - w y \<le> C"
    and bpos: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K. u x - w y - soft_pen \<kappa> (x - y)
          \<le> u xh - w yh - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
proof -
  obtain \<kappa> where kpos: "0 < \<kappa>"
    and big: "C - (u z - w z)
        < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    using soft_pen_kappa_exists[OF bpos] by blast
  have knn: "0 \<le> \<kappa>" using kpos by linarith
  have bnn: "0 \<le> \<beta>" using bpos by linarith
  obtain xh yh where xh: "xh \<in> K" and yh: "yh \<in> K"
    and mx: "\<forall>x\<in>K. \<forall>y\<in>K. u x - w y - soft_pen \<kappa> (x - y)
        \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
    using doubling_maximiser_exists_soft[OF cK neK cu cw, where \<kappa> = \<kappa>] by blast
  have mxa: "u x - w y - soft_pen \<kappa> (x - y)
      \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mx that by blast
  have near: "dist xh yh < \<beta>"
    by (rule doubling_near_soft
        [OF mxa knn xh yh z bnd[OF xh yh] bnn big])
  show ?thesis using kpos xh yh mx near by blast
qed

text \<open>The \<open>\<kappa> \<rightarrow> \<infinity>\<close> step in the sup-convolution shape the assembly consumes,
  with the same sign flip as \<open>doubling_maximiser_supconv_soft\<close>:
  instantiate at \<open>u := supconv(\<theta>u)\<epsilon>\<close> and \<open>w := \<lambda>y. -supconv(-w)\<epsilon> y\<close>.\<close>

theorem doubling_close_maximiser_supconv_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
    and z: "z \<in> K"
    and bnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y \<le> C"
    and bpos: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa> (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
           - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
proof -
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu e] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw e] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  have bnd': "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) \<le> C"
    if "x \<in> K" "y \<in> K" for x y
    using bnd[OF that] by simp
  have "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) - soft_pen \<kappa> (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh - (- supconv (- w) \<epsilon> yh)
           - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
    by (rule doubling_close_maximiser_soft
        [where u = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>"
           and w = "\<lambda>y. - supconv (- w) \<epsilon> y" and K = K and z = z and C = C
           and \<beta> = \<beta>,
         OF cK neK cA cB z bnd' bpos])
  then show ?thesis by simp
qed

subsection \<open>The \<open>\<epsilon> \<rightarrow> 0\<close> step: the sup-convolution is uniformly close on \<open>K\<close>\<close>

text \<open>\<open>exists_eps_aux\<close>, \<open>eps_mono_aux\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

(*<*)
end
(*>*)
