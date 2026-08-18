section \<open>Elementary power inequalities\<close>

(*<*)
theory Power_Inequalities
  imports Complex_Main
begin

(*>*)

text \<open>
  The real inequalities that the fourth-moment estimates, the quadratic
  variation and the pathwise quadratic variation all run on.  They were
  proved four times over, in four theories, in three sessions; they are
  collected here, ahead of everything that uses them, and nothing below
  this theory proves an arithmetic fact of this kind again.

  Everything reduces to the two-square bound \<open>2\<bar>a\<bar>\<bar>b\<bar> \<le> a\<^sup>2 + b\<^sup>2\<close>
  (@{thm [source] sum_squares_bound}); no Cauchy--Schwarz or Young
  machinery is needed.  Polynomial identities are discharged with
  \<open>algebra\<close> and the linear assembly with \<open>linarith\<close>, keeping every
  nonlinear term as a shared atom.
\<close>

subsection \<open>Squares\<close>

lemma sq_diff_le:
  fixes a b :: real
  shows "(a - b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2"
proof -
  have "2 * a * (- b) \<le> a\<^sup>2 + (- b)\<^sup>2"
    by (rule sum_squares_bound)
  then have bnd: "- (2 * (a * b)) \<le> a\<^sup>2 + b\<^sup>2"
    by simp
  have exp: "(a - b)\<^sup>2 = a\<^sup>2 - 2 * (a * b) + b\<^sup>2"
    by (simp add: power2_diff)
  show ?thesis
    using bnd exp by linarith
qed

lemma square_add_le_two:
  fixes a b :: real
  shows "(a + b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2"
  using sq_diff_le[of a "- b"] by simp

subsection \<open>A bounded function has a bounded second moment\<close>

lemma abs_prod_le_sq:
  fixes a b :: real
  shows "\<bar>a * b\<bar> \<le> a\<^sup>2 + b\<^sup>2"
proof (rule abs_leI)
  have "2 * a * b \<le> a\<^sup>2 + b\<^sup>2"
    by (rule sum_squares_bound)
  moreover have "0 \<le> a\<^sup>2" and "0 \<le> b\<^sup>2"
    by simp_all
  ultimately show "a * b \<le> a\<^sup>2 + b\<^sup>2" by linarith
next
  have "2 * a * (- b) \<le> a\<^sup>2 + (- b)\<^sup>2"
    by (rule sum_squares_bound)
  then have "- (2 * (a * b)) \<le> a\<^sup>2 + b\<^sup>2" by simp
  moreover have "0 \<le> a\<^sup>2" and "0 \<le> b\<^sup>2"
    by simp_all
  ultimately show "- (a * b) \<le> a\<^sup>2 + b\<^sup>2" by linarith
qed

lemma sq_mono_abs:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "x\<^sup>2 \<le> b\<^sup>2"
  using power_mono[OF assms abs_ge_zero, of 2] by simp

lemma sq_abs_mono:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "\<bar>x\<^sup>2\<bar> \<le> b\<^sup>2"
  using sq_mono_abs[OF assms] by simp

lemma sq_diff_le_fourth:
  fixes x a :: real
  shows "(x\<^sup>2 - a)\<^sup>2 \<le> 2 * x^4 + 2 * a\<^sup>2"
proof -
  have "(x\<^sup>2 - a)\<^sup>2 \<le> 2 * (x\<^sup>2)\<^sup>2 + 2 * a\<^sup>2" by (rule sq_diff_le)
  moreover have "(x\<^sup>2)\<^sup>2 = x^4" by algebra
  ultimately show ?thesis by simp
qed

lemma sq_times_sq: "(x::real)\<^sup>2 * x\<^sup>2 = x^4"
  by algebra

subsection \<open>Pointwise inequalities for the fourth-moment recursion\<close>

text \<open>
  Everything below reduces to the two-square bound \<open>2 \<bar>a\<bar> \<bar>b\<bar> \<le> a\<^sup>2 + b\<^sup>2\<close>
  (@{thm [source] sum_squares_bound}); no Cauchy-Schwarz or Young machinery is
  needed. Polynomial identities are discharged with \<open>algebra\<close> and the linear
  assembly with \<open>linarith\<close>, keeping every nonlinear term as a shared atom.
\<close>

lemma two_abs_prod_le_squares: "2 * \<bar>a\<bar> * \<bar>b\<bar> \<le> a\<^sup>2 + b\<^sup>2" for a b :: real
  using sum_squares_bound[of "\<bar>a\<bar>" "\<bar>b\<bar>"] by simp

lemma abs_prod_le_half_squares: "\<bar>a * b\<bar> \<le> a\<^sup>2 / 2 + b\<^sup>2 / 2" for a b :: real
proof -
  have "2 * \<bar>a * b\<bar> \<le> a\<^sup>2 + b\<^sup>2"
    using two_abs_prod_le_squares[of a b] by (simp add: abs_mult)
  thus ?thesis by linarith
qed

lemma sq_le_half_add_half_pow4: "x\<^sup>2 \<le> 1/2 + x^4/2" for x :: real
proof -
  have "0 \<le> (x\<^sup>2 - 1)\<^sup>2" by simp
  moreover have "(x\<^sup>2 - 1)\<^sup>2 = x^4 - 2*x\<^sup>2 + 1" by algebra
  ultimately show ?thesis by linarith
qed

lemma prod_sq_le_half_pow4: "a\<^sup>2 * b\<^sup>2 \<le> a^4/2 + b^4/2" for a b :: real
proof -
  have "0 \<le> (a\<^sup>2 - b\<^sup>2)\<^sup>2" by simp
  moreover have "(a\<^sup>2 - b\<^sup>2)\<^sup>2 = a^4 - 2*(a\<^sup>2*b\<^sup>2) + b^4" by algebra
  ultimately show ?thesis by linarith
qed

lemma pow4_nonneg: "0 \<le> (x::real)^4"
proof -
  have "(x::real)^4 = (x\<^sup>2)\<^sup>2" by algebra
  then show ?thesis by simp
qed

lemma pow4_diff_le: "(a - b)^4 \<le> 8*a^4 + 8*b^4" for a b :: real
proof -
  have 1: "(a - b)\<^sup>2 \<le> 2*a\<^sup>2 + 2*b\<^sup>2"
    using square_add_le_two[of a "-b"] by simp
  have 2: "((a - b)\<^sup>2)\<^sup>2 \<le> (2*a\<^sup>2 + 2*b\<^sup>2)\<^sup>2"
    by (rule power_mono[OF 1 zero_le_power2])
  have 3: "((a - b)\<^sup>2)\<^sup>2 = (a - b)^4" by algebra
  have 4: "(2*a\<^sup>2 + 2*b\<^sup>2)\<^sup>2 = 4*a^4 + 8*(a\<^sup>2*b\<^sup>2) + 4*b^4" by algebra
  have 5: "a\<^sup>2*b\<^sup>2 \<le> a^4/2 + b^4/2" by (rule prod_sq_le_half_pow4)
  from 2 3 4 5 show ?thesis by linarith
qed

lemma abs_cube_prod_le_pow4: "\<bar>a^3 * b\<bar> \<le> 3/4*a^4 + 1/4*b^4" for a b :: real
proof -
  have e: "a^3 * b = a\<^sup>2 * (a * b)" by algebra
  have 1: "\<bar>a^3 * b\<bar> = a\<^sup>2 * \<bar>a * b\<bar>"
    unfolding e by (simp add: abs_mult)
  have 2: "\<bar>a * b\<bar> \<le> a\<^sup>2/2 + b\<^sup>2/2" by (rule abs_prod_le_half_squares)
  have 3: "a\<^sup>2 * \<bar>a * b\<bar> \<le> a\<^sup>2 * (a\<^sup>2/2 + b\<^sup>2/2)"
    by (rule mult_left_mono[OF 2]) simp
  have 4: "a\<^sup>2 * (a\<^sup>2/2 + b\<^sup>2/2) = a^4/2 + (a\<^sup>2*b\<^sup>2)/2" by algebra
  have 5: "a\<^sup>2*b\<^sup>2 \<le> a^4/2 + b^4/2" by (rule prod_sq_le_half_pow4)
  from 1 3 4 5 show ?thesis by linarith
qed

lemma abs_prod_cube_le_pow4: "\<bar>a * b^3\<bar> \<le> 1/4*a^4 + 3/4*b^4" for a b :: real
proof -
  have e: "a * b^3 = b^3 * a" by algebra
  show ?thesis
    unfolding e using abs_cube_prod_le_pow4[of b a] by linarith
qed

lemma four_prod_cube_le: "4*(y*d^3) \<le> 2*(y\<^sup>2*d\<^sup>2) + 2*d^4" for y d :: real
proof -
  have a: "4*(y*d^3) \<le> 4*(\<bar>y*d\<bar>*d\<^sup>2)"
  proof -
    have e: "y*d^3 = (y*d)*d\<^sup>2" by algebra
    have "(y*d)*d\<^sup>2 \<le> \<bar>(y*d)*d\<^sup>2\<bar>" by (rule abs_ge_self)
    also have "\<bar>(y*d)*d\<^sup>2\<bar> = \<bar>y*d\<bar>*d\<^sup>2" by (simp add: abs_mult)
    finally show ?thesis unfolding e by linarith
  qed
  have b: "2*\<bar>y*d\<bar> \<le> y\<^sup>2 + d\<^sup>2"
    using two_abs_prod_le_squares[of y d] by (simp add: abs_mult)
  have c: "4*(\<bar>y*d\<bar>*d\<^sup>2) = (2*\<bar>y*d\<bar>) * (2*d\<^sup>2)" by algebra
  have d': "(2*\<bar>y*d\<bar>)*(2*d\<^sup>2) \<le> (y\<^sup>2+d\<^sup>2)*(2*d\<^sup>2)"
    by (rule mult_right_mono[OF b]) simp
  have e': "(y\<^sup>2+d\<^sup>2)*(2*d\<^sup>2) = 2*(y\<^sup>2*d\<^sup>2) + 2*d^4" by algebra
  from a c d' e' show ?thesis by linarith
qed

lemma pow4_binomial:
  "(y + d)^4 = y^4 + 4*(y^3*d) + 6*(y\<^sup>2*d\<^sup>2) + 4*(y*d^3) + d^4" for y d :: real
  by algebra

subsection \<open>Fourth powers\<close>

lemma fourth_mono_abs:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "x^4 \<le> b^4"
proof -
  have "(x\<^sup>2)\<^sup>2 \<le> (b\<^sup>2)\<^sup>2" by (rule power_mono[OF sq_mono_abs[OF assms]]) simp
  moreover have "(x\<^sup>2)\<^sup>2 = x^4" and "(b\<^sup>2)\<^sup>2 = b^4" by algebra+
  ultimately show ?thesis by simp
qed

lemma fourth_abs_mono:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "\<bar>x^4\<bar> \<le> b^4"
  using power_mono[OF assms abs_ge_zero, of 4] by (simp add: power_abs)

lemma prod_minus_sq_bound:
  fixes a b c :: real
  shows "(a * b - c)\<^sup>2 \<le> a^4 + b^4 + 2 * c\<^sup>2"
proof -
  have e1: "2 * (a*b)\<^sup>2 + 2 * c\<^sup>2 - (a*b - c)\<^sup>2 = (a*b + c)\<^sup>2"
    by (simp add: power2_diff power2_sum)
  have s1: "(a*b - c)\<^sup>2 \<le> 2 * (a*b)\<^sup>2 + 2 * c\<^sup>2"
    using e1 zero_le_power2[of "a*b + c"] by linarith
  have e2: "a^4 + b^4 - 2 * (a*b)\<^sup>2 = (a\<^sup>2 - b\<^sup>2)\<^sup>2"
    by (simp add: power2_diff power2_eq_square power4_eq_xxxx algebra_simps)
  have s2: "2 * (a*b)\<^sup>2 \<le> a^4 + b^4"
    using e2 zero_le_power2[of "a\<^sup>2 - b\<^sup>2"] by linarith
  from s1 s2 show ?thesis by linarith
qed

lemma fourth_power_sum_bound:
  fixes a b :: real
  shows "(a + b)^4 \<le> 8 * (a^4 + b^4)"
proof -
  have e1: "2 * (a\<^sup>2 + b\<^sup>2) - (a + b)\<^sup>2 = (a - b)\<^sup>2"
    by (simp add: power2_diff power2_sum)
  have s1: "(a + b)\<^sup>2 \<le> 2 * (a\<^sup>2 + b\<^sup>2)"
    using e1 zero_le_power2[of "a - b"] by linarith
  have nn: "0 \<le> (a + b)\<^sup>2" by simp
  have s2: "((a + b)\<^sup>2)\<^sup>2 \<le> (2 * (a\<^sup>2 + b\<^sup>2))\<^sup>2"
    by (rule power_mono[OF s1 nn])
  have e2: "a^4 + b^4 - 2 * (a\<^sup>2 * b\<^sup>2) = (a\<^sup>2 - b\<^sup>2)\<^sup>2"
    by (simp add: power2_diff power2_eq_square power4_eq_xxxx algebra_simps)
  have s3: "(a\<^sup>2 + b\<^sup>2)\<^sup>2 \<le> 2 * (a^4 + b^4)"
  proof -
    have s0: "2 * (a\<^sup>2 * b\<^sup>2) \<le> a^4 + b^4"
      using e2 zero_le_power2[of "a\<^sup>2 - b\<^sup>2"] by linarith
    have "(a\<^sup>2 + b\<^sup>2)\<^sup>2 = a^4 + 2 * (a\<^sup>2 * b\<^sup>2) + b^4"
      by (simp add: power2_sum power2_eq_square power4_eq_xxxx algebra_simps)
    \<comment> \<open>\<open>linarith\<close> balks here although the problem is linear in the atoms
        \<open>(a²+b²)²\<close>, \<open>a⁴\<close>, \<open>b⁴\<close>, \<open>a²b²\<close>; \<open>argo\<close> is the documented fix.\<close>
    then show ?thesis using s0 by argo
  qed
  have e3: "((a + b)\<^sup>2)\<^sup>2 = (a + b)^4"
    by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
  have e4: "(2 * (a\<^sup>2 + b\<^sup>2))\<^sup>2 = 4 * (a\<^sup>2 + b\<^sup>2)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  from s2 s3 show ?thesis unfolding e3 e4 by linarith
qed

lemma sum_pow4_le_max_times_sum:
  fixes d :: "nat \<Rightarrow> real"
  shows "(\<Sum>k<Suc m. (d k)^4)
           \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (\<Sum>k<Suc m. (d k)\<^sup>2)"
proof -
  have fin: "finite ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m})" by simp
  have per: "(d k)^4 \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2"
    if k: "k \<in> {..<Suc m}" for k
  proof -
    have mem: "(d k)\<^sup>2 \<in> (\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}" using k by auto
    have le: "(d k)\<^sup>2 \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m})"
      by (rule Max_ge[OF fin mem])
    have "(d k)^4 = (d k)\<^sup>2 * (d k)\<^sup>2" by (simp add: sq_times_sq)
    also have "\<dots> \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2"
      by (rule mult_right_mono[OF le zero_le_power2])
    finally show ?thesis .
  qed
  have "(\<Sum>k<Suc m. (d k)^4)
          \<le> (\<Sum>k<Suc m. Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2)"
    by (rule sum_mono[OF per])
  also have "\<dots> = Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (\<Sum>k<Suc m. (d k)\<^sup>2)"
    by (rule sum_distrib_left[symmetric])
  finally show ?thesis .
qed

(*<*)
end
(*>*)
