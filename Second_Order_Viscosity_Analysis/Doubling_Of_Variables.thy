section \<open>Doubling of variables\<close>

(*<*)
theory Doubling_Of_Variables
  imports Theorem_On_Sums "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

text \<open>
  \<^emph>\<open>Doubling of variables\<close> is the device that makes comparison between
  viscosity solutions work.  To compare a subsolution \<open>u\<close> with a
  supersolution \<open>w\<close> one cannot differentiate either, so instead one
  maximises the \<^emph>\<open>doubled\<close> functional
  \<open>\<Phi>(x,y) = u x - w y - P(x - y)\<close>
  over a pair of variables, with a penalty \<open>P\<close> that punishes \<open>x \<noteq> y\<close>.
  Freezing either variable at a maximising pair \<open>(x\<^sup>h, y\<^sup>h)\<close> turns the
  two-variable maximum into a one-variable touching condition, which is
  exactly what the definition of a viscosity solution can be applied to; and
  as the penalty stiffens, the maximising pair collapses onto the diagonal
  and recovers a bound on \<open>u - w\<close> itself.

  This theory is the whole apparatus that argument needs, and nothing about
  any particular equation: existence and location of the maximising pair,
  the penalty and gradient estimates, the second-order jets of the doubled
  functional and their slices in each variable, Jensen's tilt and its
  removal, the block structure of the resulting Hessians and the bounds on
  them, and the sequence lemmas used to pass to a limit.  It builds on
  @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}, which supplies
  the matrix inequality between the two diagonal blocks.

  Everything is at \<open>'a::euclidean_space\<close> except the 33 statements that
  produce a matrix, which stay at \<open>real^'n\<close>.
\<close>

text \<open>A supersolution is usually tested against a quadratic touching it from
  below on a ball.  The two bounds below say that such a quadratic is bounded
  above and below on any bounded set, so the touching can be read off on a
  compact domain without boundedness having to be assumed separately.  Every
  test function built here is a polynomial, so no class wider than \<open>C\<^sup>2\<close>
  is ever needed.\<close>

lemma quad_bdd_above_on_bounded:
  fixes p yh :: "real^'n::finite" and M :: "real^'n^'n"
    and K :: "(real^'n) set"
  assumes Kb: "bounded K"
  obtains B where "\<And>z. z \<in> K \<Longrightarrow>
    p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2 \<le> B"
proof -
  obtain R where R: "\<And>z. z \<in> K \<Longrightarrow> norm z \<le> R"
    using Kb unfolding bounded_iff by blast
  define D where "D = R + norm yh"
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define N where "N = onorm ((*v) M)"
  have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
  have main: "p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2
      \<le> norm p * D + D * (N * D) / 2" if zK: "z \<in> K" for z
  proof -
    have nz: "norm z \<le> R" by (rule R[OF zK])
    have nzy: "norm (z - yh) \<le> D"
    proof -
      have "norm (z - yh) \<le> norm z + norm yh" by (rule norm_triangle_ineq4)
      then show ?thesis unfolding D_def using nz by linarith
    qed
    have D0: "0 \<le> D" using nzy by (meson norm_ge_zero order_trans)
    have t1: "p \<bullet> (z - yh) \<le> norm p * D"
    proof -
      have "p \<bullet> (z - yh) \<le> norm p * norm (z - yh)"
        by (rule norm_cauchy_schwarz)
      moreover have "norm p * norm (z - yh) \<le> norm p * D"
        by (rule mult_left_mono[OF nzy norm_ge_zero])
      ultimately show ?thesis by linarith
    qed
    have t2: "(z - yh) \<bullet> (M *v (z - yh)) \<le> D * (N * D)"
    proof -
      have a: "(z - yh) \<bullet> (M *v (z - yh))
          \<le> norm (z - yh) * norm (M *v (z - yh))"
        by (rule norm_cauchy_schwarz)
      have b: "norm (M *v (z - yh)) \<le> N * norm (z - yh)"
        unfolding N_def by (rule onorm[OF bl])
      have c: "N * norm (z - yh) \<le> N * D"
        by (rule mult_left_mono[OF nzy N0])
      have d: "norm (z - yh) * norm (M *v (z - yh))
          \<le> norm (z - yh) * (N * D)"
      proof (rule mult_left_mono)
        show "norm (M *v (z - yh)) \<le> N * D" using b c by linarith
        show "0 \<le> norm (z - yh)" by simp
      qed
      have e: "norm (z - yh) * (N * D) \<le> D * (N * D)"
        by (rule mult_right_mono[OF nzy]) (use N0 D0 in simp)
      show ?thesis using a d e by linarith
    qed
    show ?thesis using t1 t2 by linarith
  qed
  show ?thesis by (rule that) (use main in blast)
qed

text \<open>The affine gradient field of a quadratic has the same derivative at every
  point, not just at the base point, which is what a Hessian \<^emph>\<open>field\<close> needs.\<close>

lemma quadratic_grad_derivative_at:
  fixes H :: "real^'n::finite^'n" and p x y :: "real^'n"
  shows "((\<lambda>z. p + H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
proof -
  have blH: "bounded_linear ((*v) H)" by (rule matrix_vector_mul_bounded_linear)
  have shift: "((\<lambda>z::real^'n. z - x) has_derivative (\<lambda>h. h)) (at y)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>z. H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
    using bounded_linear.has_derivative[OF blH shift] by simp
  then show ?thesis by (auto intro!: derivative_eq_intros)
qed

lemma quad_bdd_below_on_bounded:
  fixes p yh :: "real^'n::finite" and M :: "real^'n^'n"
    and K :: "(real^'n) set"
  assumes Kb: "bounded K"
  obtains B where "\<And>z. z \<in> K \<Longrightarrow>
    B \<le> p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2"
proof -
  obtain B0 where B0: "\<And>z. z \<in> K \<Longrightarrow>
    (- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2 \<le> B0"
  proof (rule quad_bdd_above_on_bounded[OF Kb,
          where p = "- p" and yh = yh and M = "- M"])
    fix BB :: real
    assume "\<And>z. z \<in> K \<Longrightarrow>
      (- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2 \<le> BB"
    then show thesis by (rule that)
  qed
  have main: "- B0 \<le> p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2"
    if zK: "z \<in> K" for z
  proof -
    have mv: "(- M) *v (z - yh) = - (M *v (z - yh))"
    proof -
      have "(- M :: real^'n^'n) *v (z - yh) = (0 - M) *v (z - yh)" by simp
      also have "\<dots> = 0 *v (z - yh) - M *v (z - yh)"
        by (rule matrix_vector_mult_diff_rdistrib)
      also have "\<dots> = - (M *v (z - yh))" by simp
      finally show ?thesis .
    qed
    have "(- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2
        = - (p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2)"
      unfolding mv by simp
    then show ?thesis using B0[OF zK] by linarith
  qed
  show ?thesis by (rule that) (use main in blast)
qed

text \<open>Freezing one variable at the joint maximiser gives the two conditions
  the doubling argument needs: freezing \<open>y = yh\<close> makes \<open>xh\<close> a maximiser of
  \<open>u\<close> against \<open>x \<mapsto> (\<alpha>/2) \<parallel>x - yh\<parallel>\<^sup>2\<close>, and freezing \<open>x = xh\<close> makes \<open>yh\<close> a
  minimiser of \<open>w\<close> against \<open>y \<mapsto> - (\<alpha>/2) \<parallel>xh - y\<parallel>\<^sup>2\<close>. This converts the
  two-variable maximum into the one-variable touching conditions that the
  sub- and supersolution definitions consume.\<close>

lemma doubling_partial_max_fst:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes jmax: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and yh: "yh \<in> S" and x: "x \<in> S"
  shows "u x - (\<alpha>/2) * (norm (x - yh))\<^sup>2
      \<le> u xh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
  using jmax[OF x yh] by simp

lemma doubling_partial_min_snd:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes jmax: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> S" and y: "y \<in> S"
  shows "w yh - (- ((\<alpha>/2) * (norm (xh - yh))\<^sup>2))
      \<le> w y - (- ((\<alpha>/2) * (norm (xh - y))\<^sup>2))"
  using jmax[OF xh y] by simp

text \<open>If the maximising pair is on the diagonal, the doubling degenerates:
  its common point maximises \<open>u - w\<close> over \<open>K\<close> itself, by comparing \<open>\<Phi>\<close>
  against the diagonal, where the penalty vanishes on both sides. This is where a
  comparison argument splits: either the maximising pair is off the diagonal,
  where a strict operator inequality applies, or \<open>u - w\<close> attains its maximum
  over \<open>K\<close> at the common point.\<close>

lemma doubling_diagonal_max:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and diag: "xh = yh" and xh: "xh \<in> K"
    and x: "x \<in> K"
  shows "u x - w x \<le> u xh - w xh"
proof -
  have "u x - w x - (\<alpha>/2) * (norm (x - x))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule mx[OF x x])
  then show ?thesis
    using diag by simp
qed

text \<open>Conversely, if \<open>u - w\<close> does not attain its maximum over \<open>K\<close> at the
  common point, the maximising pair cannot be on the diagonal, so the
  gradient is nonzero and the envelope contradiction applies.\<close>

lemma doubling_off_diagonal:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
  shows "xh \<noteq> yh"
proof
  assume "xh = yh"
  from doubling_diagonal_max[OF mx this xh x] have "u x - w x \<le> u xh - w xh" .
  with gt show False by linarith
qed

corollary doubling_grad_nonzero:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
    and a: "\<alpha> \<noteq> 0"
  shows "\<alpha> *\<^sub>R (xh - yh) \<noteq> 0"
  using doubling_off_diagonal[OF mx xh x gt] a by simp

text \<open>Every Crandall-Ishii comparison argument needs the penalty term at the
  maximising pair to be bounded, hence to vanish as \<open>\<alpha> \<rightarrow> \<infinity>\<close>, forcing
  \<open>x'\<close> and \<open>y'\<close> together and driving the doubled maximum to the maximum of
  \<open>u - w\<close>. The proof compares \<open>\<Phi>\<close> at the maximiser against \<open>\<Phi>\<close> at a
  diagonal point \<open>(z,z)\<close>, where the penalty vanishes, bounding the penalty
  at the maximiser by the gap between \<open>u(z) - w(z)\<close> and an upper bound for
  \<open>u x - w y\<close> on \<open>K \<times> K\<close>.\<close>

lemma doubling_penalty_bound:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
  shows "(\<alpha>/2) * (norm (xh - yh))\<^sup>2 \<le> C - (u z - w z)"
proof -
  have "u z - w z - (\<alpha>/2) * (norm (z - z))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule mx[OF z z])
  then have "u z - w z \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by simp
  with bnd show ?thesis by linarith
qed

text \<open>In the form actually used: for \<open>\<alpha> > 0\<close> the squared distance between
  the two components of the maximiser is \<open>O(1/\<alpha>)\<close>, with an explicit
  constant, driving \<open>x' - y' \<rightarrow> 0\<close>.\<close>

corollary doubling_dist_bound:
  fixes u w :: "'b::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C" and a: "0 < \<alpha>"
  shows "(norm (xh - yh))\<^sup>2 \<le> 2 * (C - (u z - w z)) / \<alpha>"
proof -
  have "(\<alpha>/2) * (norm (xh - yh))\<^sup>2 \<le> C - (u z - w z)"
    by (rule doubling_penalty_bound[OF mx xh yh z bnd])
  then have "\<alpha> * (norm (xh - yh))\<^sup>2 \<le> 2 * (C - (u z - w z))"
    by simp
  then show ?thesis
    using a by (simp add: field_simps)
qed

text \<open>Since the penalty is bounded, the doubled maximum is at least the
  maximum of \<open>u - w\<close> along the diagonal; with \<open>doubling_diagonal_max\<close> this
  says the doubling can only improve on the diagonal value.  That is
  \<open>doubling_ge_diagonal\<close> in @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums},
  already at \<open>'a::euclidean_space\<close>; this theory had its own copy specialised
  to \<open>'b\<close> and to the value at a maximising pair, which shadowed it.\<close>

text \<open>These four lemmas use the penalty only through \<open>Pn 0 = 0\<close>: each proof
  instantiates the maximiser inequality at a diagonal point, where the
  penalty is \<open>Pn (z - z) = Pn 0\<close> (the concrete penalty vanishing at the origin for \<open>soft_pen\<close>).
  \<open>doubling_off_diagonal_gen\<close> puts the maximising pair off the diagonal
  whenever \<open>u - w\<close> beats its value at the common point, making
  \<open>soft_grad_nonzero\<close> applicable and supplying the positive lower bound
  \<open>c\<close>.\<close>

lemma doubling_diagonal_max_gen:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and diag: "xh = yh" and xh: "xh \<in> K"
    and x: "x \<in> K"
  shows "u x - w x \<le> u xh - w xh"
proof -
  have base: "u x - w x - Pn (x - x) \<le> u xh - w yh - Pn (xh - yh)"
    by (rule mx[OF x x])
  have e1: "x - x = (0 :: 'a)" by simp
  have e2: "xh - yh = (0 :: 'a)" using diag by simp
  from base have "u x - w x - Pn 0 \<le> u xh - w yh - Pn 0"
    unfolding e1 e2 .
  then have "u x - w x \<le> u xh - w yh" unfolding P0 by simp
  then show ?thesis using diag by simp
qed

lemma doubling_off_diagonal_gen:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
  shows "xh \<noteq> yh"
proof
  assume e: "xh = yh"
  from doubling_diagonal_max_gen[OF mx P0 e xh x]
  have "u x - w x \<le> u xh - w xh" .
  with gt show False by linarith
qed

lemma doubling_penalty_bound_gen:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
  shows "Pn (xh - yh) \<le> C - (u z - w z)"
proof -
  have base: "u z - w z - Pn (z - z) \<le> u xh - w yh - Pn (xh - yh)"
    by (rule mx[OF z z])
  have e: "z - z = (0 :: 'a)" by simp
  from base have "u z - w z - Pn 0 \<le> u xh - w yh - Pn (xh - yh)"
    unfolding e .
  then have "u z - w z \<le> u xh - w yh - Pn (xh - yh)" unfolding P0 by simp
  with bnd show ?thesis by linarith
qed

text \<open>Every doubling lemma above takes the maximising property of
  \<open>(x', y')\<close> as a hypothesis; on a compact \<open>K\<close> with continuous \<open>u\<close> and
  \<open>w\<close> it follows from attainment of a supremum by a continuous function on
  the compact product \<open>K \<times> K\<close>.\<close>

theorem doubling_maximiser_exists:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cpen: "continuous_on (K \<times> K)
      (\<lambda>z. (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
    by (intro continuous_intros)
  have cont: "continuous_on (K \<times> K)
      (\<lambda>z. u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
    using cfst csnd cpen by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K.
        u (fst v) - w (snd v) - (\<alpha>/2) * (norm (fst v - snd v))\<^sup>2
          \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
    using continuous_attains_sup[OF cp nep cont] by blast
  have zf: "fst z \<in> K" and zs: "snd z \<in> K"
    using z by auto
  have "\<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this] show
      "u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
      by simp
  qed
  with zf zs show ?thesis by blast
qed

text \<open>The same for a general penalty: the penalty enters the existence proof
  only through the continuity of \<open>cpen\<close>, so the general version takes that
  as a hypothesis; the rest is \<open>compact_Times\<close> plus
  \<open>continuous_attains_sup\<close>.\<close>

theorem doubling_maximiser_exists_gen:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and cPn: "continuous_on UNIV Pn"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cdiff: "continuous_on (K \<times> K) (\<lambda>z. fst z - snd z)"
    by (intro continuous_intros)
  have cpen: "continuous_on (K \<times> K) (\<lambda>z. Pn (fst z - snd z))"
    by (rule continuous_on_compose2[OF cPn cdiff subset_UNIV])
  have cont: "continuous_on (K \<times> K)
      (\<lambda>z. u (fst z) - w (snd z) - Pn (fst z - snd z))"
    using cfst csnd cpen by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K.
        u (fst v) - w (snd v) - Pn (fst v - snd v)
          \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
    using continuous_attains_sup[OF cp nep cont] by blast
  have zf: "fst z \<in> K" and zs: "snd z \<in> K"
    using z by auto
  have "\<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - Pn (x - y)
        \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this] show
      "u x - w y - Pn (x - y)
        \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
      by simp
  qed
  with zf zs show ?thesis by blast
qed

text \<open>\<open>doubling_penalty_bound\<close> and \<open>doubling_dist_bound\<close> carry a bare
  hypothesis \<open>u x' - w y' \<le> C\<close>; on a compact \<open>K\<close> with continuous data it
  comes from the same attainment argument as the maximiser itself.\<close>

lemma doubling_upper_bound_exists:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>C. \<forall>x\<in>K. \<forall>y\<in>K. u x - w y \<le> C"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cont: "continuous_on (K \<times> K) (\<lambda>z. u (fst z) - w (snd z))"
    using cfst csnd by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K. u (fst v) - w (snd v) \<le> u (fst z) - w (snd z)"
    using continuous_attains_sup[OF cp nep cont] by blast
  have "\<forall>x\<in>K. \<forall>y\<in>K. u x - w y \<le> u (fst z) - w (snd z)"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this]
    show "u x - w y \<le> u (fst z) - w (snd z)" by simp
  qed
  then show ?thesis by blast
qed

text \<open>The bridge itself: an Alexandrov jet of \<open>v\<close> at \<open>xh\<close> with data
  \<open>(p, A)\<close> gives, for every \<open>\<delta> > 0\<close>, the local-max statement for the jet
  test function built from \<open>(p, A + \<delta> I)\<close>, the \<open>subtest\<close> hypothesis
  the comparison argument downstream requires.\<close>

theorem jet_imp_local_max_test:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes lim: "((\<lambda>k. (v (xh + k) - v xh - p \<bullet> k - (k \<bullet> (A *v k))/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball xh e.
      v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>k. norm k < e \<Longrightarrow>
        v (xh + k) - (p \<bullet> k + (k \<bullet> (A *v k))/2 + (\<delta>/2) * (norm k)\<^sup>2) \<le> v xh"
    using superjet_local_max[OF lim d] by blast
  have "\<forall>z \<in> ball xh e.
      v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
  proof
    fix z assume z: "z \<in> ball xh e"
    have nk: "norm (z - xh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have xz: "xh + (z - xh) = z" by simp
    from b[OF nk] have
      "v z - (p \<bullet> (z - xh) + ((z - xh) \<bullet> (A *v (z - xh)))/2
          + (\<delta>/2) * (norm (z - xh))\<^sup>2) \<le> v xh"
      unfolding xz .
    moreover have
      "(z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh))
        = (z - xh) \<bullet> (A *v (z - xh)) + \<delta> * (norm (z - xh))\<^sup>2"
      by (rule quad_form_shift_identity)
    ultimately show
      "v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
      by (simp add: add_divide_distrib)
  qed
  with e show ?thesis by blast
qed

text \<open>\<open>superjet_local_max\<close>
  (@{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}) uses only one
  side of its \<open>tendsto\<close> hypothesis, and a doubling argument that reaches the
  diagonal typically supplies only an upper bound on the increment of
  \<open>B = supconv (-w) \<epsilon>\<close>.  This subsection restates the chain with a
  one-sided hypothesis; \<open>onesided_of_tendsto\<close> shows it is a genuine
  weakening.  The quantifier over the threshold \<open>c\<close> is necessary, because a
  caller produces that bound inside its own proof, after the hypothesis is
  fixed.\<close>

lemma superjet_local_max_onesided:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F kk in at 0.
      (u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>kk. norm kk < e \<longrightarrow>
      u (xh + kk) - (p \<bullet> kk + (kk \<bullet> X kk)/2 + (\<delta>/2) * (norm kk)\<^sup>2) \<le> u xh"
proof -
  have d2: "0 < \<delta>/2" using d by simp
  from ub[OF d2] obtain e where e: "0 < e"
    and b: "\<And>kk. kk \<noteq> 0 \<Longrightarrow> dist kk 0 < e
      \<Longrightarrow> (u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < \<delta>/2"
    unfolding eventually_at by blast
  have main: "u (xh + kk) - (p \<bullet> kk + (kk \<bullet> X kk)/2 + (\<delta>/2) * (norm kk)\<^sup>2)
      \<le> u xh" if nk: "norm kk < e" for kk
  proof (cases "kk = 0")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have nn: "0 < (norm kk)\<^sup>2" using False by simp
    have dk: "dist kk 0 < e" using nk by (simp add: dist_norm)
    have "(u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < \<delta>/2"
      by (rule b[OF False dk])
    hence "u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2 < (\<delta>/2) * (norm kk)\<^sup>2"
      using nn by (simp add: field_simps)
    thus ?thesis by simp
  qed
  show ?thesis using e main by blast
qed

theorem jet_imp_local_min_test_onesided:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F kk in at 0.
      ((- v) (yh + kk) - (- v) yh - (- p) \<bullet> kk
        - (kk \<bullet> ((- A) *v kk))/2) / (norm kk)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>kk. norm kk < e \<Longrightarrow>
        (- v) (yh + kk) - ((- p) \<bullet> kk + (kk \<bullet> ((- A) *v kk))/2
          + (\<delta>/2) * (norm kk)\<^sup>2) \<le> (- v) yh"
    using superjet_local_max_onesided[OF ub d] by blast
  have "\<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
  proof
    fix z assume z: "z \<in> ball yh e"
    have nk: "norm (z - yh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have yz: "yh + (z - yh) = z" by simp
    have negq: "(z - yh) \<bullet> ((- A) *v (z - yh))
        = - ((z - yh) \<bullet> (A *v (z - yh)))"
      by (simp add: matrix_vector_neg_left)
    from b[OF nk] have h:
      "- v z - (- (p \<bullet> (z - yh))
          + ((z - yh) \<bullet> ((- A) *v (z - yh)))/2
          + (\<delta>/2) * (norm (z - yh))\<^sup>2) \<le> - v yh"
      unfolding yz by simp
    have q: "(z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh))
        = (z - yh) \<bullet> (A *v (z - yh)) - \<delta> * (norm (z - yh))\<^sup>2"
      by (rule quad_form_shift_identity_neg)
    from h show
      "v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
      unfolding q negq by (simp add: field_simps)
  qed
  with e show ?thesis by blast
qed

theorem jet_imp_local_min_test:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes lim: "((\<lambda>k. ((- v) (yh + k) - (- v) yh - (- p) \<bullet> k
      - (k \<bullet> ((- A) *v k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>k. norm k < e \<Longrightarrow>
        (- v) (yh + k) - ((- p) \<bullet> k + (k \<bullet> ((- A) *v k))/2
          + (\<delta>/2) * (norm k)\<^sup>2) \<le> (- v) yh"
    using superjet_local_max[OF lim d] by blast
  have "\<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
  proof
    fix z assume z: "z \<in> ball yh e"
    have nk: "norm (z - yh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have yz: "yh + (z - yh) = z" by simp
    have negq: "(z - yh) \<bullet> ((- A) *v (z - yh))
        = - ((z - yh) \<bullet> (A *v (z - yh)))"
      by (simp add: matrix_vector_neg_left)
    from b[OF nk] have h:
      "- v z - (- (p \<bullet> (z - yh))
          + ((z - yh) \<bullet> ((- A) *v (z - yh)))/2
          + (\<delta>/2) * (norm (z - yh))\<^sup>2) \<le> - v yh"
      unfolding yz by simp
    have q: "(z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh))
        = (z - yh) \<bullet> (A *v (z - yh)) - \<delta> * (norm (z - yh))\<^sup>2"
      by (rule quad_form_shift_identity_neg)
    from h show
      "v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
      unfolding q negq by (simp add: field_simps)
  qed
  with e show ?thesis by blast
qed

lemma doubled_penalty_jet:
  fixes P :: "real^'n::finite \<Rightarrow> real" and Z :: "real^'n^'n" and G :: "real^'n"
    and zh :: "(real^'n) \<times> (real^'n)"
  assumes Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
      - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>k. (P (fst (zh + k) - snd (zh + k)) - P (fst zh - snd zh)
      - ((G, - G) :: (real^'n) \<times> (real^'n)) \<bullet> k
      - (k \<bullet> ((Z *v (fst k - snd k), Z *v (snd k - fst k))
            :: (real^'n) \<times> (real^'n)))/2) / (norm k)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
proof -
  define R where "R = (\<lambda>h::real^'n. P ((fst zh - snd zh) + h)
      - P (fst zh - snd zh) - G \<bullet> h - (h \<bullet> (Z *v h))/2)"
  have Rlim: "((\<lambda>h. R h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding R_def by (rule Pjet)
  have R0: "R 0 = 0" unfolding R_def by simp
  have num: "P (fst (zh + k) - snd (zh + k)) - P (fst zh - snd zh)
      - ((G, - G) :: (real^'n) \<times> (real^'n)) \<bullet> k
      - (k \<bullet> ((Z *v (fst k - snd k), Z *v (snd k - fst k))
            :: (real^'n) \<times> (real^'n)))/2
    = R (fst k - snd k)" for k
  proof -
    have mvd: "Z *v (snd k - fst k) = - (Z *v (fst k - snd k))"
      by (simp add: matrix_vector_mult_diff_gen)
    have e: "fst (zh + k) - snd (zh + k)
        = (fst zh - snd zh) + (fst k - snd k)"
      by simp
    show ?thesis
      unfolding R_def e mvd
      by (simp add: inner_prod_def
          algebra_simps)
  qed
  have main: "((\<lambda>k::(real^'n)\<times>(real^'n). R (fst k - snd k) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  proof (rule tendstoI)
    fix e :: real assume e: "0 < e"
    then have e4: "0 < e/4" by simp
    have evR: "\<forall>\<^sub>F h in at (0::real^'n). dist (R h / (norm h)\<^sup>2) 0 < e/4"
      by (rule tendstoD[OF Rlim e4])
    obtain \<delta> where d0: "0 < \<delta>"
      and dd: "\<And>h::real^'n. h \<noteq> 0 \<Longrightarrow> dist h 0 < \<delta>
          \<Longrightarrow> dist (R h / (norm h)\<^sup>2) 0 < e/4"
      using evR unfolding eventually_at by blast
    show "\<forall>\<^sub>F k in at (0::(real^'n)\<times>(real^'n)).
        dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
      unfolding eventually_at
    proof (intro exI[of _ "\<delta>/2"] conjI)
      show "0 < \<delta>/2" using d0 by simp
      show "\<forall>k\<in>UNIV. k \<noteq> (0::(real^'n)\<times>(real^'n)) \<and> dist k 0 < \<delta>/2
          \<longrightarrow> dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
      proof (intro ballI impI)
        fix k :: "(real^'n)\<times>(real^'n)"
        assume k: "k \<noteq> 0 \<and> dist k 0 < \<delta>/2"
        have knz: "k \<noteq> 0" using k by simp
        have kd: "norm k < \<delta>/2" using k by (simp add: dist_norm)
        have kpos: "0 < norm k" using knz by simp
        have ksq: "0 < (norm k)\<^sup>2" using kpos by simp
        show "dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
        proof (cases "fst k - snd k = 0")
          case True
          then show ?thesis using R0 e by simp
        next
          case False
          have nf: "norm (fst k) \<le> norm k"
            using norm_fst_le[of "fst k" "snd k"] by simp
          have ns: "norm (snd k) \<le> norm k"
            using norm_snd_le[where x = "fst k" and y = "snd k"] by simp
          have nh: "norm (fst k - snd k) \<le> 2 * norm k"
          proof -
            have "norm (fst k - snd k) \<le> norm (fst k) + norm (snd k)"
              by (rule norm_triangle_ineq4)
            then show ?thesis using nf ns by linarith
          qed
          have hd: "dist (fst k - snd k) 0 < \<delta>"
            using nh kd by (simp add: dist_norm)
          have step: "dist (R (fst k - snd k) / (norm (fst k - snd k))\<^sup>2) 0
              < e/4"
            by (rule dd[OF False hd])
          have hpos: "0 < (norm (fst k - snd k))\<^sup>2" using False by simp
          have absR: "\<bar>R (fst k - snd k)\<bar>
              < (e/4) * (norm (fst k - snd k))\<^sup>2"
          proof -
            have "\<bar>R (fst k - snd k)\<bar> / (norm (fst k - snd k))\<^sup>2 < e/4"
              using step by (simp add: dist_real_def)
            then show ?thesis using hpos by (simp add: pos_divide_less_eq)
          qed
          have sq4: "(norm (fst k - snd k))\<^sup>2 \<le> 4 * (norm k)\<^sup>2"
          proof -
            have "(norm (fst k - snd k))\<^sup>2 \<le> (2 * norm k)\<^sup>2"
              by (rule power_mono[OF nh]) simp
            then show ?thesis by (simp add: power2_eq_square)
          qed
          have lt: "\<bar>R (fst k - snd k)\<bar> < e * (norm k)\<^sup>2"
          proof -
            have "(e/4) * (norm (fst k - snd k))\<^sup>2
                \<le> (e/4) * (4 * (norm k)\<^sup>2)"
              by (rule mult_left_mono[OF sq4]) (use e in linarith)
            then show ?thesis using absR by simp
          qed
          show ?thesis
            using lt ksq by (simp add: dist_real_def pos_divide_less_eq)
        qed
      qed
    qed
  qed
  show ?thesis unfolding num by (rule main)
qed

text \<open>The Jensen/Alexandrov layer needs global semiconvexity of
  \<open>a(x) + b(y) - P(x - y)\<close>, i.e. \<open>P\<close> semiconcave (Hessian bounded above); a
  quadratic gets this for free, a globally quartic penalty does not, since
  its Hessian grows like \<open>\<beta>\<parallel>d\<parallel>\<^sup>2\<close>. For \<open>P\<close> semiconcave with constant
  \<open>\<kappa>\<close>, the identity
  \<open>-P(x-y) + \<kappa>\<parallel>z\<parallel>\<^sup>2 = [(\<kappa>/2)\<parallel>x-y\<parallel>\<^sup>2 - P(x-y)] + (\<kappa>/2)\<parallel>x+y\<parallel>\<^sup>2\<close> writes the
  functional as a sum of two convex pieces, composed with
  \<open>z \<mapsto> fst z - snd z\<close> and \<open>z \<mapsto> fst z + snd z\<close> respectively. For quadratic
  \<open>P\<close> the first bracket vanishes identically, collapsing to
  \<open>semiconvex_penalty\<close>.\<close>

lemma convex_on_prod_diff:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes g: "convex_on UNIV g"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a. g (fst z - snd z))"
proof (rule convex_onI)
  fix t :: real and x y :: "'a \<times> 'a"
  assume t: "0 < t" "t < 1"
  have L: "fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) - snd ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      = (1 - t) *\<^sub>R (fst x - snd x) + t *\<^sub>R (fst y - snd y)"
    by (simp add: algebra_simps)
  show "g (fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) - snd ((1 - t) *\<^sub>R x + t *\<^sub>R y))
      \<le> (1 - t) * g (fst x - snd x) + t * g (fst y - snd y)"
    unfolding L
    by (rule convex_onD[OF g]) (use t in auto)
qed simp

lemma convex_on_prod_add:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes g: "convex_on UNIV g"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a. g (fst z + snd z))"
proof (rule convex_onI)
  fix t :: real and x y :: "'a \<times> 'a"
  assume t: "0 < t" "t < 1"
  have L: "fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) + snd ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      = (1 - t) *\<^sub>R (fst x + snd x) + t *\<^sub>R (fst y + snd y)"
    by (simp add: algebra_simps)
  show "g (fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) + snd ((1 - t) *\<^sub>R x + t *\<^sub>R y))
      \<le> (1 - t) * g (fst x + snd x) + t * g (fst y + snd y)"
    unfolding L
    by (rule convex_onD[OF g]) (use t in auto)
qed simp

theorem semiconvex_penalty_gen:
  fixes P :: "'a::euclidean_space \<Rightarrow> real"
  assumes k: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - P d)"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      - P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2)"
proof -
  have eq: "(\<lambda>z::'a \<times> 'a. - P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a \<times> 'a.
          ((\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))
          + (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2)"
  proof (rule ext)
    fix z :: "'a \<times> 'a"
    have d: "(norm (fst z - snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 - 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
          inner_commute)
    have s: "(norm (fst z + snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 + 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
          inner_commute)
    show "- P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2
        = ((\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))
          + (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2"
      unfolding norm_prod_sq d s by (simp add: algebra_simps)
  qed
  have c1: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      (\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))"
    by (rule convex_on_prod_diff[OF sc])
  have cn: "convex_on UNIV (\<lambda>x::'a. (\<kappa>/2) * (norm x)\<^sup>2)"
  proof -
    have k2: "0 \<le> \<kappa>/2" using k by simp
    have "convex_on UNIV (\<lambda>x::'a. (norm x)\<^sup>2)"
      by (rule convex_on_norm_sq[OF convex_UNIV])
    then show ?thesis by (rule convex_on_cmul[OF k2])
  qed
  have c2: "convex_on UNIV (\<lambda>z::'a \<times> 'a. (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2)"
    by (rule convex_on_prod_add[OF cn])
  show ?thesis unfolding eq by (rule convex_on_add[OF c1 c2])
qed

lemma convex_on_norm_lift:
  fixes dummy :: "'a::real_normed_vector"
  shows "convex_on UNIV (\<lambda>d::'a. norm ((d, 1) :: 'a \<times> real))"
proof (rule convex_onI)
  fix t :: real and x y :: 'a
  assume t: "0 < t" "t < 1"
  have L: "(((1 - t) *\<^sub>R x + t *\<^sub>R y, 1) :: 'a \<times> real)
      = (1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real) + t *\<^sub>R ((y, 1) :: 'a \<times> real)"
    by simp
  have n1: "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
      = (1 - t) * norm ((x, 1) :: 'a \<times> real)"
  proof -
    have "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
        = \<bar>1 - t\<bar> * norm ((x, 1) :: 'a \<times> real)"
      by (rule norm_scaleR)
    moreover have "\<bar>1 - t\<bar> = 1 - t" using t by simp
    ultimately show ?thesis by simp
  qed
  have n2: "norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))
      = t * norm ((y, 1) :: 'a \<times> real)"
  proof -
    have "norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))
        = \<bar>t\<bar> * norm ((y, 1) :: 'a \<times> real)"
      by (rule norm_scaleR)
    moreover have "\<bar>t\<bar> = t" using t by simp
    ultimately show ?thesis by simp
  qed
  have "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real) + t *\<^sub>R ((y, 1) :: 'a \<times> real))
      \<le> norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
        + norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))"
    by (rule norm_triangle_ineq)
  also have "\<dots> = (1 - t) * norm ((x, 1) :: 'a \<times> real)
        + t * norm ((y, 1) :: 'a \<times> real)"
    unfolding n1 n2 ..
  finally show "norm (((1 - t) *\<^sub>R x + t *\<^sub>R y, 1) :: 'a \<times> real)
      \<le> (1 - t) * norm ((x, 1) :: 'a \<times> real)
        + t * norm ((y, 1) :: 'a \<times> real)"
    unfolding L .
qed simp

text \<open>Subtracting \<open>\<delta>\<parallel>z - \<xi>\<parallel>\<^sup>2\<close> and adding back \<open>\<delta>\<parallel>z\<parallel>\<^sup>2\<close> leaves an affine
  term \<open>\<delta>(2 z \<bullet> \<xi> - \<parallel>\<xi>\<parallel>\<^sup>2)\<close>, so a semiconvex \<open>\<Psi>\<close> stays semiconvex after
  this shift, with its constant raised by \<open>2\<delta>\<close>; the argument is
  independent of the penalty.\<close>

lemma semiconvex_shift_perturb:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<Psi> z + (C/2) * (norm z)\<^sup>2)"
    and dnn: "0 \<le> \<delta>"
  shows "convex_on UNIV (\<lambda>z. (\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2)
      + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2)"
proof -
  have sq: "(norm (z - \<xi>))\<^sup>2 = (norm z)\<^sup>2 - 2 * (z \<bullet> \<xi>) + (norm \<xi>)\<^sup>2"
    for z :: 'a
    by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
        inner_commute)
  have e: "(\<lambda>z::'a. (\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2)
        + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a. (\<Psi> z + (C/2) * (norm z)\<^sup>2)
        + \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
  proof (rule ext)
    fix z :: 'a
    show "(\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2) + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2
        = (\<Psi> z + (C/2) * (norm z)\<^sup>2) + \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2)"
      unfolding sq by (simp add: algebra_simps)
  qed
  have aff: "convex_on UNIV (\<lambda>z::'a. \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
  proof (rule convex_onI)
    fix t :: real and x y :: 'a
    assume "0 < t" "t < 1"
    show "\<delta> * (2 * (((1 - t) *\<^sub>R x + t *\<^sub>R y) \<bullet> \<xi>) - (norm \<xi>)\<^sup>2)
        \<le> (1 - t) * (\<delta> * (2 * (x \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))
          + t * (\<delta> * (2 * (y \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
      by (simp add: algebra_simps)
  qed simp
  show ?thesis unfolding e by (rule convex_on_add[OF cvx aff])
qed

text \<open>The annulus bound Jensen's strict-gap version needs: a plain
  maximiser of \<open>\<Phi>\<close> over \<open>cball \<xi>\<^sub>0 r\<close> gives no strict gap, but
  subtracting \<open>\<delta>\<parallel>z - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> costs at least \<open>\<delta>\<rho>\<^sup>2\<close> on the annulus
  \<open>\<rho> \<le> \<parallel>y - \<xi>\<^sub>0\<parallel>\<close>, while the centre value \<open>\<Phi>(\<xi>\<^sub>0)\<close> is exact.\<close>

lemma shifted_annulus_bound_split_gen:
  fixes A B :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        A (fst y) + B (snd y) - Pn (fst y - snd y)
        \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and dnn: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)
      \<le> (A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) - \<delta> * \<rho>\<^sup>2"
proof -
  have nsplit: "(norm (y - \<xi>\<^sub>0))\<^sup>2
      = (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2 + (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2"
  proof -
    have "(norm (y - \<xi>\<^sub>0))\<^sup>2
        = (norm (fst (y - \<xi>\<^sub>0)))\<^sup>2 + (norm (snd (y - \<xi>\<^sub>0)))\<^sup>2"
      by (rule norm_prod_sq)
    then show ?thesis by simp
  qed
  have dn: "norm (y - \<xi>\<^sub>0) = dist y \<xi>\<^sub>0" by (simp add: dist_norm)
  have sq: "\<rho>\<^sup>2 \<le> (norm (y - \<xi>\<^sub>0))\<^sup>2"
    unfolding dn by (rule power_mono[OF ann]) (use rho in linarith)
  have pen: "\<delta> * \<rho>\<^sup>2 \<le> \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (rule mult_left_mono[OF sq dnn])
  have mx: "A (fst y) + B (snd y) - Pn (fst y - snd y)
      \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    by (rule mxK[OF y])
  have e: "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)
      = (A (fst y) + B (snd y) - Pn (fst y - snd y))
        - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    unfolding nsplit by (simp add: algebra_simps)
  show ?thesis unfolding e using mx pen by linarith
qed

theorem sums_matrix_inequality_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
    and v: "v \<noteq> 0"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       + v \<bullet> (snd (W (0, v)) + Z *v v) \<le> 0"
proof -
  define Pop where "Pop = (\<lambda>k::(real^'n) \<times> (real^'n).
      ((Z *v (fst k - snd k), Z *v (snd k - fst k)) :: (real^'n) \<times> (real^'n)))"
  define WP where "WP = (\<lambda>k::(real^'n) \<times> (real^'n). W k + Pop k)"
  define g0 where "g0 = ((G, - G) :: (real^'n) \<times> (real^'n))"
  have scPop: "Pop (s *\<^sub>R u) = s *\<^sub>R Pop u" for s :: real and u
    unfolding Pop_def
    by (simp add: scaleR_diff_right[symmetric] matrix_vector_mult_scaleR_gen)
  have scWP: "WP (s *\<^sub>R u) = s *\<^sub>R WP u" for s :: real and u
    unfolding WP_def scW scPop by (simp add: scaleR_add_right)
  have penlim: "((\<lambda>k. (Pn (fst (zh + k) - snd (zh + k))
        - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    unfolding g0_def Pop_def by (rule doubled_penalty_jet[OF Pjet])
  have rem: "((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2)
      + (Pn (fst (zh + k) - snd (zh + k))
        - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2)
      = (a (fst (zh + k)) + b (snd (zh + k)))
        - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2" for k
  proof -
    have iWP: "k \<bullet> WP k = k \<bullet> W k + k \<bullet> Pop k"
      unfolding WP_def by (simp add: inner_add_right)
    have iq: "(q + g0) \<bullet> k = q \<bullet> k + g0 \<bullet> k"
      by (simp add: inner_add_left)
    show ?thesis unfolding iWP iq by simp argo
  qed
  have expTheta: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k)))
      - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have s: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
            - Pn (fst (zh + k) - snd (zh + k)))
          - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
          - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
        + ((Pn (fst (zh + k) - snd (zh + k))
          - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2))
        \<longlongrightarrow> 0) (at 0)"
      using tendsto_add[OF expPsi penlim] by simp
    have e: "(((a (fst (zh + k)) + b (snd (zh + k))
            - Pn (fst (zh + k) - snd (zh + k)))
          - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
          - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
        + ((Pn (fst (zh + k) - snd (zh + k))
          - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2)
      = ((a (fst (zh + k)) + b (snd (zh + k)))
        - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2)
        / (norm k)\<^sup>2" for k
      using rem[of k] by (simp add: add_divide_distrib[symmetric])
    show ?thesis using s unfolding e .
  qed
  have blk: "(v, v) \<bullet> WP (v, v)
      = v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v))"
    by (rule product_form_block_diagonal[OF expTheta scWP v v])
  have pdiag: "(v, v) \<bullet> Pop (v, v) = 0"
    unfolding Pop_def by (simp add: inner_prod_def)
  have "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v) + (v, v) \<bullet> Pop (v, v)"
    unfolding WP_def by (simp add: inner_add_right)
  hence "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v)"
    unfolding pdiag by simp
  moreover have "(v, v) \<bullet> W (v, v) \<le> 0" by (rule neg)
  ultimately have "v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v)) \<le> 0"
    unfolding blk[symmetric] by simp
  thus ?thesis unfolding WP_def Pop_def by simp
qed

text \<open>The ordering in \<open>\<le>\<close> form, then with the negativity hypothesis
  discharged at the interior maximum, both with \<open>\<alpha> *\<^sub>R v\<close> replaced by
  \<open>Z *v v\<close> and the penalty's jet \<open>Pjet\<close> threaded through.\<close>

theorem sums_gives_ordering_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       \<le> v \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof (cases "v = 0")
  case True
  then show ?thesis by simp
next
  case False
  have h: "v \<bullet> (fst (W (v, 0)) + Z *v v)
      + v \<bullet> (snd (W (0, v)) + Z *v v) \<le> 0"
    by (rule sums_matrix_inequality_gen[OF expPsi Pjet scW neg False])
  have neg_eq: "v \<bullet> (- (snd (W (0, v)) + Z *v v))
      = - (v \<bullet> (snd (W (0, v)) + Z *v v))"
    by (rule inner_minus_right)
  show ?thesis
    unfolding neg_eq using h by linarith
qed

theorem sums_ordering_at_interior_max_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k))
        \<le> a (fst zh) + b (snd zh) - Pn (fst zh - snd zh)"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       \<le> v \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::(real^'n) \<times> (real^'n).
      a (fst z) + b (snd z) - Pn (fst z - snd z))"
  have mxP: "\<Psi> (zh + k) \<le> \<Psi> zh" if "norm k < d" for k
    unfolding \<Psi>_def by (rule mx[OF that])
  have expP: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding \<Psi>_def by (rule expPsi)
  have neg: "k \<bullet> W k \<le> 0" for k
    using second_order_interior_max[OF blW dpos mxP expP] by blast
  have scW: "W (s *\<^sub>R u) = s *\<^sub>R W u" for s :: real and u
    using blW by (simp add: linear_simps)
  show ?thesis
    by (rule sums_gives_ordering_gen[OF expPsi Pjet scW neg])
qed

lemma linear_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. fst (W (v, 0)) + Z *v v)"
proof -
  have lW: "linear W"
    using blW by (simp add: linear_conv_bounded_linear)
  have l1: "linear (\<lambda>v::real^'n. fst (W (v, 0)))"
  proof (rule linearI)
    fix x y :: "real^'n"
    have "W (x + y, 0) = W (((x, 0) :: (real^'n) \<times> (real^'n)) + (y, 0))"
      by simp
    also have "\<dots> = W (x, 0) + W (y, 0)" by (rule linear_add[OF lW])
    finally show "fst (W (x + y, 0)) = fst (W (x, 0)) + fst (W (y, 0))"
      by simp
  next
    fix c :: real and x :: "real^'n"
    have "W (c *\<^sub>R x, 0) = W (c *\<^sub>R ((x, 0) :: (real^'n) \<times> (real^'n)))"
      by simp
    also have "\<dots> = c *\<^sub>R W (x, 0)" by (rule linear_cmul[OF lW])
    finally show "fst (W (c *\<^sub>R x, 0)) = c *\<^sub>R fst (W (x, 0))"
      by simp
  qed
  have l2: "linear (\<lambda>v::real^'n. Z *v v)"
    by (rule matrix_vector_mul_linear)
  show ?thesis by (rule linear_compose_add[OF l1 l2])
qed

lemma linear_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
proof -
  have lW: "linear W"
    using blW by (simp add: linear_conv_bounded_linear)
  have l1: "linear (\<lambda>v::real^'n. snd (W (0, v)))"
  proof (rule linearI)
    fix x y :: "real^'n"
    have "W (0, x + y) = W (((0, x) :: (real^'n) \<times> (real^'n)) + (0, y))"
      by simp
    also have "\<dots> = W (0, x) + W (0, y)" by (rule linear_add[OF lW])
    finally show "snd (W (0, x + y)) = snd (W (0, x)) + snd (W (0, y))"
      by simp
  next
    fix c :: real and x :: "real^'n"
    have "W (0, c *\<^sub>R x) = W (c *\<^sub>R ((0, x) :: (real^'n) \<times> (real^'n)))"
      by simp
    also have "\<dots> = c *\<^sub>R W (0, x)" by (rule linear_cmul[OF lW])
    finally show "snd (W (0, c *\<^sub>R x)) = c *\<^sub>R snd (W (0, x))"
      by simp
  qed
  have l2: "linear (\<lambda>v::real^'n. Z *v v)"
    by (rule matrix_vector_mul_linear)
  have l3: "linear (\<lambda>v::real^'n. snd (W (0, v)) + Z *v v)"
    by (rule linear_compose_add[OF l1 l2])
  show ?thesis by (rule linear_compose_neg[OF l3])
qed

lemma sym_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "v \<bullet> (fst (W (z, 0)) + Z *v z)
       = z \<bullet> (fst (W (v, 0)) + Z *v v)"
proof -
  have w1: "v \<bullet> fst (W (z, 0)) = ((v, 0) :: (real^'n) \<times> (real^'n)) \<bullet> W (z, 0)"
    by (simp add: inner_prod_def)
  have w2: "z \<bullet> fst (W (v, 0)) = ((z, 0) :: (real^'n) \<times> (real^'n)) \<bullet> W (v, 0)"
    by (simp add: inner_prod_def)
  have wsym: "v \<bullet> fst (W (z, 0)) = z \<bullet> fst (W (v, 0))"
    unfolding w1 w2 by (rule symW)
  have zsym: "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
    by (rule inner_matrix_sym[OF symZ])
  show ?thesis
    using wsym zsym by (simp add: inner_add_right)
qed

lemma sym_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "v \<bullet> (- (snd (W (0, z)) + Z *v z))
       = z \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof -
  have w1: "v \<bullet> snd (W (0, z)) = ((0, v) :: (real^'n) \<times> (real^'n)) \<bullet> W (0, z)"
    by (simp add: inner_prod_def)
  have w2: "z \<bullet> snd (W (0, v)) = ((0, z) :: (real^'n) \<times> (real^'n)) \<bullet> W (0, v)"
    by (simp add: inner_prod_def)
  have wsym: "v \<bullet> snd (W (0, z)) = z \<bullet> snd (W (0, v))"
    unfolding w1 w2 by (rule symW)
  have zsym: "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
    by (rule inner_matrix_sym[OF symZ])
  have l: "v \<bullet> (- (snd (W (0, z)) + Z *v z))
      = - (v \<bullet> snd (W (0, z))) - (v \<bullet> (Z *v z))"
    by (simp add: inner_add_right inner_diff_right)
  have r: "z \<bullet> (- (snd (W (0, v)) + Z *v v))
      = - (z \<bullet> snd (W (0, v))) - (z \<bullet> (Z *v v))"
    by (simp add: inner_add_right inner_diff_right)
  show ?thesis unfolding l r using wsym zsym by simp
qed

text \<open>A comparison argument consumes the Hessian ordering \<open>psd (Ym - Xm)\<close>.
  The theorem on sums (\<open>sums_matrix_inequality\<close>,
  @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}) delivers the
  ordering between the two diagonal blocks.  Writing
  \<open>X v = fst (W (v,0)) + \<alpha> v\<close> and
  \<open>Y v = - (snd (W (0,v)) + \<alpha> v)\<close> --- negated because the supersolution
  enters the doubled functional as \<open>-w\<close> --- this reads
  \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>; the \<open>+ \<alpha> v\<close> term in each block is the penalty's
  second derivative restricted to that block.\<close>

theorem sums_gives_ordering:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
  shows "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       \<le> v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof (cases "v = 0")
  case True
  then show ?thesis by simp
next
  case False
  have raw: "v \<bullet> fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
       + v \<bullet> snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)) \<le> 0"
    by (rule sums_matrix_inequality[OF expPsi scW neg False])
  have e1: "fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
      = fst (W (v, 0)) + \<alpha> *\<^sub>R v"
    by simp
  have e2: "snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0))
      = snd (W (0, v)) + \<alpha> *\<^sub>R v"
    by simp
  from raw have h: "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       + v \<bullet> (snd (W (0, v)) + \<alpha> *\<^sub>R v) \<le> 0"
    unfolding e1 e2 .
  have neg_eq: "v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))
      = - (v \<bullet> (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule inner_minus_right)
  show ?thesis
    unfolding neg_eq using h by linarith
qed

text \<open>The hypothesis \<open>k \<cdot> W k \<le> 0\<close> of \<open>sums_gives_ordering\<close> is what
  \<open>second_order_interior_max\<close> gives at an interior maximum, which the
  doubled functional has by construction; the ordering then depends only
  on the maximum property and the jet.\<close>

theorem sums_ordering_at_interior_max:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       \<le> v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::('a) \<times> ('a).
      a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
  have mxP: "\<Psi> (zh + k) \<le> \<Psi> zh" if "norm k < d" for k
    unfolding \<Psi>_def by (rule mx[OF that])
  have expP: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding \<Psi>_def by (rule expPsi)
  have neg: "k \<bullet> W k \<le> 0" for k
    using second_order_interior_max[OF blW dpos mxP expP] by blast
  have scW: "W (s *\<^sub>R u) = s *\<^sub>R W u" for s :: real and u
    using blW by (simp add: linear_simps)
  show ?thesis
    by (rule sums_gives_ordering[OF expPsi scW neg])
qed

text \<open>The doubled functional built from the sup-convolutions of \<open>u\<close> and
  \<open>w\<close> is semiconvex (\<open>doubled_functional_semiconvex\<close>) with constant
  \<open>1/\<epsilon> + 1/\<epsilon> + 2\<alpha>\<close>, one \<open>1/\<epsilon>\<close> from each sup-convolution and \<open>2\<alpha>\<close>
  from the penalty; positive as soon as \<open>\<epsilon> > 0\<close>, so Jensen's lemma
  applies and produces a point carrying a genuine Alexandrov jet.\<close>

lemma doubled_semiconvexity_constant_pos:
  fixes \<epsilon> \<alpha> :: real
  assumes e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
  shows "0 < 1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>"
proof -
  have inv: "0 < inverse \<epsilon>"
    by (rule positive_imp_inverse_positive[OF e])
  have "0 < 1/\<epsilon>"
    using inv by (simp add: inverse_eq_divide)
  then show ?thesis using a by linarith
qed

text \<open>The shifted version of Jensen's lemma for the doubled sup-convolution
  functional, giving the strict inequality Jensen needs: subtracting
  \<open>\<delta>\<parallel>z - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> turns a plain maximiser \<open>\<xi>\<^sub>0\<close> into a strict one, with
  gap \<open>\<delta>\<rho>\<^sup>2\<close> on the annulus. By \<open>norm_sq_prod_split\<close> the perturbation
  splits across the two blocks, so the perturbed functional keeps the
  doubled form \<open>a (fst z) + b (snd z) - penalty\<close>.\<close>

lemma norm_sq_prod_split:
  fixes z c :: "('a::euclidean_space) \<times> 'a"
  shows "(norm (z - c))\<^sup>2
       = (norm (fst z - fst c))\<^sup>2 + (norm (snd z - snd c))\<^sup>2"
  by (simp add: power2_norm_eq_inner inner_prod_def)

text \<open>Subtracting \<open>\<delta>\<parallel>y - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> costs at least \<open>\<delta>\<rho>\<^sup>2\<close> outside the
  \<open>\<rho>\<close>-ball and nothing at the centre, turning a plain maximiser of
  \<open>\<Phi>\<close> into a strict one; stated abstractly in \<open>\<Phi>\<close> since nothing about
  the doubling is used.\<close>

lemma shifted_annulus_bound:
  fixes \<Phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow> \<Phi> y \<le> \<Phi> \<xi>\<^sub>0"
    and dpos: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "\<Phi> y - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2 \<le> \<Phi> \<xi>\<^sub>0 - \<delta> * \<rho>\<^sup>2"
proof -
  have dn: "dist y \<xi>\<^sub>0 = norm (y - \<xi>\<^sub>0)"
    by (simp add: dist_norm)
  have "\<rho>\<^sup>2 \<le> (norm (y - \<xi>\<^sub>0))\<^sup>2"
    using ann rho unfolding dn by (simp add: power_mono)
  then have "\<delta> * \<rho>\<^sup>2 \<le> \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (rule mult_left_mono[OF _ dpos])
  moreover have "\<Phi> y \<le> \<Phi> \<xi>\<^sub>0" by (rule mx[OF y])
  ultimately show ?thesis by linarith
qed

text \<open>With \<open>m = \<Phi> \<xi>\<^sub>0 - \<delta>\<rho>\<^sup>2\<close>, the smallness condition
  the shifted doubled-jet package needs reduces to
  \<open>2 dd r < \<delta>\<rho>\<^sup>2\<close>, a condition on \<open>dd, r, \<delta>, \<rho>\<close> alone, so \<open>dd\<close> can
  always be chosen after \<open>\<delta>\<close> and \<open>\<rho>\<close>.\<close>

lemma shifted_jensen_smallness:
  fixes \<Phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes r: "0 < r" and dpos: "0 < \<delta>" and rho: "0 < \<rho>"
    and ddlt: "dd < (\<delta> * \<rho>\<^sup>2) / (2*r)"
  shows "2 * dd * r
      < (\<Phi> \<xi>\<^sub>0 - \<delta> * (norm (\<xi>\<^sub>0 - \<xi>\<^sub>0))\<^sup>2) - (\<Phi> \<xi>\<^sub>0 - \<delta> * \<rho>\<^sup>2)"
proof -
  have r2: "0 < 2*r" using r by simp
  have "dd * (2*r) < ((\<delta> * \<rho>\<^sup>2) / (2*r)) * (2*r)"
    by (rule mult_strict_right_mono[OF ddlt r2])
  also have "((\<delta> * \<rho>\<^sup>2) / (2*r)) * (2*r) = \<delta> * \<rho>\<^sup>2"
    using r2 by simp
  finally have "dd * (2*r) < \<delta> * \<rho>\<^sup>2" .
  then have "2 * dd * r < \<delta> * \<rho>\<^sup>2"
    by (simp add: algebra_simps)
  then show ?thesis by simp
qed

text \<open>A doubling maximiser is naturally stated for the unsplit functional
  \<open>A (fst y) + B (snd y) - penalty\<close>, whereas
  the shifted doubled-jet package wants its annulus bound with the
  two per-block quadratics written out; \<open>norm_sq_prod_split\<close> reconciles
  the two forms, and the centre value is unchanged since both quadratics
  vanish at \<open>\<xi>\<^sub>0\<close>.\<close>

lemma shifted_annulus_bound_split:
  fixes A B :: "'a::euclidean_space \<Rightarrow> real"
  assumes mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        A (fst y) + B (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
        \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2"
    and dpos: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
      \<le> (A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0)
            - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2) - \<delta> * \<rho>\<^sup>2"
proof -
  have sp: "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
      = (A (fst y) + B (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2)
        - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (simp add: norm_sq_prod_split algebra_simps)
  show ?thesis
    unfolding sp
    by (rule shifted_annulus_bound
        [where \<Phi> = "\<lambda>z. A (fst z) + B (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
           and \<xi>\<^sub>0 = \<xi>\<^sub>0 and r = r and \<delta> = \<delta> and \<rho> = \<rho>,
         OF mxK dpos rho y ann])
qed

text \<open>The jet transfer for a linear shift: a jet of \<open>f - c \<bullet> \<cdot>\<close> is a jet
  of \<open>f\<close> with the gradient moved by \<open>c\<close> and the Hessian untouched, by
  direct rewriting since the shift is affine.\<close>

lemma jet_transfer_quadratic:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lim: "((\<lambda>h. ((f (xh + h) - \<delta> * (norm (xh + h - c))\<^sup>2)
        - (f xh - \<delta> * (norm (xh - c))\<^sup>2)
        - p \<bullet> h - (h \<bullet> X h)/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (f (xh + h) - f xh
        - (p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h
        - (h \<bullet> (X h + (2*\<delta>) *\<^sub>R h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have eq: "(f (xh + h) - f xh
        - (p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h
        - (h \<bullet> (X h + (2*\<delta>) *\<^sub>R h))/2) / (norm h)\<^sup>2
      = ((f (xh + h) - \<delta> * (norm (xh + h - c))\<^sup>2)
        - (f xh - \<delta> * (norm (xh - c))\<^sup>2)
        - p \<bullet> h - (h \<bullet> X h)/2) / (norm h)\<^sup>2" for h
  proof -
    have re: "xh + h - c = (xh - c) + h" by simp
    have sq: "(norm (xh + h - c))\<^sup>2
        = (norm (xh - c))\<^sup>2 + 2 * ((xh - c) \<bullet> h) + (norm h)\<^sup>2"
      unfolding re
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    have ip: "(p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h = p \<bullet> h + 2*\<delta>*((xh - c) \<bullet> h)"
      by (simp add: inner_add_left)
    have hh: "h \<bullet> (X h + (2*\<delta>) *\<^sub>R h) = h \<bullet> X h + 2*\<delta>*(norm h)\<^sup>2"
      by (simp add: inner_add_right power2_norm_eq_inner)
    show ?thesis
      unfolding sq ip hh by (simp add: algebra_simps)
  qed
  show ?thesis
    unfolding eq by (rule lim)
qed

text \<open>Jensen's lemma returns a global maximum of the tilted functional
  \<open>\<Psi> + p \<cdot> \<cdot>\<close> over \<open>cball \<xi> r\<close>, whereas \<open>sums_ordering_at_interior_max\<close>
  wants a plain interior maximum on a ball. The tilt is harmless: it
  splits as \<open>fst p \<cdot> fst z + snd p \<cdot> snd z\<close> and absorbs into the two
  summands \<open>a\<close> and \<open>b\<close>, leaving the doubled block structure intact, so
  the global maximum restricts to an interior maximum on a ball of radius
  \<open>r - dist z' \<xi> > 0\<close> around \<open>z'\<close>.\<close>

lemma tilt_absorb:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
  shows "(a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + p \<bullet> z
       = (a (fst z) + fst p \<bullet> fst z) + (b (snd z) + snd p \<bullet> snd z)
         - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
  by (cases p, cases z) simp

lemma global_max_imp_interior_max:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<Psi> y \<le> \<Psi> zh"
    and kk: "norm k < r - dist zh \<xi>"
  shows "\<Psi> (zh + k) \<le> \<Psi> zh"
proof -
  have "dist (zh + k) \<xi> \<le> dist (zh + k) zh + dist zh \<xi>"
    by (rule dist_triangle)
  moreover have "dist (zh + k) zh = norm k"
    by (simp add: dist_norm)
  ultimately have "dist (zh + k) \<xi> \<le> norm k + dist zh \<xi>"
    by simp
  with kk have "dist (zh + k) \<xi> < r"
    by linarith
  then have "zh + k \<in> cball \<xi> r"
    by (simp add: dist_commute)
  then show ?thesis
    by (rule mx)
qed

lemma interior_radius_pos:
  fixes zh \<xi> :: "'a::euclidean_space"
  assumes "dist zh \<xi> < r"
  shows "0 < r - dist zh \<xi>"
  using assms by linarith

text \<open>Jensen's output becomes exactly the interior-maximum hypothesis of
  \<open>sums_ordering_at_interior_max\<close>, with the tilt absorbed into the two
  summands.\<close>

theorem doubled_tilted_interior_max:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh"
    and kk: "norm k < r - dist zh \<xi>"
  shows "(a (fst (zh + k)) + fst p \<bullet> fst (zh + k))
         + (b (snd (zh + k)) + snd p \<bullet> snd (zh + k))
         - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
       \<le> (a (fst zh) + fst p \<bullet> fst zh) + (b (snd zh) + snd p \<bullet> snd zh)
         - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::('a) \<times> ('a).
      (a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + p \<bullet> z)"
  have mxP: "\<Psi> y \<le> \<Psi> zh" if "y \<in> cball \<xi> r" for y
    unfolding \<Psi>_def by (rule mx[OF that])
  have "\<Psi> (zh + k) \<le> \<Psi> zh"
    by (rule global_max_imp_interior_max
        [where \<Psi> = \<Psi> and \<xi> = \<xi> and r = r and zh = zh and k = k,
         OF mxP kk])
  then show ?thesis
    unfolding \<Psi>_def tilt_absorb .
qed

text \<open>The linearity and symmetry of the two diagonal blocks that
  the Hessian ordering at an interior maximum needs follow from the Alexandrov jet's
  \<open>bounded_linear W\<close> and \<open>u \<cdot> W u' = u' \<cdot> W u\<close>, via
  \<open>linear_slice_fst\<close> / \<open>linear_slice_snd\<close> / \<open>sym_slice_fst\<close> /
  \<open>sym_slice_snd\<close> (@{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}).\<close>

lemma linear_of_bounded_linear_prod:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes blW: "bounded_linear W"
  shows "linear W"
proof (rule linearI)
  fix x y show "W (x + y) = W x + W y"
    using blW by (simp add: linear_simps)
next
  fix c x show "W (c *\<^sub>R x) = c *\<^sub>R W x"
    using blW by (simp add: linear_simps)
qed

lemma linear_block_fst:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
proof -
  have lW: "linear W"
    by (rule linear_of_bounded_linear_prod[OF blW])
  have "linear (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z)))"
    by (rule linear_slice_fst[OF lW])
  then show ?thesis by simp
qed

lemma linear_block_snd:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  have lW: "linear W"
    by (rule linear_of_bounded_linear_prod[OF blW])
  have "linear (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0)))"
    by (rule linear_slice_snd[OF lW])
  then show ?thesis by simp
qed

lemma sym_block_fst:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (fst (W (z, 0)) + \<alpha> *\<^sub>R z)
       = z \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
proof -
  have "v \<bullet> (\<lambda>y. fst (W (y, 0) + \<alpha> *\<^sub>R (y - 0, 0 - y))) z
      = z \<bullet> (\<lambda>y. fst (W (y, 0) + \<alpha> *\<^sub>R (y - 0, 0 - y))) v"
    by (rule sym_slice_fst[OF symW])
  then show ?thesis by simp
qed

lemma sym_block_snd:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (- (snd (W (0, z)) + \<alpha> *\<^sub>R z))
       = z \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  have "v \<bullet> (\<lambda>y. - snd (W (0, y) + \<alpha> *\<^sub>R (0 - y, y - 0))) z
      = z \<bullet> (\<lambda>y. - snd (W (0, y) + \<alpha> *\<^sub>R (0 - y, y - 0))) v"
    by (rule sym_slice_snd[OF symW])
  then show ?thesis by simp
qed

text \<open>A comparison argument reads the two block Hessians as symmetric
  matrices, so it needs \<open>transpose Xm = Xm\<close> and \<open>transpose Ym = Ym\<close>.  Both
  follow from the jet: \<open>matrix_of_symmetric\<close>
  (@{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}) converts an
  abstract symmetric linear map into a symmetric matrix, fed by the block
  lemmas above.\<close>

lemma transpose_matrix_block_fst:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
       = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
  by (rule matrix_of_symmetric[OF linear_block_fst[OF blW]
        sym_block_fst[OF symW]])

lemma transpose_matrix_block_snd:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
       = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
  by (rule matrix_of_symmetric[OF linear_block_snd[OF blW]
        sym_block_snd[OF symW]])

text \<open>A comparison argument needs the jets of \<open>\<theta> u\<close> at \<open>x'\<close> and of
  \<open>-w\<close> at \<open>y'\<close> to share a common gradient \<open>p\<close> (with sign \<open>p\<close>, \<open>-p\<close>).
  Since the penalty \<open>-(\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> contributes \<open>\<minusplus>\<alpha>(x - y)\<close> to the
  two blocks, this holds exactly when the doubled gradient
  \<open>q\<^sub>1 + q\<^sub>2 = 0\<close>, which is automatic since \<open>q = 0\<close> at an interior
  maximum (\<open>second_order_interior_max\<close>). This gives the common gradient
  \<open>p = \<alpha>(x' - y')\<close>, whose nonvanishing \<open>doubling_grad_nonzero\<close>
  establishes.\<close>

theorem gradient_vanishes_at_interior_max:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes blW: "bounded_linear W" and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow> \<Psi> (zh + k) \<le> \<Psi> zh"
    and expPsi: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
        / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = 0"
proof -
  have "q \<bullet> q = 0"
    using second_order_interior_max[OF blW dpos mx expPsi] by blast
  then show ?thesis
    by simp
qed

text \<open>The two component jets the envelope-form comparison assembly takes as
  hypotheses come from the doubled jet by restricting to the two
  coordinate slices. Moving the first argument by \<open>h\<close> and holding the
  second fixed changes \<open>(\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> by a linear term
  \<open>\<alpha>(x - y) \<cdot> h\<close> plus a quadratic term \<open>(\<alpha>/2)\<bar>h\<bar>\<^sup>2\<close>, exactly, since
  the penalty's Taylor expansion is exact -- the source of both the
  \<open>\<alpha>(x' - y')\<close> in the gradient and the \<open>+ \<alpha> v\<close> in the Hessian block.\<close>

lemma penalty_difference_identity:
  fixes x y h :: "'a::euclidean_space"
  shows "(\<alpha>/2) * (norm (x + h - y))\<^sup>2 - (\<alpha>/2) * (norm (x - y))\<^sup>2
       = \<alpha> * ((x - y) \<bullet> h) + (\<alpha>/2) * (norm h)\<^sup>2"
proof -
  have "(norm (x + h - y))\<^sup>2 = (norm ((x - y) + h))\<^sup>2"
    by (simp add: algebra_simps)
  also have "\<dots> = (norm (x - y))\<^sup>2 + 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
    by (simp add: power2_norm_eq_inner
        inner_commute algebra_simps)
  finally show ?thesis
    by (simp add: field_simps)
qed

text \<open>The slice embedding is a legitimate change of filter: as \<open>h\<close> tends
  to \<open>0\<close> in \<open>'a\<close> avoiding \<open>0\<close>, the pair \<open>(h, 0)\<close> tends to \<open>0\<close> in
  the product avoiding \<open>0\<close>, letting a limit statement about the doubled
  functional be evaluated along the slice.\<close>

lemma filterlim_slice_fst:
  "filterlim (\<lambda>h::'a::euclidean_space. (h, 0::'a)) (at 0) (at 0)"
proof (rule filterlim_atI)
  show "((\<lambda>h::'a. (h, 0::'a)) \<longlongrightarrow> 0) (at 0)"
    by (simp add: zero_prod_def tendsto_Pair)
next
  show "\<forall>\<^sub>F h in at (0 :: 'a). (h, 0::'a) \<noteq> 0"
    by (simp add: eventually_at_filter zero_prod_def)
qed

lemma filterlim_slice_snd:
  "filterlim (\<lambda>h::'a::euclidean_space. (0::'a, h)) (at 0) (at 0)"
proof (rule filterlim_atI)
  show "((\<lambda>h::'a. (0::'a, h)) \<longlongrightarrow> 0) (at 0)"
    by (simp add: zero_prod_def tendsto_Pair)
next
  show "\<forall>\<^sub>F h in at (0 :: 'a). (0::'a, h) \<noteq> 0"
    by (simp add: eventually_at_filter zero_prod_def)
qed

text \<open>The doubled jet restricts to the first slice: the \<open>b\<close> terms cancel
  since the second argument does not move, the penalty contributes
  \<open>\<alpha>(x' - y') \<cdot> h\<close> to the gradient and \<open>\<alpha> h\<close> to the Hessian, and
  \<open>W\<close> contributes its first diagonal block, exactly the block \<open>X\<close> of
  the theorem on sums.\<close>

lemma doubled_slice_numerator_fst:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  shows "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
        - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
      - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
      - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2)
    = a (fst zh + h) - a (fst zh)
      - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
      - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2"
proof -
  have p: "(\<alpha>/2) * (norm (fst zh + h - snd zh))\<^sup>2
      - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      = \<alpha> * ((fst zh - snd zh) \<bullet> h) + (\<alpha>/2) * (norm h)\<^sup>2"
    by (rule penalty_difference_identity)
  show ?thesis
    using p by (simp add: inner_prod_def inner_commute
        power2_norm_eq_inner algebra_simps)
qed

theorem doubled_jet_slice_fst:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_fst]
    by (simp add: o_def)
  have eq: "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2
      = (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2" for h
    unfolding doubled_slice_numerator_fst
    by (simp add: norm_Pair)
  from comp[unfolded eq] show ?thesis .
qed

text \<open>The same restriction for an arbitrary penalty \<open>P\<close> given by its jet: a
  general \<open>P\<close> has a remainder rather than an exact identity, so the two
  limits are added via \<open>tendsto_add\<close>, since \<open>P(d+h) - P(d)\<close> cancels
  between them (\<open>d = x' - y'\<close>). The resulting jet has gradient
  \<open>fst q + G\<close> and Hessian \<open>fst (W (h,0)) + Z h\<close>, the quadratic
  statement with \<open>\<alpha>(x' - y')\<close> replaced by \<open>G\<close> and \<open>\<alpha> h\<close> by \<open>Z h\<close>.\<close>

theorem doubled_jet_slice_fst_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_fst]
    by (simp add: o_def)
  have sum0: "((\<lambda>h. (((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      + ((P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF comp Pjet] by simp
  have eq: "(((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      + ((P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)
    = (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2" for h
  proof -
    have np: "norm ((h, 0) :: (real^'n) \<times> (real^'n)) = norm h"
      by (simp add: norm_Pair)
    have num: "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
            - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
          - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
          - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2)
        + (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
            - G \<bullet> h - (h \<bullet> (Z *v h))/2)
      = a (fst zh + h) - a (fst zh)
          - (fst q + G) \<bullet> h
          - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2"
      by (simp add: inner_prod_def
          algebra_simps)
    show ?thesis
      unfolding np
      using num by (simp add: add_divide_distrib[symmetric])
  qed
  from sum0[unfolded eq] show ?thesis .
qed

text \<open>The mirror image on the second slice: the penalty now moves the
  second argument, so its linear contribution changes sign, giving the
  gradient of \<open>b\<close> at \<open>y'\<close> as \<open>q\<^sub>2 - \<alpha>(x' - y')\<close>, while the quadratic
  contribution \<open>\<alpha> h\<close> to the Hessian keeps the same sign in both slices
  -- this asymmetry is what makes the two jets share \<open>p\<close> and \<open>-p\<close> while
  both blocks carry \<open>+ \<alpha> v\<close>.\<close>

lemma penalty_difference_identity_snd:
  fixes x y h :: "'a::euclidean_space"
  shows "(\<alpha>/2) * (norm (x - (y + h)))\<^sup>2 - (\<alpha>/2) * (norm (x - y))\<^sup>2
       = - (\<alpha> * ((x - y) \<bullet> h)) + (\<alpha>/2) * (norm h)\<^sup>2"
proof -
  have e1: "(norm (x - (y + h)))\<^sup>2
      = (norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
  proof -
    have "(norm (x - (y + h)))\<^sup>2 = (norm ((x - y) - h))\<^sup>2"
      by (simp add: algebra_simps)
    also have "\<dots> = (norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    finally show ?thesis .
  qed
  have e2: "(\<alpha>/2) * (norm (x - (y + h)))\<^sup>2
      = (\<alpha>/2) * ((norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2)"
    using e1 by simp
  show ?thesis
    using e2 by (simp add: algebra_simps)
qed

lemma doubled_slice_numerator_snd:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  shows "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
        - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
      - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
      - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2)
    = b (snd zh + h) - b (snd zh)
      - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
      - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2"
proof -
  have p: "(\<alpha>/2) * (norm (fst zh - (snd zh + h)))\<^sup>2
      - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      = - (\<alpha> * ((fst zh - snd zh) \<bullet> h)) + (\<alpha>/2) * (norm h)\<^sup>2"
    by (rule penalty_difference_identity_snd)
  show ?thesis
    using p by (simp add: inner_prod_def inner_commute
        power2_norm_eq_inner algebra_simps)
qed

theorem doubled_jet_slice_snd:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_snd]
    by (simp add: o_def)
  have eq: "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2
      = (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2" for h
    unfolding doubled_slice_numerator_snd
    by (simp add: norm_Pair)
  from comp[unfolded eq] show ?thesis .
qed

text \<open>The mirror slice for a general penalty: the second slice moves \<open>y\<close>,
  so the penalty is evaluated at \<open>d - h\<close>, and the jet hypothesis is
  transported along \<open>h \<mapsto> -h\<close>, a filter isomorphism of \<open>at 0\<close>
  (\<open>negfilt\<close>); the sign flips in \<open>(-h) \<bullet> (Z (-h))\<close> cancel, so the
  transported remainder is the same \<open>o(\<parallel>h\<parallel>\<^sup>2)\<close> with \<open>G \<bullet> h\<close> flipped,
  exactly why the two slice gradients come out as negatives.\<close>

theorem doubled_jet_slice_snd_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have mv: "Z *v (- h) = - (Z *v h)" for h :: "real^'n"
    by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
  have negfilt: "filterlim (\<lambda>h::real^'n. - h) (at 0) (at 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>h::real^'n. - h) \<longlongrightarrow> - 0) (at 0)"
      by (intro tendsto_intros)
    then show "((\<lambda>h::real^'n. - h) \<longlongrightarrow> 0) (at 0)" by simp
    show "\<forall>\<^sub>F h in at (0::real^'n). - h \<noteq> 0"
      by (simp add: eventually_at_filter)
  qed
  have Pneg0: "((\<lambda>h. (P ((fst zh - snd zh) + - h) - P (fst zh - snd zh)
      - G \<bullet> (- h) - ((- h) \<bullet> (Z *v (- h)))/2) / (norm (- h))\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF Pjet negfilt] by (simp add: o_def)
  have Pneg: "((\<lambda>h. (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
      + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have e: "(P ((fst zh - snd zh) + - h) - P (fst zh - snd zh)
          - G \<bullet> (- h) - ((- h) \<bullet> (Z *v (- h)))/2) / (norm (- h))\<^sup>2
        = (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
          + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2" for h
      by (simp add: mv algebra_simps)
    show ?thesis using Pneg0 unfolding e .
  qed
  have comp: "((\<lambda>h. ((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_snd]
    by (simp add: o_def)
  have sum0: "((\<lambda>h. (((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      + ((P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
        + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF comp Pneg] by simp
  have eq: "(((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      + ((P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
        + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)
    = (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2" for h
  proof -
    have np: "norm ((0, h) :: (real^'n) \<times> (real^'n)) = norm h"
      by (simp add: norm_Pair)
    have num: "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
            - P (fst (zh + (0, h)) - snd (zh + (0, h))))
          - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
          - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2)
        + (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
            + G \<bullet> h - (h \<bullet> (Z *v h))/2)
      = b (snd zh + h) - b (snd zh)
          - (snd q - G) \<bullet> h
          - (h \<bullet> (snd (W (0, h)) + Z *v h))/2"
      by (simp add: inner_prod_def
          algebra_simps)
    show ?thesis
      unfolding np
      using num by (simp add: add_divide_distrib[symmetric])
  qed
  from sum0[unfolded eq] show ?thesis .
qed

text \<open>With \<open>q = 0\<close> at the doubled maximum
  (\<open>gradient_vanishes_at_interior_max\<close>) the two gradients become
  \<open>\<alpha>(x' - y')\<close> and \<open>-\<alpha>(x' - y')\<close>, the shared \<open>p\<close> and \<open>-p\<close> that
  the envelope-form comparison assembly requires.\<close>

corollary doubled_jet_slices_at_max:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes blW: "bounded_linear W" and dpos: "0 < dd"
    and mx: "\<And>hk. norm hk < dd \<Longrightarrow>
        a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (\<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (\<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have q0: "q = 0"
    by (rule gradient_vanishes_at_interior_max[where \<Psi> = "\<lambda>z.
          a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
          and zh = zh and q = q and W = W and d = dd,
        OF blW dpos mx expPsi])
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (\<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using doubled_jet_slice_fst[OF expPsi] unfolding q0 by simp
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (\<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using doubled_jet_slice_snd[OF expPsi] unfolding q0 by simp
qed

text \<open>\<open>matrix_apply_eq\<close> is \<open>matrix_vec_apply\<close> from
  @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}.\<close>

lemma block_fst_matrix_apply:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v) *v h
       = fst (W (h, 0)) + \<alpha> *\<^sub>R h"
  by (rule matrix_vec_apply[OF linear_block_fst[OF blW]])

lemma block_snd_matrix_apply:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "(- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h
       = snd (W (0, h)) + \<alpha> *\<^sub>R h"
proof -
  have l: "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule linear_block_snd[OF blW])
  have "(- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h
      = - (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)) *v h)"
    by (rule matrix_vector_neg_left)
  also have "\<dots> = - (- (snd (W (0, h)) + \<alpha> *\<^sub>R h))"
    using matrix_vec_apply[OF l] by simp
  finally show ?thesis by simp
qed

text \<open>A second way to absorb Jensen's tilt, which removes the limit rather than
  controlling it: at an interior maximum of the tilted functional, the
  untilted jet has gradient exactly \<open>-p\<close>, since the tilt contributes
  \<open>p \<bullet> k\<close> to every increment.\<close>

theorem gradient_is_minus_tilt:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes blW: "bounded_linear W" and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow> \<Psi> (zh + k) + p \<bullet> (zh + k) \<le> \<Psi> zh + p \<bullet> zh"
    and expPsi: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
        / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - p"
proof -
  have mxT: "(\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) \<le> (\<lambda>z. \<Psi> z + p \<bullet> z) zh"
    if "norm k < d" for k
    using mx[OF that] by simp
  have expT: "((\<lambda>k. ((\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) - (\<lambda>z. \<Psi> z + p \<bullet> z) zh
        - (q + p) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have eq: "((\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) - (\<lambda>z. \<Psi> z + p \<bullet> z) zh
        - (q + p) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
      by (simp add: algebra_simps)
    show ?thesis
      unfolding eq by (rule expPsi)
  qed
  have "q + p = 0"
    by (rule gradient_vanishes_at_interior_max
        [where \<Psi> = "\<lambda>z. \<Psi> z + p \<bullet> z" and zh = zh and q = "q + p"
           and W = W and d = d,
         OF blW dpos mxT expT])
  then show ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

text \<open>The diagonal bound \<open>k \<bullet> Wk\<close> does not by itself bound the operator;
  polarisation recovers the off-diagonal entries by pure algebra, and the
  parallelogram law turns the result into a bound uniform over the unit
  sphere, with no spectral theory.\<close>

lemma polarization_symmetric:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
  shows "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
proof -
  have a: "W (u + v) = W u + W v"
    using lin unfolding linear_iff by blast
  have b: "W (u - v) = W u - W v"
    using lin by (simp add: linear_diff)
  have e1: "(u + v) \<bullet> W (u + v) = u \<bullet> W u + u \<bullet> W v + (v \<bullet> W u + v \<bullet> W v)"
    unfolding a by (simp add: inner_add_left inner_add_right)
  have e2: "(u - v) \<bullet> W (u - v) = u \<bullet> W u - u \<bullet> W v - (v \<bullet> W u - v \<bullet> W v)"
    unfolding b by (simp add: inner_diff_left inner_diff_right)
  have s: "v \<bullet> W u = u \<bullet> W v"
    by (rule sym)
  show ?thesis
    unfolding e1 e2 s by simp
qed

lemma parallelogram_norm:
  fixes u v :: "'a::euclidean_space"
  shows "(norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2
       = 2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2"
  by (simp add: power2_norm_eq_inner
      inner_commute algebra_simps)

theorem symmetric_form_bound:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
proof -
  have pol: "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
    by (rule polarization_symmetric[OF lin sym])
  have b1: "\<bar>(u + v) \<bullet> W (u + v)\<bar> \<le> c * (norm (u + v))\<^sup>2"
    by (rule bnd)
  have b2: "\<bar>(u - v) \<bullet> W (u - v)\<bar> \<le> c * (norm (u - v))\<^sup>2"
    by (rule bnd)
  have b1a: "- (c * (norm (u + v))\<^sup>2) \<le> (u + v) \<bullet> W (u + v)"
    using b1 by (simp add: abs_le_iff)
  have b1b: "(u + v) \<bullet> W (u + v) \<le> c * (norm (u + v))\<^sup>2"
    using b1 by (simp add: abs_le_iff)
  have b2a: "- (c * (norm (u - v))\<^sup>2) \<le> (u - v) \<bullet> W (u - v)"
    using b2 by (simp add: abs_le_iff)
  have b2b: "(u - v) \<bullet> W (u - v) \<le> c * (norm (u - v))\<^sup>2"
    using b2 by (simp add: abs_le_iff)
  have par: "(norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2
      = 2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2"
    by (rule parallelogram_norm)
  have e: "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
      = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
  proof -
    have "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
        = c * ((norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2)"
      by (simp add: algebra_simps)
    also have "\<dots> = c * (2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2)"
      unfolding par ..
    also have "\<dots> = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro abs_leI)
    show "u \<bullet> W v \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1b b2a e by linarith
    show "- (u \<bullet> W v) \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1a b2b e by linarith
  qed
qed

text \<open>On the unit sphere the bound is simply \<open>c\<close>: the Hessians at the doubled
  maxima are bounded entrywise by the semiconvexity constant, uniformly in
  the tilt, giving the boundedness a Bolzano-Weierstrass argument needs.\<close>

corollary symmetric_form_bound_unit:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
    and nu: "norm u = 1" and nv: "norm v = 1"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c"
proof -
  have "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
    by (rule symmetric_form_bound[OF lin sym bnd])
  then show ?thesis
    unfolding nu nv by simp
qed

text \<open>With the operator bound, Bolzano-Weierstrass applies directly: the
  perturbed data live in a ball of a finite-dimensional space, and
  \<open>cball\<close> is (sequentially) compact.  Stated for an arbitrary euclidean
  space, this covers the pair \<open>(gradient, Hessian)\<close> at once, since a
  product of euclidean spaces is euclidean.\<close>

theorem bounded_seq_limit_point:
  fixes Z :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes bnd: "\<And>i. norm (Z i) \<le> B"
  shows "\<exists>Z0 r. strict_mono r \<and> (\<lambda>i. Z (r i)) \<longlonglongrightarrow> Z0"
proof -
  have mem: "Z i \<in> cball (0::'a) B" for i
    using bnd[of i] by simp
  have sc: "seq_compact (cball (0::'a) B)"
    by (rule compact_imp_seq_compact[OF compact_cball])
  obtain Z0 r where sm: "strict_mono r" and lim: "(Z \<circ> r) \<longlonglongrightarrow> Z0"
    using sc mem unfolding seq_compact_def by blast
  show ?thesis
  proof (intro exI conjI)
    show "strict_mono r" by (rule sm)
    show "(\<lambda>i. Z (r i)) \<longlonglongrightarrow> Z0"
      using lim by (simp add: o_def)
  qed
qed

text \<open>If a property holds along a sequence converging to \<open>Z\<^sub>0\<close>, it holds at
  points arbitrarily close to \<open>Z\<^sub>0\<close> --- the hypothesis shape that estimates on a
  semicontinuous envelope need.  Stated for an arbitrary predicate, so it
  serves both the subsolution and the supersolution side.\<close>

theorem nearby_of_convergent:
  fixes Z :: "nat \<Rightarrow> 'a::metric_space"
  assumes conv: "Z \<longlonglongrightarrow> Z0" and P: "\<And>i. P (Z i)" and e0: "0 < e"
  shows "\<exists>z. dist z Z0 < e \<and> P z"
proof -
  from conv[unfolded lim_sequentially] e0
  obtain N where N: "\<And>i. N \<le> i \<Longrightarrow> dist (Z i) Z0 < e"
    by blast
  have d: "dist (Z N) Z0 < e"
    using N[of N] by simp
  have p: "P (Z N)"
    by (rule P)
  from d p show ?thesis by blast
qed

text \<open>\<open>p \<noteq> 0\<close> needs a positive lower bound on \<open>\<parallel>p\<parallel>\<close> along the family, not
  merely nonvanishing at each member.  If \<open>x̂\<close> misses the maximum of
  \<open>u - w\<close> by at least \<open>\<gamma>\<close>, comparing \<open>\<Phi>\<close> at \<open>(x̂,ŷ)\<close> against the diagonal
  point gives \<open>\<gamma> + (\<alpha>/2)\<parallel>x̂-ŷ\<parallel>\<^sup>2 \<le> w x̂ - w ŷ\<close>, so the value gap forces a
  position gap via a modulus of continuity for \<open>w\<close>; for Lipschitz \<open>w\<close> the
  bound is \<open>\<gamma>/L\<^sub>w\<close>, independent of \<open>\<alpha>\<close>.\<close>

theorem doubling_grad_lower_bound:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and zK: "z \<in> K" and xK: "xh \<in> K" and yK: "yh \<in> K"
    and a: "0 \<le> \<alpha>"
    and gap: "u xh - w xh + \<gamma> \<le> u z - w z"
    and lip: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> \<bar>w p - w q\<bar> \<le> Lw * norm (p - q)"
    and Lw: "0 < Lw"
  shows "\<gamma> / Lw \<le> norm (xh - yh)"
proof -
  have diag: "u z - w z
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule doubling_ge_diagonal[where u = u and w = w and K = K, OF zK mx])
  have sq: "0 \<le> (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    using a by simp
  have gw: "\<gamma> \<le> w xh - w yh"
    using diag gap sq by linarith
  have "\<bar>w xh - w yh\<bar> \<le> Lw * norm (xh - yh)"
    by (rule lip[OF xK yK])
  then have "\<gamma> \<le> Lw * norm (xh - yh)"
    using gw by linarith
  then show ?thesis
    using Lw by (simp add: field_simps)
qed

text \<open>The shared gradient \<open>p = \<alpha>(x̂-ŷ)\<close> has norm at least \<open>\<alpha>\<gamma>/L\<^sub>w\<close>, a bound
  holding fixed along the family, which is what lets \<open>p \<noteq> 0\<close> survive the
  limit.\<close>

corollary doubling_grad_norm_lower_bound:
  fixes u w :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and zK: "z \<in> K" and xK: "xh \<in> K" and yK: "yh \<in> K"
    and a: "0 < \<alpha>"
    and gap: "u xh - w xh + \<gamma> \<le> u z - w z"
    and lip: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> \<bar>w p - w q\<bar> \<le> Lw * norm (p - q)"
    and Lw: "0 < Lw"
  shows "\<alpha> * (\<gamma> / Lw) \<le> norm (\<alpha> *\<^sub>R (xh - yh))"
proof -
  have base: "\<gamma> / Lw \<le> norm (xh - yh)"
    by (rule doubling_grad_lower_bound[where u = u and w = w and K = K
          and z = z, OF mx zK xK yK less_imp_le[OF a] gap lip Lw])
  have step: "\<alpha> * (\<gamma> / Lw) \<le> \<alpha> * norm (xh - yh)"
    by (rule mult_left_mono[OF base less_imp_le[OF a]])
  have nrm: "norm (\<alpha> *\<^sub>R (xh - yh)) = \<alpha> * norm (xh - yh)"
  proof -
    have ab: "\<bar>\<alpha>\<bar> = \<alpha>"
      by (rule abs_of_pos[OF a])
    have "norm (\<alpha> *\<^sub>R (xh - yh)) = \<bar>\<alpha>\<bar> * norm (xh - yh)"
      by (rule norm_scaleR)
    then show ?thesis unfolding ab .
  qed
  show ?thesis unfolding nrm by (rule step)
qed

text \<open>The last hypothesis of the strict-inequality contradiction at the limit - that the
  two gradient sequences share a limit - follows from the tilts shrinking
  to zero: with tilt \<open>p\<^sub>i\<close> the untilted jet has gradient \<open>-p\<^sub>i\<close>, so the two
  block gradients differ by \<open>fst p\<^sub>i + snd p\<^sub>i\<close> alone, independent of the
  maximiser.\<close>

lemma tendsto_of_norm_bound:
  fixes Z :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes b: "\<And>i. norm (Z i) \<le> D i" and D: "D \<longlonglongrightarrow> 0"
  shows "Z \<longlonglongrightarrow> 0"
proof (rule Lim_null_comparison[OF _ D])
  show "\<forall>\<^sub>F i in sequentially. norm (Z i) \<le> D i"
    using b by simp
qed

theorem gradient_sequences_align:
  fixes Pt :: "nat \<Rightarrow> ('a::euclidean_space) \<times> ('a)" and G :: "nat \<Rightarrow> 'a"
  assumes tilt: "Pt \<longlonglongrightarrow> 0" and gconv: "G \<longlonglongrightarrow> g"
  shows "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    and "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
proof -
  have f0: "(\<lambda>i. fst (Pt i)) \<longlonglongrightarrow> 0"
    using tendsto_fst[OF tilt] by (simp add: zero_prod_def)
  have s0: "(\<lambda>i. snd (Pt i)) \<longlonglongrightarrow> 0"
    using tendsto_snd[OF tilt] by (simp add: zero_prod_def)
  show "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    using tendsto_add[OF tendsto_minus[OF f0] gconv] by simp
  show "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
    using tendsto_add[OF s0 gconv] by simp
qed

text \<open>The doubling supplies tilts bounded by a sequence \<open>dd\<^sub>i \<rightarrow> 0\<close>, exactly
  what re-running Jensen with a shrinking tilt parameter gives.\<close>

corollary gradient_sequences_align_of_bound:
  fixes Pt :: "nat \<Rightarrow> ('a::euclidean_space) \<times> ('a)" and G :: "nat \<Rightarrow> 'a"
  assumes b: "\<And>i. norm (Pt i) \<le> dd i" and dd: "dd \<longlonglongrightarrow> 0"
    and gconv: "G \<longlonglongrightarrow> g"
  shows "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    and "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
proof -
  have t0: "Pt \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF b dd])
  show "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    by (rule gradient_sequences_align(1)[OF t0 gconv])
  show "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
    by (rule gradient_sequences_align(2)[OF t0 gconv])
qed

text \<open>the strict-inequality contradiction at the limit wants the operator bound at
  \<open>X\<^sub>i\<close>, but the shifted subsolution bound only delivers it at the
  corrected matrix \<open>X\<^sub>i+\<delta>I\<close>, so the two limits \<open>i \<rightarrow> \<infinity>\<close> and \<open>\<delta> \<rightarrow> 0\<close>
  must be taken together via the nearby-point formulation.  The predicate
  is taken curried, as \<open>Q p' M'\<close> rather than \<open>P (p', M')\<close>, so that \<open>OF\<close>
  unifies against the unreduced projections.\<close>

theorem nearby_of_convergent_shifted:
  fixes Pz :: "nat \<Rightarrow> real^'n::finite" and Mz :: "nat \<Rightarrow> real^'n^'n"
  assumes conv: "(\<lambda>i. (Pz i, Mz i)) \<longlonglongrightarrow> Z0"
    and Q: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> Q (Pz i) (Mz i + \<delta> *\<^sub>R mat 1)"
    and D: "0 < D" and e0: "0 < e"
  shows "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) Z0 < e
      \<and> Q p' M'"
proof -
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e/2"
  proof -
    have dle: "d \<le> e/(2*(N+1))" unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e/2"
    proof -
      have expand: "(e/2) * (2*(N+1)) = e * N + e"
        by (simp add: algebra_simps)
      have "e * N < (e/2) * (2*(N+1))"
        unfolding expand using e0 by linarith
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have e2: "0 < e/2" using e0 by simp
  from conv[unfolded lim_sequentially] e2
  obtain M where M: "\<And>i. M \<le> i \<Longrightarrow> dist ((Pz i, Mz i)) Z0 < e/2"
    by blast
  have dz: "dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0 < e/2"
    using M[of M] by simp
  have shift: "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      (Pz M, Mz M) = d * N"
  proof -
    have "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        = sqrt ((dist (Pz M) (Pz M))\<^sup>2
            + (dist (Mz M + d *\<^sub>R mat 1) (Mz M))\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (Mz M + d *\<^sub>R mat 1) (Mz M)"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have tri: "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) Z0
      \<le> dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        + dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0"
    by (rule dist_triangle)
  have near: "dist ((Pz M, Mz M + d *\<^sub>R mat 1)
      :: (real^'n) \<times> (real^'n^'n)) Z0 < e"
    using tri shift small dz by linarith
  have q: "Q (Pz M) (Mz M + d *\<^sub>R mat 1)"
    by (rule Q[OF d0 dD])
  from near q show ?thesis by blast
qed

text \<open>The mirrored version for the supersolution side: the correction runs the
  other way, \<open>Y\<^sub>i-\<delta>I\<close>, but the estimate is identical since the shift has
  the same norm.\<close>

theorem nearby_of_convergent_shifted_neg:
  fixes Pz :: "nat \<Rightarrow> real^'n::finite" and Mz :: "nat \<Rightarrow> real^'n^'n"
  assumes conv: "(\<lambda>i. (Pz i, Mz i)) \<longlonglongrightarrow> Z0"
    and Q: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> Q (Pz i) (Mz i - \<delta> *\<^sub>R mat 1)"
    and D: "0 < D" and e0: "0 < e"
  shows "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) Z0 < e
      \<and> Q p' M'"
proof -
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e/2"
  proof -
    have dle: "d \<le> e/(2*(N+1))" unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e/2"
    proof -
      have expand: "(e/2) * (2*(N+1)) = e * N + e"
        by (simp add: algebra_simps)
      have "e * N < (e/2) * (2*(N+1))"
        unfolding expand using e0 by linarith
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have e2: "0 < e/2" using e0 by simp
  from conv[unfolded lim_sequentially] e2
  obtain M where M: "\<And>i. M \<le> i \<Longrightarrow> dist ((Pz i, Mz i)) Z0 < e/2"
    by blast
  have dz: "dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0 < e/2"
    using M[of M] by simp
  have shift: "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      (Pz M, Mz M) = d * N"
  proof -
    have "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        = sqrt ((dist (Pz M) (Pz M))\<^sup>2
            + (dist (Mz M - d *\<^sub>R mat 1) (Mz M))\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (Mz M - d *\<^sub>R mat 1) (Mz M)"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have tri: "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) Z0
      \<le> dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        + dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0"
    by (rule dist_triangle)
  have near: "dist ((Pz M, Mz M - d *\<^sub>R mat 1)
      :: (real^'n) \<times> (real^'n^'n)) Z0 < e"
    using tri shift small dz by linarith
  have q: "Q (Pz M) (Mz M - d *\<^sub>R mat 1)"
    by (rule Q[OF d0 dD])
  from near q show ?thesis by blast
qed

text \<open>the sequential comparison assembly consumes a sequence of Jensen
  applications with tilts shrinking to zero.  Jensen's smallness condition
  \<open>2 dd r < \<Phi>(\<xi>)-m\<close> holds for every sufficiently small tilt once the
  centre beats the boundary value at all, so an admissible sequence
  converging to zero always exists.\<close>

lemma jensen_tilt_threshold_pos:
  fixes r m Psixi :: real
  assumes gap: "m < Psixi" and r: "0 < r"
  shows "0 < (Psixi - m) / (2*r)"
  using gap r by simp

lemma jensen_tilt_small_enough:
  fixes r m Psixi dd :: real
  assumes r: "0 < r"
    and dlt: "dd < (Psixi - m) / (2*r)"
  shows "2 * dd * r < Psixi - m"
proof -
  have r2: "0 < 2*r" using r by simp
  have "dd * (2*r) < ((Psixi - m) / (2*r)) * (2*r)"
    by (rule mult_strict_right_mono[OF dlt r2])
  also have "((Psixi - m) / (2*r)) * (2*r) = Psixi - m"
    using r2 by simp
  finally have "dd * (2*r) < Psixi - m" .
  then show ?thesis
    by (simp add: algebra_simps)
qed

text \<open>An explicit admissible sequence, not canonical, giving the family
  construction a concrete witness rather than a bare existence claim.\<close>

lemma tilt_sequence_pos:
  fixes D :: real
  assumes D: "0 < D"
  shows "0 < D / (2 + real i)"
  using D by simp

lemma tilt_sequence_lt:
  fixes D :: real
  assumes D: "0 < D"
  shows "D / (2 + real i) < D"
proof -
  have den: "(1::real) < 2 + real i" by simp
  have "D / (2 + real i) < D / 1"
    by (rule divide_strict_left_mono[OF den D]) simp
  then show ?thesis by simp
qed

lemma tilt_sequence_tendsto:
  fixes D :: real
  shows "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
proof -
  have F: "filterlim (\<lambda>i. 2 + real i) at_top sequentially"
    by (rule filterlim_tendsto_add_at_top[OF tendsto_const
          filterlim_real_sequentially])
  show ?thesis
    by (rule tendsto_divide_0[OF tendsto_const
          filterlim_at_top_imp_at_infinity[OF F]])
qed

theorem tilt_sequence_admissible:
  fixes D :: real
  assumes D: "0 < D"
  shows "\<And>i. 0 < D / (2 + real i)"
    and "\<And>i. D / (2 + real i) < D"
    and "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
proof -
  show "0 < D / (2 + real i)" for i
    by (rule tilt_sequence_pos[OF D])
  show "D / (2 + real i) < D" for i
    by (rule tilt_sequence_lt[OF D])
  show "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
qed

text \<open>\<open>doubling_grad_lower_bound\<close> converts a value gap in \<open>w\<close> into a position
  gap via a Lipschitz modulus, more than continuity on compact \<open>K\<close>
  supplies.  Continuity plus compactness suffices instead: pairs in
  \<open>K \<times> K\<close> realising a fixed gap \<open>\<gamma> > 0\<close> stay bounded away from the
  diagonal, since a sequence with \<open>\<parallel>p\<^sub>n-q\<^sub>n\<parallel> \<rightarrow> 0\<close> would force \<open>\<gamma> \<le> 0\<close>
  by continuity at the common limit.  The resulting separation depends on
  \<open>\<gamma>\<close>, \<open>K\<close> and \<open>v\<close> but not \<open>\<alpha>\<close>.\<close>

lemma positive_separation_of_value_gap:
  fixes v :: "'a::real_normed_vector \<Rightarrow> real"
  assumes cK: "compact K" and cv: "continuous_on K v" and g: "0 < \<gamma>"
  shows "\<exists>d>0. \<forall>p\<in>K. \<forall>q\<in>K. \<gamma> \<le> v p - v q \<longrightarrow> d \<le> norm (p - q)"
proof (rule ccontr)
  assume "\<not> (\<exists>d>0. \<forall>p\<in>K. \<forall>q\<in>K. \<gamma> \<le> v p - v q \<longrightarrow> d \<le> norm (p - q))"
  then have H: "\<And>d. 0 < d \<Longrightarrow> \<exists>p\<in>K. \<exists>q\<in>K. \<gamma> \<le> v p - v q \<and> norm (p - q) < d"
    by force
  have ex: "\<forall>n::nat. \<exists>z. fst z \<in> K \<and> snd z \<in> K
      \<and> \<gamma> \<le> v (fst z) - v (snd z) \<and> norm (fst z - snd z) < 1/(2 + real n)"
  proof
    fix n :: nat
    have pos: "0 < 1/(2 + real n)" by simp
    obtain p q where "p \<in> K" "q \<in> K" "\<gamma> \<le> v p - v q"
        "norm (p - q) < 1/(2 + real n)"
      using H[OF pos] by blast
    then show "\<exists>z. fst z \<in> K \<and> snd z \<in> K
        \<and> \<gamma> \<le> v (fst z) - v (snd z) \<and> norm (fst z - snd z) < 1/(2 + real n)"
      by (intro exI[of _ "(p, q)"]) simp
  qed
  have exZ: "\<exists>Z. \<forall>n. fst (Z n) \<in> K \<and> snd (Z n) \<in> K
      \<and> \<gamma> \<le> v (fst (Z n)) - v (snd (Z n))
      \<and> norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)"
    using ex by (rule choice)
  then obtain Z where Z: "\<forall>n. fst (Z n) \<in> K \<and> snd (Z n) \<in> K
      \<and> \<gamma> \<le> v (fst (Z n)) - v (snd (Z n))
      \<and> norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)"
    by blast
  have pK: "fst (Z n) \<in> K" for n using Z by blast
  have qK: "snd (Z n) \<in> K" for n using Z by blast
  have gapn: "\<gamma> \<le> v (fst (Z n)) - v (snd (Z n))" for n using Z by blast
  have small: "norm (fst (Z n) - snd (Z n)) \<le> 1/(2 + real n)" for n
  proof -
    have "norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)" using Z by blast
    then show ?thesis by linarith
  qed
  have diff0: "(\<lambda>n. fst (Z n) - snd (Z n)) \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF small tilt_sequence_tendsto])
  have allp: "\<forall>n. fst (Z n) \<in> K" using pK by blast
  obtain l r where lK: "l \<in> K" and sm: "strict_mono r"
    and lim: "((\<lambda>n. fst (Z n)) \<circ> r) \<longlonglongrightarrow> l"
    by (rule seq_compactE[OF compact_imp_seq_compact[OF cK] allp])
  have limp: "(\<lambda>n. fst (Z (r n))) \<longlonglongrightarrow> l" using lim by (simp add: o_def)
  have limq: "(\<lambda>n. snd (Z (r n))) \<longlonglongrightarrow> l"
  proof -
    have "((\<lambda>n. fst (Z n) - snd (Z n)) \<circ> r) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_subseq_LIMSEQ[OF diff0 sm])
    then have d0: "(\<lambda>n. fst (Z (r n)) - snd (Z (r n))) \<longlonglongrightarrow> 0"
      by (simp add: o_def)
    have "(\<lambda>n. fst (Z (r n)) - (fst (Z (r n)) - snd (Z (r n)))) \<longlonglongrightarrow> l - 0"
      by (rule tendsto_diff[OF limp d0])
    then show ?thesis by simp
  qed
  have seqc: "\<And>x a. a \<in> K \<Longrightarrow> (\<forall>n. x n \<in> K) \<Longrightarrow> x \<longlonglongrightarrow> a \<Longrightarrow> (v \<circ> x) \<longlonglongrightarrow> v a"
    using cv unfolding continuous_on_sequentially by blast
  have cvp: "(\<lambda>n. v (fst (Z (r n)))) \<longlonglongrightarrow> v l"
  proof -
    have "(v \<circ> (\<lambda>n. fst (Z (r n)))) \<longlonglongrightarrow> v l"
      by (rule seqc[OF lK _ limp]) (use pK in blast)
    then show ?thesis by (simp add: o_def)
  qed
  have cvq: "(\<lambda>n. v (snd (Z (r n)))) \<longlonglongrightarrow> v l"
  proof -
    have "(v \<circ> (\<lambda>n. snd (Z (r n)))) \<longlonglongrightarrow> v l"
      by (rule seqc[OF lK _ limq]) (use qK in blast)
    then show ?thesis by (simp add: o_def)
  qed
  have "\<gamma> \<le> v l - v l"
  proof (rule tendsto_lowerbound[OF tendsto_diff[OF cvp cvq]])
    show "\<forall>\<^sub>F n in sequentially. \<gamma> \<le> v (fst (Z (r n))) - v (snd (Z (r n)))"
      using gapn by simp
  qed simp
  then show False using g by simp
qed

text \<open>The parameter choice for the shifted family: the perturbation \<open>\<delta>\<^sub>i\<close> and
  Jensen's tilt \<open>dd\<^sub>i\<close> must satisfy \<open>shifted_jensen_smallness\<close>'s
  \<open>dd\<^sub>i < \<delta>\<^sub>i\<rho>\<^sup>2/(2r)\<close>; taking \<open>\<delta>\<^sub>i=D\<^sub>0/(2+i)\<close> and \<open>dd\<^sub>i=\<delta>\<^sub>i\<rho>\<^sup>2/(4r)\<close>
  satisfies it with room to spare, and both sequences vanish.\<close>

lemma shifted_family_parameters:
  fixes D\<^sub>0 \<rho> r :: real
  assumes D0: "0 < D\<^sub>0" and rho: "0 < \<rho>" and r: "0 < r"
  shows "0 < D\<^sub>0/(2 + real i)"
    and "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)"
    and "D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
        < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (2*r)"
    and "(\<lambda>i. D\<^sub>0/(2 + real i)) \<longlonglongrightarrow> 0"
    and "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) \<longlonglongrightarrow> 0"
proof -
  show d1: "0 < D\<^sub>0/(2 + real i)"
    by (rule tilt_sequence_pos[OF D0])
  have rs: "0 < \<rho>\<^sup>2" using rho by simp
  have dr: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
    by (rule mult_pos_pos[OF d1 rs])
  have r4: "0 < 4*r" using r by simp
  show "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)"
    by (rule divide_pos_pos[OF dr r4])
  show "D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (2*r)"
    by (rule divide_strict_left_mono[OF _ dr]) (use r in auto)
  show t0: "(\<lambda>i. D\<^sub>0/(2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
  have "(\<lambda>i. D\<^sub>0/(2 + real i) * (\<rho>\<^sup>2 / (4*r))) \<longlonglongrightarrow> 0 * (\<rho>\<^sup>2 / (4*r))"
    by (rule tendsto_mult[OF t0 tendsto_const])
  then show "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) \<longlonglongrightarrow> 0"
    by simp
qed

text \<open>Extending an usc \<open>u\<close> off a closed \<open>K\<close> by a constant at or below its
  minimum on \<open>K\<close> keeps it usc; \<open>usc_extension_bounded\<close> in the
  \<open>Semicontinuous_Analysis\<close> session does the \<open>-B\<close> case, needed as negative
  as required so the doubled functional cannot be maximised off \<open>K\<close>.\<close>

lemma usc_extend_const_below:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and K :: "('a) set"
  assumes cl: "closed K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lo: "\<And>y. y \<in> K \<Longrightarrow> Bl \<le> u y" and CB: "C \<le> Bl"
    and lt: "(if z \<in> K then u z else C) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (if y \<in> K then u y else C) < c"
proof (cases "z \<in> K")
  case True
  then have uz: "u z < c" using lt by simp
  have Cc: "C < c" using CB lo[OF True] uz by linarith
  obtain e where e0: "0 < e" and h: "\<And>y. dist z y < e \<Longrightarrow> u y < c"
    using uscu[OF uz] by blast
  show ?thesis
  proof (rule exI[of _ e], intro conjI allI impI e0)
    fix y assume "dist z y < e"
    then show "(if y \<in> K then u y else C) < c" using h Cc by simp
  qed
next
  case False
  then have Cc: "C < c" using lt by simp
  have opn: "open (- K)" using cl by (rule open_Compl)
  have zin: "z \<in> - K" using False by simp
  obtain e where e0: "0 < e" and bl: "ball z e \<subseteq> - K"
    using opn zin unfolding open_contains_ball by blast
  show ?thesis
  proof (rule exI[of _ e], intro conjI allI impI e0)
    fix y assume dy: "dist z y < e"
    then have "y \<in> ball z e" by (simp add: dist_commute)
    then have "y \<notin> K" using bl by blast
    then show "(if y \<in> K then u y else C) < c" using Cc by simp
  qed
qed

text \<open>The two-domain localised maximiser drops the \<open>x\<close>-side boundary
  avoidance of the one-domain version: maximise the doubled sup-convolved
  functional over the compact
  \<open>Q \<times> K'\<close>; if the \<open>x\<close>-side sup-convolution is below \<open>\<beta>\<close> off \<open>Q\<close> and a
  witness beats \<open>\<beta>+B\<^sub>w\<close>, the maximiser maximises over all of
  \<open>UNIV \<times> K'\<close>, leaving only the \<open>y\<close>-coordinate constrained - which
  \<open>K \<subseteq> K'\<^sup>\<circ>\<close> gives room for.  This is the shape a two-domain
  comparison principle needs.\<close>

lemma doubled_maximiser_over_UNIV_snd:
  fixes A Bfun Pn :: "'a::euclidean_space \<Rightarrow> real" and K' Q :: "('a) set"
  assumes cQ: "compact Q" and cK': "compact K'"
    and cA: "continuous_on UNIV A" and cB: "continuous_on UNIV Bfun"
    and cP: "continuous_on UNIV Pn"
    and zQ: "z \<in> Q" and zK': "z \<in> K'"
    and Bw: "\<And>y. Bfun y \<le> Bw"
    and Pnn: "\<And>d. 0 \<le> Pn d"
    and out: "\<And>x. x \<notin> Q \<Longrightarrow> A x \<le> \<beta>"
    and gapv: "\<beta> + Bw < A z + Bfun z - Pn (z - z)"
  obtains xh yh where "xh \<in> Q" and "yh \<in> K'"
    and "\<And>x y. y \<in> K' \<Longrightarrow>
        A x + Bfun y - Pn (x - y) \<le> A xh + Bfun yh - Pn (xh - yh)"
proof -
  define S where "S = Q \<times> K'"
  define F where "F = (\<lambda>p :: ('a) \<times> ('a).
      A (fst p) + Bfun (snd p) - Pn (fst p - snd p))"
  have cS: "compact S" unfolding S_def by (rule compact_Times[OF cQ cK'])
  have zS: "(z, z) \<in> S" unfolding S_def using zQ zK' by simp
  have neS: "S \<noteq> {}" using zS by blast
  have cF: "continuous_on S F"
    unfolding F_def
    by (intro continuous_intros
        continuous_on_compose2[OF cA continuous_on_fst[OF continuous_on_id]]
        continuous_on_compose2[OF cB continuous_on_snd[OF continuous_on_id]]
        continuous_on_compose2[OF cP])
      auto
  obtain \<xi> where xiS: "\<xi> \<in> S" and mxS: "\<And>p. p \<in> S \<Longrightarrow> F p \<le> F \<xi>"
    using continuous_attains_sup[OF cS neS cF] by blast
  have xhQ: "fst \<xi> \<in> Q" and yhK: "snd \<xi> \<in> K'"
    using xiS unfolding S_def by auto
  have base: "A z + Bfun z - Pn (z - z) \<le> F \<xi>"
    using mxS[OF zS] unfolding F_def by simp
  have all: "A x + Bfun y - Pn (x - y)
      \<le> A (fst \<xi>) + Bfun (snd \<xi>) - Pn (fst \<xi> - snd \<xi>)" if y: "y \<in> K'" for x y
  proof (cases "x \<in> Q")
    case True
    then have "(x, y) \<in> S" unfolding S_def using y by simp
    from mxS[OF this] show ?thesis unfolding F_def by simp
  next
    case False
    have "A x + Bfun y - Pn (x - y) \<le> \<beta> + Bw"
      using out[OF False] Bw[of y] Pnn[of "x - y"] by linarith
    also have "\<dots> < A z + Bfun z - Pn (z - z)" by (rule gapv)
    also have "\<dots> \<le> F \<xi>" by (rule base)
    finally show ?thesis unfolding F_def by simp
  qed
  show ?thesis by (rule that[OF xhQ yhK]) (use all in blast)
qed

text \<open>Maximality over \<open>UNIV \<times> K'\<close> restricts to the ball the Crandall--Ishii
  core wants as soon as the \<open>y\<close>-coordinate has room; the \<open>x\<close>-coordinate is
  unconstrained.\<close>

lemma mxK_of_UNIV_snd:
  fixes A Bfun Pn :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>x y. y \<in> K' \<Longrightarrow>
      A x + Bfun y - Pn (x - y)
      \<le> A (fst \<xi>\<^sub>0) + Bfun (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and ball: "cball (snd \<xi>\<^sub>0) r \<subseteq> K'"
    and p: "p \<in> cball \<xi>\<^sub>0 r"
  shows "A (fst p) + Bfun (snd p) - Pn (fst p - snd p)
      \<le> A (fst \<xi>\<^sub>0) + Bfun (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
proof -
  have "dist (snd p) (snd \<xi>\<^sub>0) \<le> dist p \<xi>\<^sub>0" by (rule dist_snd_le)
  also have "\<dots> \<le> r" using p by (simp add: dist_commute)
  finally have "snd p \<in> cball (snd \<xi>\<^sub>0) r" by (simp add: dist_commute)
  then have "snd p \<in> K'" using ball by blast
  from mx[OF this] show ?thesis .
qed

text \<open>The other half of the two-domain interface: the core reads the
  subsolution property at the attainment point of \<open>supconv(\<theta>u)\<epsilon>\<close> over the
  \<open>\<rho>\<close>-ball around \<open>x\<^sup>h\<close>, and a definition gated on \<open>{u>0}\<close> admits
  that point whenever the sup-convolution is positive there, since the
  attained value adds a nonnegative penalty.  Positivity on the whole
  ball, not just at \<open>x\<^sup>h\<close>, is free since \<open>\<rho>\<close> is a free parameter
  preserved by shrinking.\<close>

lemma cont_pos_near:
  fixes A :: "'a::euclidean_space \<Rightarrow> real"
  assumes cA: "continuous_on UNIV A" and pos: "0 < A p"
  obtains \<rho> where "0 < \<rho>" and "\<And>x. dist x p \<le> \<rho> \<Longrightarrow> 0 < A x"
proof -
  have ic: "isCont A p"
    using cA by (simp add: continuous_on_eq_continuous_at)
  obtain d where d0: "0 < d"
    and h: "\<And>x. dist x p < d \<Longrightarrow> dist (A x) (A p) < A p"
    using ic[unfolded continuous_at_eps_delta] pos by blast
  show ?thesis
  proof (rule that[of "d/2"])
    show "0 < d/2" using d0 by simp
    fix x assume "dist x p \<le> d/2"
    then have "dist x p < d" using d0 by linarith
    from h[OF this] have "\<bar>A x - A p\<bar> < A p" by (simp add: dist_real_def)
    then show "0 < A x" by linarith
  qed
qed

lemma supconv_radius_uniform:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes lo: "\<And>y. Bl \<le> u y" and e: "0 < \<epsilon>" and h: "0 < \<eta>"
    and small: "2*\<epsilon>*(Bu - Bl) < \<eta>\<^sup>2"
  shows "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < \<eta>"
proof -
  have mono: "2*\<epsilon>*(Bu - u x) \<le> 2*\<epsilon>*(Bu - Bl)"
    by (rule mult_left_mono) (use lo[of x] e in linarith)+
  have hpos: "0 < \<eta>\<^sup>2" using h by simp
  have mx: "max 0 (2*\<epsilon>*(Bu - u x)) < \<eta>\<^sup>2"
  proof (cases "0 \<le> 2*\<epsilon>*(Bu - u x)")
    case True
    then have "max 0 (2*\<epsilon>*(Bu - u x)) = 2*\<epsilon>*(Bu - u x)" by simp
    then show ?thesis using mono small by linarith
  next
    case False
    then have "max 0 (2*\<epsilon>*(Bu - u x)) = 0" by simp
    then show ?thesis using hpos by linarith
  qed
  have "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < sqrt (\<eta>\<^sup>2)"
    by (rule real_sqrt_less_mono[OF mx])
  moreover have "sqrt (\<eta>\<^sup>2) = \<eta>" using h by simp
  ultimately show ?thesis by simp
qed

text \<open>This step makes \<open>interior K\<close>, not \<open>K\<close>, the domain where the viscosity
  properties are used.  The needed geometric data at the doubling
  maximiser \<open>(x̂,ŷ)\<close> - \<open>cball \<xi>\<^sub>0 r \<subseteq> K \<times> K\<close> and
  \<open>cball x R\<^sub>u \<subseteq> interior K\<close> - follows by
  \<open>cball_subset_interior_of_far_from_boundary\<close> from \<open>x̂\<close> and \<open>ŷ\<close> lying more
  than \<open>\<kappa>\<close> from \<open>K - interior K\<close>, which the interior/boundary gap of
  \<open>\<theta>u-w\<close> forces via \<open>m + 2\<sigma> + \<tau> + \<tau>' < M\<close>, each small quantity
  controlled by a free parameter (\<open>\<sigma>\<close> by \<open>\<epsilon>\<close>, \<open>\<tau>\<close> by \<open>\<alpha>\<close>, \<open>\<tau>'\<close> by
  \<open>\<kappa>\<close>).  Stated for abstract \<open>f\<close>, \<open>g\<close> and moduli, so the sup-convolutions
  and \<open>\<theta>\<close>-scaling stay invisible.\<close>

lemma uniform_modulus_on_compact:
  fixes v :: "'a::heine_borel \<Rightarrow> real"
  assumes cC: "compact C" and cv: "continuous_on C v" and s: "0 < \<sigma>"
  shows "\<exists>\<eta>>0. \<forall>p\<in>C. \<forall>q\<in>C. dist p q \<le> \<eta> \<longrightarrow> v q \<le> v p + \<sigma>"
proof -
  have uc: "uniformly_continuous_on C v"
    by (rule compact_uniformly_continuous[OF cv cC])
  obtain d where d0: "0 < d"
    and dd: "\<And>x x'. x \<in> C \<Longrightarrow> x' \<in> C \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (v x') (v x) < \<sigma>"
    by (rule uniformly_continuous_onE[OF uc s]) blast
  have main: "\<forall>p\<in>C. \<forall>q\<in>C. dist p q \<le> d/2 \<longrightarrow> v q \<le> v p + \<sigma>"
  proof (intro ballI impI)
    fix p q assume p: "p \<in> C" and q: "q \<in> C" and dpq: "dist p q \<le> d/2"
    have "dist q p < d" using dpq d0 by (simp add: dist_commute)
    then have "dist (v q) (v p) < \<sigma>" by (rule dd[OF p q])
    then show "v q \<le> v p + \<sigma>" by (simp add: dist_real_def)
  qed
  have "0 < d/2" using d0 by simp
  then show ?thesis using main by blast
qed

theorem doubling_maximiser_far_from_boundary:
  fixes f g :: "'a::euclidean_space \<Rightarrow> real"
  assumes xK: "xh \<in> K" and yK: "yh \<in> K"
    and val: "M \<le> f z + g z"
    and tr: "f z + g z \<le> f xh + g yh + 2*\<sigma>"
    and near: "dist xh yh \<le> \<beta>"
    and modg: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<beta> \<Longrightarrow> g q \<le> g p + \<tau>"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> f c + g c \<le> m"
    and modF: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<kappa>
        \<Longrightarrow> f p + g p \<le> f q + g q + \<tau>'"
    and gap: "m + 2*\<sigma> + \<tau> + \<tau>' < M"
    and b: "b \<in> K - interior K"
  shows "\<kappa> < dist xh b"
proof (rule ccontr)
  assume "\<not> \<kappa> < dist xh b"
  then have d: "dist xh b \<le> \<kappa>" by linarith
  have bK: "b \<in> K" using b by simp
  have g1: "g yh \<le> g xh + \<tau>" by (rule modg[OF xK yK near])
  have s1: "M \<le> f xh + g yh + 2*\<sigma>" using val tr by linarith
  have s2: "M \<le> f xh + g xh + \<tau> + 2*\<sigma>" using s1 g1 by linarith
  have s3: "f xh + g xh \<le> f b + g b + \<tau>'" by (rule modF[OF xK bK d])
  have s4: "f b + g b \<le> m" by (rule bdry[OF b])
  from s2 s3 s4 gap show False by linarith
qed

text \<open>Of the eleven lemmas in the localisation layer, only two mention the
  penalty, and neither uses anything quadratic about it:
  \<open>doubling_maximiser_value_transfer\<close> uses only \<open>Pn 0 = 0\<close>, and
  \<open>norm_lt_of_penalty_bound\<close> uses only coercivity, phrased as "the
  penalty exceeds \<open>C\<close> outside radius \<open>\<beta>\<close>".
  \<open>doubling_maximiser_far_from_boundary\<close> itself is penalty-free,
  consuming the penalty only through the abstracted \<open>tr\<close> and \<open>near\<close>.\<close>

lemma doubling_maximiser_value_transfer_gen:
  fixes A Bf f g :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + Bf y - Pn (x - y) \<le> A xh + Bf yh - Pn (xh - yh)"
    and zK: "z \<in> K"
    and P0: "Pn 0 = 0"
    and lowA: "f z \<le> A z" and lowB: "g z \<le> Bf z"
    and upA: "A xh \<le> f xh + \<sigma>" and upB: "Bf yh \<le> g yh + \<sigma>"
  shows "f z + g z + Pn (xh - yh) \<le> f xh + g yh + 2*\<sigma>"
proof -
  have diag: "A z + Bf z - Pn (z - z) \<le> A xh + Bf yh - Pn (xh - yh)"
    by (rule mx[OF zK zK])
  have zz: "z - z = (0 :: 'a)" by simp
  have "A z + Bf z \<le> A xh + Bf yh - Pn (xh - yh)"
    using diag unfolding zz P0 by simp
  then show ?thesis using lowA lowB upA upB by linarith
qed

lemma norm_lt_of_penalty_bound_gen:
  fixes d :: "'a::real_normed_vector" and Pn :: "'a \<Rightarrow> real" and C \<beta> :: real
  assumes p: "Pn d \<le> C"
    and coer: "\<And>x. \<beta> \<le> norm x \<Longrightarrow> C < Pn x"
  shows "norm d < \<beta>"
proof (rule ccontr)
  assume "\<not> norm d < \<beta>"
  then have "\<beta> \<le> norm d" by linarith
  then have "C < Pn d" by (rule coer)
  then show False using p by argo
qed

text \<open>A diagonal maximiser bounds the increment of each component above by
  the penalty only; the maximiser inequality is one-sided and says
  nothing below.\<close>

lemma diagonal_max_increments:
  fixes A B :: "'a::euclidean_space \<Rightarrow> real" and Pn :: "'a \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + B y - Pn (x - y) \<le> A p + B p - Pn (p - p)"
    and P0: "Pn 0 = 0"
    and pK: "p \<in> K"
  shows "\<And>y. y \<in> K \<Longrightarrow> B y - B p \<le> Pn (p - y)"
    and "\<And>x. x \<in> K \<Longrightarrow> A x - A p \<le> Pn (x - p)"
proof -
  have e: "p - p = (0 :: 'a)" by simp
  show "B y - B p \<le> Pn (p - y)" if y: "y \<in> K" for y
  proof -
    have "A p + B y - Pn (p - y) \<le> A p + B p - Pn 0"
      using mx[OF pK y] unfolding e .
    then show ?thesis unfolding P0 by simp
  qed
  show "A x - A p \<le> Pn (x - p)" if x: "x \<in> K" for x
  proof -
    have "A x + B p - Pn (x - p) \<le> A p + B p - Pn 0"
      using mx[OF x pK] unfolding e .
    then show ?thesis unfolding P0 by simp
  qed
qed

lemma fary_of_pin:
  fixes K K' :: "('a::euclidean_space) set" and xh yh q b :: "'a"
  assumes gap: "\<And>x c. x \<in> K \<Longrightarrow> c \<in> K' - interior K' \<Longrightarrow> d < dist x c"
    and qK: "q \<in> K" and xQ: "dist xh q \<le> dQ"
    and pin: "norm (xh - yh) < \<beta>"
    and fit: "\<beta> + dQ + \<kappa> \<le> d"
    and bK: "b \<in> K' - interior K'"
  shows "\<kappa> < dist yh b"
proof -
  have g: "d < dist q b" by (rule gap[OF qK bK])
  have t1: "dist q b \<le> dist q yh + dist yh b" by (rule dist_triangle)
  have t2: "dist q yh \<le> dist q xh + dist xh yh" by (rule dist_triangle)
  have e1: "dist xh yh = norm (xh - yh)" by (simp add: dist_norm)
  have e2: "dist q xh = dist xh q" by (rule dist_commute)
  have "dist q yh < dQ + \<beta>" using t2 pin xQ unfolding e1 e2 by linarith
  then show ?thesis using g t1 fit by linarith
qed

text \<open>the doubled-jet package produces four objects at once - the
  maximiser, the tilt, the gradient and the Hessian - so plain \<open>choice\<close>
  does not apply directly; this is the general skolemisation form,
  reusable wherever a construction is run at each index and collected
  into sequences.\<close>

lemma choice4:
  assumes "\<And>i. \<exists>a b c d. P i a b c d"
  shows "\<exists>A B C D. \<forall>i. P i (A i) (B i) (C i) (D i)"
  using assms by metis

theorem norm_matrix_le_of_form_bound:
  fixes W :: "real^'n::finite \<Rightarrow> real^'n"
  assumes lin: "linear W" and sym: "\<And>v z. v \<bullet> W z = z \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "norm (matrix W) \<le> real (card (Basis :: (real^'n^'n) set)) * c"
proof (rule norm_le_card_Basis_bound)
  fix e :: "real^'n^'n"
  assume "e \<in> Basis"
  then obtain i j where e: "e = axis i (axis j 1)"
    using matrix_Basis_cases by blast
  have nu: "norm (axis i (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have nv: "norm (axis j (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have "\<bar>(axis i 1 :: real^'n) \<bullet> W (axis j 1)\<bar> \<le> c"
    by (rule symmetric_form_bound_unit[OF lin sym bnd nu nv])
  then show "\<bar>matrix W \<bullet> e\<bar> \<le> c"
    unfolding e inner_matrix_axis[OF lin] .
qed

text \<open>From the jet to \<open>\<parallel>X\<^sub>i\<parallel> \<le> BX\<close>: testing the product-space Hessian
  \<open>W\<close> against \<open>(k,0)\<close> and \<open>(0,k)\<close> bounds the two block maps, with block
  constant \<open>C+\<bar>\<alpha>\<bar>\<close>.  No sign hypothesis on \<open>C\<close> is needed:
  \<open>-C\<parallel>k\<parallel>\<^sup>2 \<le> k \<bullet> Wk \<le> 0\<close> already forces \<open>0 \<le> C\<parallel>k\<parallel>\<^sup>2\<close>.\<close>

lemma hessian_abs_bound_of_two_sided:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
  shows "\<bar>k \<bullet> W k\<bar> \<le> C * (norm k)\<^sup>2"
proof -
  have l: "- (C * (norm k)\<^sup>2) \<le> k \<bullet> W k" by (rule lo)
  have h: "k \<bullet> W k \<le> 0" by (rule hi)
  from l h have nn: "0 \<le> C * (norm k)\<^sup>2" by linarith
  from l h nn show ?thesis by (intro abs_leI) linarith+
qed

lemma block_form_bound_fst:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)\<bar> \<le> (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((k, 0) :: ('a) \<times> ('a)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> fst (W (k, 0))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(k, 0)"] by (simp add: inner_prod_def n0)
  have eqsum: "k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)
      = k \<bullet> fst (W (k, 0)) + \<alpha> * (norm k)\<^sup>2"
    by (simp add: inner_add_right power2_norm_eq_inner)
  have aa: "\<bar>\<alpha> * (norm k)\<^sup>2\<bar> = \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    by (simp add: abs_mult)
  have "\<bar>k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)\<bar>
      \<le> \<bar>k \<bullet> fst (W (k, 0))\<bar> + \<bar>\<alpha> * (norm k)\<^sup>2\<bar>"
    unfolding eqsum by (rule abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    using b1 aa by linarith
  also have "\<dots> = (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma block_form_bound_snd:
  fixes W :: "('a::euclidean_space) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))\<bar> \<le> (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((0, k) :: ('a) \<times> ('a)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> snd (W (0, k))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(0, k)"] by (simp add: inner_prod_def n0)
  have eqsum: "k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))
      = - (k \<bullet> snd (W (0, k)) + \<alpha> * (norm k)\<^sup>2)"
    by (simp add: inner_diff_right inner_add_right
        power2_norm_eq_inner)
  have aa: "\<bar>\<alpha> * (norm k)\<^sup>2\<bar> = \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    by (simp add: abs_mult)
  have "\<bar>k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))\<bar>
      \<le> \<bar>k \<bullet> snd (W (0, k))\<bar> + \<bar>\<alpha> * (norm k)\<^sup>2\<bar>"
    unfolding eqsum by (simp add: abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    using b1 aa by linarith
  also have "\<dots> = (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem norm_block_matrices_bounded:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W" and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
  shows "norm (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    and "norm (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
proof -
  have bnd: "\<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2" for z
    by (rule hessian_abs_bound_of_two_sided[OF lo hi])
  show "norm (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_fst[OF blW] sym_block_fst[OF symW]
           block_form_bound_fst[OF bnd]])
  show "norm (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_snd[OF blW] sym_block_snd[OF symW]
           block_form_bound_snd[OF bnd]])
qed

text \<open>For a general penalty, \<open>onorm_le_matrix_component_sum\<close> bounds
  \<open>onorm ((*v) Z)\<close> by the entry sum, and Cauchy-Schwarz gives the
  quadratic form bound, replacing the quadratic version's \<open>\<bar>\<alpha>\<bar>\<close>.  The
  block bounds take the constant abstractly (\<open>KZ\<close>), so a sharper bound -
  e.g. the quartic's Hessian \<open>\<beta>((d \<bullet> d)I+2dd\<^sup>T)\<close> has norm
  \<open>O(\<beta>\<parallel>d\<parallel>\<^sup>2)\<close> - can be supplied instead.\<close>

lemma block_form_bound_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (fst (W (k, 0)) + Z *v k)\<bar> \<le> (C + KZ) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((k, 0) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> fst (W (k, 0))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(k, 0)"] by (simp add: inner_prod_def n0)
  have b2: "\<bar>k \<bullet> (Z *v k)\<bar> \<le> KZ * (norm k)\<^sup>2" by (rule bZ)
  have "\<bar>k \<bullet> (fst (W (k, 0)) + Z *v k)\<bar>
      \<le> \<bar>k \<bullet> fst (W (k, 0))\<bar> + \<bar>k \<bullet> (Z *v k)\<bar>"
    by (simp add: inner_add_right abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + KZ * (norm k)\<^sup>2"
    using b1 b2 by linarith
  also have "\<dots> = (C + KZ) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma block_form_bound_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (- (snd (W (0, k)) + Z *v k))\<bar> \<le> (C + KZ) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((0, k) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> snd (W (0, k))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(0, k)"] by (simp add: inner_prod_def n0)
  have b2: "\<bar>k \<bullet> (Z *v k)\<bar> \<le> KZ * (norm k)\<^sup>2" by (rule bZ)
  have e: "k \<bullet> (- (snd (W (0, k)) + Z *v k))
      = - (k \<bullet> snd (W (0, k))) - (k \<bullet> (Z *v k))"
    by (simp add: inner_add_right inner_diff_right)
  have "\<bar>k \<bullet> (- (snd (W (0, k)) + Z *v k))\<bar>
      \<le> \<bar>k \<bullet> snd (W (0, k))\<bar> + \<bar>k \<bullet> (Z *v k)\<bar>"
    unfolding e by simp
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + KZ * (norm k)\<^sup>2"
    using b1 b2 by linarith
  also have "\<dots> = (C + KZ) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem norm_block_matrices_bounded_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W" and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
    and lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "norm (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    and "norm (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
proof -
  have bnd: "\<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2" for z
    by (rule hessian_abs_bound_of_two_sided[OF lo hi])
  show "norm (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_fst_gen[OF blW] sym_block_fst_gen[OF symW symZ]
           block_form_bound_fst_gen[OF bnd bZ]])
  show "norm (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_snd_gen[OF blW] sym_block_snd_gen[OF symW symZ]
           block_form_bound_snd_gen[OF bnd bZ]])
qed

text \<open>The lower bound \<open>c \<le> \<parallel>G\<^sub>i\<parallel>\<close> is given by
  \<open>doubling_grad_norm_lower_bound\<close> at the doubling maximiser (the centre
  \<open>\<xi>\<close> of Jensen's ball); a triangle inequality moves it to Jensen's point
  at cost \<open>2\<bar>\<alpha>\<bar>\<rho>\<close>, uniformly in the index, so \<open>\<rho> < c/(4\<bar>\<alpha>\<bar>)\<close> keeps
  half of it.  The cost is left explicit since \<open>\<rho>\<close> is also constrained
  from the boundary side.\<close>

lemma penalty_gradient_nearby_bound:
  fixes zh \<xi> :: "('a::euclidean_space) \<times> ('a)"
  assumes c: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    and d: "dist zh \<xi> \<le> \<rho>"
  shows "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst zh - snd zh))"
proof -
  have f: "norm (fst \<xi> - fst zh) \<le> \<rho>"
  proof -
    have "norm (fst \<xi> - fst zh) = dist (fst \<xi>) (fst zh)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist \<xi> zh" by (rule dist_fst_le)
    also have "\<dots> = dist zh \<xi>" by (rule dist_commute)
    finally show ?thesis using d by linarith
  qed
  have s: "norm (snd \<xi> - snd zh) \<le> \<rho>"
  proof -
    have "norm (snd \<xi> - snd zh) = dist (snd \<xi>) (snd zh)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist \<xi> zh" by (rule dist_snd_le)
    also have "\<dots> = dist zh \<xi>" by (rule dist_commute)
    finally show ?thesis using d by linarith
  qed  have eq: "\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>) - \<alpha> *\<^sub>R (fst zh - snd zh)
      = \<alpha> *\<^sub>R ((fst \<xi> - fst zh) - (snd \<xi> - snd zh))"
    by (simp add: algebra_simps)
  have "norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) - norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>) - \<alpha> *\<^sub>R (fst zh - snd zh))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> = \<bar>\<alpha>\<bar> * norm ((fst \<xi> - fst zh) - (snd \<xi> - snd zh))"
    unfolding eq by simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (norm (fst \<xi> - fst zh) + norm (snd \<xi> - snd zh))"
    by (intro mult_left_mono norm_triangle_ineq4) simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)"
    using f s by (intro mult_left_mono) auto
  finally have "norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))
      - norm (\<alpha> *\<^sub>R (fst zh - snd zh)) \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)" .
  moreover have "\<bar>\<alpha>\<bar> * (2 * \<rho>) = 2 * \<bar>\<alpha>\<bar> * \<rho>" by simp
  ultimately show ?thesis using c by linarith
qed

text \<open>the doubled-jet package returns, at each tilt, a maximiser of the
  tilted functional together with an Alexandrov jet of the untilted one;
  this reads off the two component jets.  The tilt costs nothing to
  absorb: at an interior maximum of the tilted functional the untilted
  jet has gradient exactly \<open>-p\<close> (\<open>gradient_is_minus_tilt\<close>), so the two
  block gradients are \<open>-fst p+\<alpha>(x̂-ŷ)\<close> and \<open>-(snd p+\<alpha>(x̂-ŷ))\<close>, matching
  \<open>Pu\<close> and \<open>-Pw\<close> of the bounded-family comparison assembly with common
  penalty gradient \<open>G = \<alpha>(x̂-ŷ)\<close>.\<close>

theorem tilted_doubled_jet_slices:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
    and zh \<xi> pt q :: "('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - pt"
    and "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  show qm: "q = - pt"
    by (rule gradient_is_minus_tilt
        [where \<Psi> = "\<lambda>z. a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
           and d = "r - dist zh \<xi>" and zh = zh and p = pt and q = q and W = W,
         OF blW dpos mxT expPsi])
  have s1: "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_fst[OF expPsi])
  have s2: "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_snd[OF expPsi])
  have eqf: "(- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh))
      = fst q + \<alpha> *\<^sub>R (fst zh - snd zh)"
    using qm by simp
  have eqs: "(- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh)))
      = snd q - \<alpha> *\<^sub>R (fst zh - snd zh)"
    using qm by simp
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s1 unfolding eqf .
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s2 unfolding eqs .
qed

text \<open>The same for a general penalty: \<open>global_max_imp_interior_max\<close> and
  \<open>gradient_is_minus_tilt\<close> are already abstract in \<open>\<Psi>\<close>, so the
  conclusion is the quadratic one with \<open>\<alpha>(x̂-ŷ)\<close> replaced by \<open>G\<close> and
  \<open>\<alpha> h\<close> by \<open>Zh\<close>, carrying the penalty's jet \<open>(G,Z)\<close> along.\<close>

theorem tilted_doubled_jet_slices_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - P (fst y - snd y)) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - pt"
    and "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + G)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  show qm: "q = - pt"
    by (rule gradient_is_minus_tilt
        [where \<Psi> = "\<lambda>z. a (fst z) + b (snd z) - P (fst z - snd z)"
           and d = "r - dist zh \<xi>" and zh = zh and p = pt and q = q and W = W,
         OF blW dpos mxT expPsi])
  have s1: "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_fst_gen[OF expPsi Pjet])
  have s2: "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_snd_gen[OF expPsi Pjet])
  have eqf: "(- fst pt + G) = fst q + G"
    using qm by simp
  have eqs: "(- (snd pt + G)) = snd q - G"
    using qm by simp
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s1 unfolding eqf .
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + G)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s2 unfolding eqs .
qed

text \<open>The Hessian bound for a general penalty needs no jet of \<open>P\<close> at all,
  since \<open>second_order_interior_max\<close> concerns the full functional's
  Hessian \<open>W\<close>; a pure transcription.\<close>

theorem tilted_doubled_hessian_nonpositive_gen:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real" and P :: "'a \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
    and zh \<xi> pt q :: "('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - P (fst y - snd y)) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> W v \<le> 0"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  have eq: "(((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = ((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
    by (simp add: algebra_simps)
  have expT: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  have "(q + pt) \<bullet> v = 0 \<and> v \<bullet> W v \<le> 0"
    by (rule second_order_interior_max
        [where f = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and x = zh and q = "q + pt" and X = W and \<delta> = "r - dist zh \<xi>",
         OF blW dpos mxT expT])
  then show ?thesis by simp
qed

theorem tilted_doubled_hessian_nonpositive:
  fixes a b :: "'a::euclidean_space \<Rightarrow> real"
    and W :: "('a) \<times> ('a) \<Rightarrow> ('a) \<times> ('a)"
    and zh \<xi> pt q :: "('a) \<times> ('a)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> W v \<le> 0"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  have eq: "(((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
    by (simp add: algebra_simps)
  have expT: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  have "(q + pt) \<bullet> v = 0 \<and> v \<bullet> W v \<le> 0"
    by (rule second_order_interior_max
        [where f = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and x = zh and q = "q + pt" and X = W and \<delta> = "r - dist zh \<xi>",
         OF blW dpos mxT expT])
  then show ?thesis by simp
qed

lemma norm_Pair_le:
  fixes a :: "'a::real_normed_vector" and b :: "'b::real_normed_vector"
  shows "norm ((a, b) :: 'a \<times> 'b) \<le> norm a + norm b"
proof -
  have eq: "((a, b) :: 'a \<times> 'b) = (a, 0) + (0, b)" by simp
  have "norm ((a, b) :: 'a \<times> 'b)
      \<le> norm ((a, 0) :: 'a \<times> 'b) + norm ((0, b) :: 'a \<times> 'b)"
    unfolding eq by (rule norm_triangle_ineq)
  then show ?thesis by (simp add: norm_Pair)
qed

theorem bounded_seq_limit_point_triple:
  fixes A :: "nat \<Rightarrow> 'a::euclidean_space" and B :: "nat \<Rightarrow> 'b::euclidean_space"
    and C :: "nat \<Rightarrow> 'c::euclidean_space"
  assumes bA: "\<And>i. norm (A i) \<le> Ba" and bB: "\<And>i. norm (B i) \<le> Bb"
    and bC: "\<And>i. norm (C i) \<le> Bc"
  shows "\<exists>A0 B0 C0 rr. strict_mono rr \<and> (\<lambda>i. A (rr i)) \<longlonglongrightarrow> A0
      \<and> (\<lambda>i. B (rr i)) \<longlonglongrightarrow> B0 \<and> (\<lambda>i. C (rr i)) \<longlonglongrightarrow> C0"
proof -
  have bnd: "norm ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c) \<le> Ba + Bb + Bc" for i
  proof -
    have "norm ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c)
        \<le> norm (A i) + norm ((B i, C i) :: 'b \<times> 'c)"
      by (rule norm_Pair_le)
    moreover have "norm ((B i, C i) :: 'b \<times> 'c) \<le> norm (B i) + norm (C i)"
      by (rule norm_Pair_le)
    ultimately show ?thesis
      using bA[of i] bB[of i] bC[of i] by linarith
  qed
  obtain Z0 rr where sm: "strict_mono rr"
    and lim: "(\<lambda>i. ((A (rr i), B (rr i), C (rr i)) :: 'a \<times> 'b \<times> 'c)) \<longlonglongrightarrow> Z0"
    using bounded_seq_limit_point
      [where Z = "\<lambda>i. ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c)", OF bnd]
    by blast
  show ?thesis
  proof (intro exI conjI)
    show "strict_mono rr" by (rule sm)
    show "(\<lambda>i. A (rr i)) \<longlonglongrightarrow> fst Z0"
      using tendsto_fst[OF lim] by simp
    show "(\<lambda>i. B (rr i)) \<longlonglongrightarrow> fst (snd Z0)"
      using tendsto_fst[OF tendsto_snd[OF lim]] by simp
    show "(\<lambda>i. C (rr i)) \<longlonglongrightarrow> snd (snd Z0)"
      using tendsto_snd[OF tendsto_snd[OF lim]] by simp
  qed
qed

text \<open>The assembly's hypotheses are all data of the comparison argument - the
  two viscosity properties, the scaling \<open>\<theta>\<close>, the sup-convolution
  parameter \<open>\<epsilon>\<close>, the penalty weight \<open>\<alpha>\<close>, and Jensen's geometric data
  \<open>(\<xi>,r,\<rho>,m)\<close> - plus two smallness conditions relating them; the jets,
  Hessians and gradients are all produced.  \<open>subu\<close>/\<open>subw\<close> require the
  sup-convolutions' attaining balls in \<open>\<Omega>\<close>, a genuine smallness condition
  on \<open>\<epsilon>\<close> via the explicit \<open>O(\<surd>\<epsilon>)\<close> radius of attainment of the sup-convolution on a ball;
  \<open>rsmall\<close> requires \<open>\<rho>\<close> small compared with \<open>c/(2\<bar>\<alpha>\<bar>)\<close> so the gradient
  lower bound survives the move to Jensen's maximiser.\<close>

lemma penalty_gradient_nearby_upper:
  fixes zh \<xi> :: "('a::euclidean_space) \<times> ('a)"
  assumes d: "dist zh \<xi> \<le> \<rho>"
  shows "norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) + 2 * \<bar>\<alpha>\<bar> * \<rho>"
proof -
  have f: "norm (fst zh - fst \<xi>) \<le> \<rho>"
  proof -
    have "norm (fst zh - fst \<xi>) = dist (fst zh) (fst \<xi>)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist zh \<xi>" by (rule dist_fst_le)
    finally show ?thesis using d by linarith
  qed
  have s: "norm (snd zh - snd \<xi>) \<le> \<rho>"
  proof -
    have "norm (snd zh - snd \<xi>) = dist (snd zh) (snd \<xi>)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist zh \<xi>" by (rule dist_snd_le)
    finally show ?thesis using d by linarith
  qed
  have eq: "\<alpha> *\<^sub>R (fst zh - snd zh) - \<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)
      = \<alpha> *\<^sub>R ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))"
    by (simp add: algebra_simps)
  have "norm (\<alpha> *\<^sub>R (fst zh - snd zh)) - norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))
      \<le> norm (\<alpha> *\<^sub>R (fst zh - snd zh) - \<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> = \<bar>\<alpha>\<bar> * norm ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))"
    unfolding eq by simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (norm (fst zh - fst \<xi>) + norm (snd zh - snd \<xi>))"
    by (intro mult_left_mono norm_triangle_ineq4) simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)"
    using f s by (intro mult_left_mono) auto
  finally have "norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      - norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)" .
  moreover have "\<bar>\<alpha>\<bar> * (2 * \<rho>) = 2 * \<bar>\<alpha>\<bar> * \<rho>" by simp
  ultimately show ?thesis by linarith
qed

text \<open>The four block-matrix helpers under a general Hessian block \<open>Z\<close>: each
  is the corresponding lemma with \<open>\<alpha> *\<^sub>R v\<close> replaced by \<open>Z *v v\<close>, the
  symmetry pair additionally needing \<open>Z\<close> symmetric.\<close>

lemma block_fst_matrix_apply_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "matrix (\<lambda>v. fst (W (v, 0)) + Z *v v) *v h
       = fst (W (h, 0)) + Z *v h"
  by (rule matrix_vec_apply[OF linear_block_fst_gen[OF blW]])

lemma block_snd_matrix_apply_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "(- matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))) *v h
       = snd (W (0, h)) + Z *v h"
proof -
  have l: "linear (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
    by (rule linear_block_snd_gen[OF blW])
  have "(- matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))) *v h
      = - (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)) *v h)"
    by (rule matrix_vector_neg_left)
  also have "\<dots> = - (- (snd (W (0, h)) + Z *v h))"
    using matrix_vec_apply[OF l] by simp
  finally show ?thesis by simp
qed

lemma transpose_matrix_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "transpose (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
       = matrix (\<lambda>v. fst (W (v, 0)) + Z *v v)"
  by (rule matrix_of_symmetric[OF linear_block_fst_gen[OF blW]
        sym_block_fst_gen[OF symW symZ]])

lemma transpose_matrix_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
       = matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
  by (rule matrix_of_symmetric[OF linear_block_snd_gen[OF blW]
        sym_block_snd_gen[OF symW symZ]])

text \<open>Two locality facts about the penalty gradient for a general penalty:
  the quadratic penalty's gradient \<open>\<alpha> *\<^sub>R d\<close> is \<open>\<bar>\<alpha>\<bar>\<close>-Lipschitz; in
  general a Lipschitz bound \<open>KG\<close> on the gradient field \<open>Gf\<close> is assumed
  instead, with the displacement \<open>d\<close> moving by at most \<open>2\<rho>\<close> as in the
  quadratic case.\<close>

lemma diff_displacement_bound:
  fixes zh \<xi> :: "('a::euclidean_space) \<times> ('a)"
  assumes d: "dist zh \<xi> \<le> \<rho>"
  shows "norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>)) \<le> 2*\<rho>"
proof -
  have e: "(fst zh - snd zh) - (fst \<xi> - snd \<xi>)
      = (fst zh - fst \<xi>) - (snd zh - snd \<xi>)" by simp
  have "norm ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))
      \<le> norm (fst zh - fst \<xi>) + norm (snd zh - snd \<xi>)"
    by (rule norm_triangle_ineq4)
  moreover have "norm (fst zh - fst \<xi>) \<le> \<rho>"
    using dist_fst_le[of zh \<xi>] d by (simp add: dist_norm)
  moreover have "norm (snd zh - snd \<xi>) \<le> \<rho>"
    using dist_snd_le[of zh \<xi>] d by (simp add: dist_norm)
  ultimately show ?thesis unfolding e by linarith
qed

lemma penalty_gradient_nearby_upper_gen:
  fixes zh \<xi> :: "('a::euclidean_space) \<times> ('a)" and Gf :: "'a \<Rightarrow> 'a"
  assumes d: "dist zh \<xi> \<le> \<rho>"
    and lip: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KG: "0 \<le> KG"
  shows "norm (Gf (fst zh - snd zh)) \<le> norm (Gf (fst \<xi> - snd \<xi>)) + KG * (2*\<rho>)"
proof -
  have "norm (Gf (fst zh - snd zh)) - norm (Gf (fst \<xi> - snd \<xi>))
      \<le> norm (Gf (fst zh - snd zh) - Gf (fst \<xi> - snd \<xi>))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> \<le> KG * norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>))"
    by (rule lip)
  also have "\<dots> \<le> KG * (2*\<rho>)"
    by (rule mult_left_mono[OF diff_displacement_bound[OF d] KG])
  finally show ?thesis by linarith
qed

lemma penalty_gradient_nearby_bound_gen:
  fixes zh \<xi> :: "('a::euclidean_space) \<times> ('a)" and Gf :: "'a \<Rightarrow> 'a"
  assumes c: "c \<le> norm (Gf (fst \<xi> - snd \<xi>))"
    and d: "dist zh \<xi> \<le> \<rho>"
    and lip: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KG: "0 \<le> KG"
  shows "c - KG * (2*\<rho>) \<le> norm (Gf (fst zh - snd zh))"
proof -
  have "norm (Gf (fst \<xi> - snd \<xi>)) - norm (Gf (fst zh - snd zh))
      \<le> norm (Gf (fst \<xi> - snd \<xi>) - Gf (fst zh - snd zh))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> \<le> KG * norm ((fst \<xi> - snd \<xi>) - (fst zh - snd zh))"
    by (rule lip)
  also have "norm ((fst \<xi> - snd \<xi>) - (fst zh - snd zh))
      = norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>))"
    by (rule norm_minus_commute)
  finally have "norm (Gf (fst \<xi> - snd \<xi>)) - norm (Gf (fst zh - snd zh))
      \<le> KG * (2*\<rho>)"
    using mult_left_mono[OF diff_displacement_bound[OF d] KG] by linarith
  then show ?thesis using c by linarith
qed

text \<open>The chain above needs \<open>u\<close> and \<open>w\<close> global, bounded and continuous on all
  of \<open>'a\<close>, since the sup-convolution is a supremum over the whole
  space, while a maximum-principle interface supplies only
  \<open>continuous_on K\<close>.  Tietze's extension theorem gives a global continuous
  representative with the same sup-norm bound, and the viscosity properties
  are unaffected because they are local conditions at points of the open
  \<open>interior K\<close>.\<close>

lemma continuous_extension_bounded:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes cK: "closed K" and cu: "continuous_on K u"
    and B0: "0 \<le> B" and B: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
  shows "\<exists>v. continuous_on UNIV v \<and> (\<forall>y\<in>K. v y = u y) \<and> (\<forall>y. \<bar>v y\<bar> \<le> B)"
proof -
  have cl: "closedin (top_of_set UNIV) K"
    using cK by (simp add: closedin_closed_eq)
  have nB: "\<And>x. x \<in> K \<Longrightarrow> norm (u x) \<le> B" using B by simp
  show ?thesis
  proof (rule Tietze[OF cu cl B0 nB])
    fix g :: "'a \<Rightarrow> real"
    assume cg: "continuous_on UNIV g"
      and geq: "\<And>x. x \<in> K \<Longrightarrow> g x = u x"
      and gB: "\<And>x. x \<in> UNIV \<Longrightarrow> norm (g x) \<le> B"
    have "\<forall>y. \<bar>g y\<bar> \<le> B" using gB by simp
    then show "\<exists>v. continuous_on UNIV v \<and> (\<forall>y\<in>K. v y = u y)
        \<and> (\<forall>y. \<bar>v y\<bar> \<le> B)"
      using cg geq by blast
  qed
qed

text \<open>Packaged: from a compact \<open>K\<close> and a function continuous on it comes a
  global representative, bounded by the sup-norm on \<open>K\<close>, continuous,
  agreeing on \<open>K\<close>, and carrying the viscosity property unchanged.\<close>

lemma bounded_on_compact:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes cK: "compact K" and cu: "continuous_on K u"
  shows "\<exists>B\<ge>0. \<forall>y\<in>K. \<bar>u y\<bar> \<le> B"
proof (cases "K = {}")
  case True
  then show ?thesis by (intro exI[of _ 0]) simp
next
  case False
  have c: "continuous_on K (\<lambda>y. \<bar>u y\<bar>)"
    by (intro continuous_intros cu)
  obtain x where xK: "x \<in> K" and mx: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> \<bar>u x\<bar>"
    using continuous_attains_sup[OF cK False c] by blast
  have "0 \<le> \<bar>u x\<bar>" by simp
  then show ?thesis using mx by blast
qed

text \<open>The assembly's ball hypotheses - \<open>cball \<xi>\<^sub>0 r \<subseteq> K \<times> K\<close> for Jensen,
  \<open>cball x R\<^sub>u \<subseteq> interior K\<close> for attainment - are instances of one
  geometric fact: a point of closed \<open>K\<close> further than \<open>\<kappa>\<close> from every
  point of \<open>K - interior K\<close> has its whole \<open>\<kappa>\<close>-ball inside
  \<open>interior K\<close>, since a segment leaving \<open>K\<close> must cross
  \<open>frontier K = K - interior K\<close>.\<close>

lemma cball_subset_interior_of_far_from_boundary:
  fixes K :: "('a::euclidean_space) set"
  assumes cK: "closed K" and xK: "x \<in> K"
    and k0: "0 \<le> \<kappa>"
    and far: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist x b"
  shows "cball x \<kappa> \<subseteq> interior K"
proof
  fix y assume y: "y \<in> cball x \<kappa>"
  then have dxy: "dist x y \<le> \<kappa>" by simp
  have fr: "frontier K = K - interior K"
    using cK by (simp add: frontier_def)
  have yK: "y \<in> K"
  proof (rule ccontr)
    assume ny: "y \<notin> K"
    have conn: "connected (closed_segment x y)" by simp
    have m1: "closed_segment x y \<inter> K \<noteq> {}"
      using xK ends_in_segment(1)[of x y] by blast
    have m2: "closed_segment x y - K \<noteq> {}"
      using ny ends_in_segment(2)[of x y] by blast
    obtain b where b: "b \<in> closed_segment x y" and bf: "b \<in> frontier K"
      using connected_Int_frontier[OF conn m1 m2] by blast
    have "norm (b - x) \<le> norm (y - x)" by (rule segment_bound1[OF b])
    then have "dist x b \<le> dist x y"
      by (simp add: dist_norm norm_minus_commute)
    then have "dist x b \<le> \<kappa>" using dxy by linarith
    moreover have "\<kappa> < dist x b" using far bf fr by blast
    ultimately show False by linarith
  qed
  show "y \<in> interior K"
  proof (rule ccontr)
    assume "y \<notin> interior K"
    with yK have "y \<in> K - interior K" by simp
    then have "\<kappa> < dist x y" by (rule far)
    with dxy show False by linarith
  qed
qed

lemma cball_prod_subset_of_far_from_boundary:
  fixes K :: "('a::euclidean_space) set"
  assumes cK: "closed K" and xK: "x \<in> K" and yK: "y \<in> K"
    and k0: "0 \<le> \<kappa>"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist x b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist y b"
    and z: "dist z (x, y) \<le> \<kappa>"
  shows "fst z \<in> K \<and> snd z \<in> K"
proof -
  have d1: "dist (fst z) x \<le> \<kappa>"
    using dist_fst_le[of z "(x, y)"] z by simp
  have d2: "dist (snd z) y \<le> \<kappa>"
    using dist_snd_le[of z "(x, y)"] z by simp
  have s1: "cball x \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF cK xK k0 farx])
  have s2: "cball y \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF cK yK k0 fary])
  have "fst z \<in> cball x \<kappa>" using d1 by (simp add: dist_commute)
  then have "fst z \<in> interior K" using s1 by blast
  moreover have "snd z \<in> cball y \<kappa>" using d2 by (simp add: dist_commute)
  then have "snd z \<in> interior K" using s2 by blast
  ultimately show ?thesis using interior_subset by blast
qed

text \<open>a maximum-principle interface asserts a maximiser in \<open>K - interior K\<close>,
  which is inhabited for compact nonempty \<open>K\<close>: otherwise
  \<open>K = interior K\<close> is clopen in the connected whole space, and
  \<open>K \<noteq> UNIV\<close> since \<open>K\<close> is bounded.  With \<open>K = {}\<close> the predicate is
  unprovable, since the hypotheses hold vacuously but the conclusion
  asserts membership in the empty set; \<open>K \<noteq> {}\<close> is a genuine side
  condition.\<close>

lemma compact_frontier_nonempty:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and ne: "K \<noteq> {}"
    and dim: "0 < CARD('n)"
  shows "K - interior K \<noteq> {}"
proof -
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have fr: "frontier K = K - interior K"
    using clK by (simp add: frontier_def)
  have unb: "\<not> bounded (UNIV :: (real^'n) set)"
  proof -
    have "\<exists>x :: 'n. True" using dim by (simp add: card_gt_0_iff ex_in_conv)
    then show ?thesis by simp
  qed
  have nU: "K \<noteq> UNIV"
  proof
    assume "K = UNIV"
    then have "bounded (UNIV :: (real^'n) set)"
      using compact_imp_bounded[OF cK] by simp
    with unb show False by blast
  qed
  have "frontier K \<noteq> {}" using ne nU by (simp add: frontier_eq_empty)
  then show ?thesis unfolding fr .
qed

text \<open>The \<open>y\<close>-side avoidance is free in the two-domain setting: \<open>K\<close> sits a
  positive distance inside \<open>K'\<close>, so once the penalty pins \<open>y^h\<close> near
  \<open>K\<close> it is interior to \<open>K'\<close>.  The \<open>x\<close>-side needs no analogue, since the
  gate lemmas put \<open>x^h\<close> in \<open>\<Omega>\<close> wherever it lands.\<close>

lemma two_domain_gap:
  fixes K K' :: "('a::euclidean_space) set"
  assumes cK: "compact K" and cK': "compact K'" and sub: "K \<subseteq> interior K'"
  obtains d where "0 < d"
    and "\<And>x b. x \<in> K \<Longrightarrow> b \<in> K' - interior K' \<Longrightarrow> d < dist x b"
proof -
  have clB: "closed (K' - interior K')"
    by (intro closed_Diff compact_imp_closed[OF cK'] open_interior)
  have disj: "K \<inter> (K' - interior K') = {}" using sub by blast
  obtain d where d0: "0 < d"
    and dd: "\<And>x b. x \<in> K \<Longrightarrow> b \<in> K' - interior K' \<Longrightarrow> d \<le> dist x b"
    using separate_compact_closed[OF cK clB disj] by blast
  show ?thesis
  proof (rule that[of "d/2"])
    show "0 < d/2" using d0 by simp
    fix x b assume "x \<in> K" and "b \<in> K' - interior K'"
    from dd[OF this] show "d/2 < dist x b" using d0 by linarith
  qed
qed


(*<*)
end
(*>*)
