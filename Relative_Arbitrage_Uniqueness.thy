(*
  Title:   Relative_Arbitrage_Uniqueness.thy
  Content: The uniqueness side of Theorem 1.1 of arXiv:2512.17702
           (Lai/Shkolnikov/Soner), and the structural pieces of Lemma 3.1.

  Proved outright:
  \<^item> gradient-scaling invariance of F: the feasible set of Eq. (1.9), hence
    F itself, depends on the gradient argument p only through its kernel
    constraint, so F(c p, M) = F(p, M) for c \<noteq> 0 (part of Lemma 3.1's
    analysis of the p-dependence);
  \<^item> orthogonal equivariance and the dilation identity
        F(p, M) = c\<^sup>2 F(Q\<^sup>T p, c\<^sup>-\<^sup>2 Q\<^sup>T M Q)          (c \<noteq> 0, Q orthogonal)
    used to conjugate the PDE under the transformations T\<^sub>\<iota> of the
    uniqueness hypothesis of Theorem 1.1;
  \<^item> given a comparison principle, uniqueness of viscosity solutions with
    prescribed boundary values (the way Theorem 1.1's uniqueness statement
    follows from comparison).

  Axiomatized (as the locale assumption of comparison_principle):
  the comparison half itself.  Its proof in the paper runs through the
  Crandall--Ishii lemma (doubling of variables with quartic penalty and
  second-order jets), a deep result of viscosity theory with no Isabelle
  formalization, and is taken here as an interface assumption.
*)

theory Relative_Arbitrage_Uniqueness
  imports Relative_Arbitrage_Convexity
begin

unbundle inner_syntax

text \<open>Keep matrix-vector products in \<open>*v\<close>-form: the default normalization
  to the vector-matrix form \<open>x v* A\<close> would obstruct the conjugation
  rewrites below.\<close>

declare transpose_matrix_vector [simp del]

section \<open>Lemma 3.1, structural part: dependence of \<open>F\<close> on the gradient\<close>

text \<open>The feasible set of Eq. (1.9) sees \<open>p\<close> only through the linear
  constraint \<open>a p = 0\<close>, hence only through the line spanned by \<open>p\<close>.\<close>

lemma feasible_scale_p:
  fixes p :: "real^'n"
  assumes c: "c \<noteq> 0"
  shows "feasible k L (c *\<^sub>R p) = feasible k L p"
proof -
  have "a *v (c *\<^sub>R p) = 0 \<longleftrightarrow> a *v p = 0" for a :: "real^'n^'n"
  proof
    assume "a *v (c *\<^sub>R p) = 0"
    then have "c *\<^sub>R (a *v p) = 0"
      by (simp add: matrix_vector_mult_scaleR)
    with c show "a *v p = 0"
      by simp
  next
    assume "a *v p = 0"
    then show "a *v (c *\<^sub>R p) = 0"
      by (simp add: matrix_vector_mult_scaleR)
  qed
  then show ?thesis
    by (simp add: feasible_def)
qed

theorem ell_op_scale_p:
  fixes p :: "real^'n"
  assumes c: "c \<noteq> 0"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
  by (simp add: ell_op_def feasible_scale_p[OF c])

section \<open>Orthogonal equivariance and the dilation identity\<close>

text \<open>Orthogonal conjugation \<open>a \<mapsto> Q\<^sup>T a Q\<close> maps the feasible set for \<open>p\<close>
  bijectively onto the feasible set for \<open>Q\<^sup>T p\<close>, and traces are invariant;
  dilating the Hessian rescales the infimum.  Together these give the
  identity \<open>F(p, M) = c\<^sup>2 F(Q\<^sup>T p, c\<^sup>-\<^sup>2 Q\<^sup>T M Q)\<close> behind the
  transformation hypothesis of Theorem 1.1.\<close>

definition orth_mat :: "real^'n^'n \<Rightarrow> bool" where
  "orth_mat Q \<longleftrightarrow> transpose Q ** Q = mat 1 \<and> Q ** transpose Q = mat 1"

lemma orth_mat_inner:
  assumes "orth_mat Q"
  shows "(Q *v x) \<bullet> (Q *v y) = x \<bullet> y"
proof -
  have "(Q *v x) \<bullet> (Q *v y) = (transpose Q *v (Q *v x)) \<bullet> y"
    by (simp add: inner_transpose_matrix)
  also have "transpose Q *v (Q *v x) = (transpose Q ** Q) *v x"
    by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = x"
    using assms by (simp add: orth_mat_def)
  finally show ?thesis .
qed

lemma orth_mat_surj:
  assumes "orth_mat Q"
  shows "Q *v (transpose Q *v x) = x"
  using assms
  by (simp add: matrix_vector_mul_assoc orth_mat_def)

lemma orth_mat_transpose:
  assumes "orth_mat Q"
  shows "orth_mat (transpose Q)"
  using assms by (simp add: orth_mat_def)

text \<open>Conjugation preserves each defining condition of the feasible set.\<close>

lemma psd_conjugate:
  assumes a: "psd a" and Q: "orth_mat Q"
  shows "psd (transpose Q ** a ** Q)"
proof -
  have sym: "transpose a = a"
    using a by (simp add: psd_def)
  have "transpose (transpose Q ** a ** Q)
      = transpose Q ** transpose a ** transpose (transpose Q)"
    by (simp add: matrix_transpose_mul matrix_mul_assoc)
  also have "\<dots> = transpose Q ** a ** Q"
    by (simp add: sym)
  finally have symc: "transpose (transpose Q ** a ** Q)
      = transpose Q ** a ** Q" .
  have quad: "0 \<le> x \<bullet> ((transpose Q ** a ** Q) *v x)" for x
  proof -
    have "x \<bullet> ((transpose Q ** a ** Q) *v x)
        = x \<bullet> (transpose Q *v (a *v (Q *v x)))"
      by (simp add: matrix_vector_mul_assoc[symmetric] matrix_mul_assoc)
    also have "\<dots> = (Q *v x) \<bullet> (a *v (Q *v x))"
      by (simp add: inner_transpose_matrix)
    also have "\<dots> \<ge> 0"
      using a by (simp add: psd_def)
    finally show ?thesis .
  qed
  show ?thesis
    using symc quad by (simp add: psd_def)
qed

lemma eigen_lb_conjugate:
  assumes lb: "eigen_lb a m" and Q: "orth_mat Q"
  shows "eigen_lb (transpose Q ** a ** Q) m"
proof -
  obtain S where S: "subspace S" "m \<le> dim S"
    "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    using lb by (auto simp: eigen_lb_def)
  define S' where "S' = (\<lambda>x. transpose Q *v x) ` S"
  have subS': "subspace S'"
    unfolding S'_def
    by (intro linear_subspace_image S(1) matrix_vector_mul_linear)
  have dimS': "dim S' = dim S"
  proof -
    have inj: "inj_on ((*v) (transpose Q)) (span S)"
    proof (rule inj_onI)
      fix x y assume "transpose Q *v x = transpose Q *v y"
      then have "Q *v (transpose Q *v x) = Q *v (transpose Q *v y)"
        by simp
      then show "x = y"
        by (simp add: orth_mat_surj[OF Q])
    qed
    show ?thesis
      unfolding S'_def
      by (intro dim_image_eq[of _ S] matrix_vector_mul_linear inj)
  qed
  have ray: "x \<bullet> x \<le> x \<bullet> ((transpose Q ** a ** Q) *v x)" if x: "x \<in> S'" for x
  proof -
    from x obtain y where y: "y \<in> S" "x = transpose Q *v y"
      by (auto simp: S'_def)
    have Ox: "Q *v x = y"
      by (simp add: y orth_mat_surj[OF Q])
    have "x \<bullet> ((transpose Q ** a ** Q) *v x)
        = x \<bullet> (transpose Q *v (a *v (Q *v x)))"
      by (simp add: matrix_vector_mul_assoc[symmetric] matrix_mul_assoc)
    also have "\<dots> = (Q *v x) \<bullet> (a *v (Q *v x))"
      by (simp add: inner_transpose_matrix)
    also have "\<dots> = y \<bullet> (a *v y)"
      by (simp add: Ox)
    also have "\<dots> \<ge> y \<bullet> y"
      by (rule S(3)[OF y(1)])
    also have "y \<bullet> y = x \<bullet> x"
      using orth_mat_inner[OF orth_mat_transpose[OF Q], of y y]
      by (simp add: y)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding eigen_lb_def
    using subS' dimS' S(2) ray by (intro exI[of _ S']) auto
qed

lemma eigen_ub_conjugate:
  assumes ub: "eigen_ub a L" and Q: "orth_mat Q"
  shows "eigen_ub (transpose Q ** a ** Q) L"
proof -
  have "x \<bullet> ((transpose Q ** a ** Q) *v x) \<le> L * (x \<bullet> x)" for x
  proof -
    have "x \<bullet> ((transpose Q ** a ** Q) *v x)
        = (Q *v x) \<bullet> (a *v (Q *v x))"
      by (simp add: matrix_vector_mul_assoc[symmetric] matrix_mul_assoc
          inner_transpose_matrix)
    also have "\<dots> \<le> L * ((Q *v x) \<bullet> (Q *v x))"
      using ub by (simp add: eigen_ub_def)
    also have "(Q *v x) \<bullet> (Q *v x) = x \<bullet> x"
      by (rule orth_mat_inner[OF Q])
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: eigen_ub_def)
qed

lemma kernel_conjugate:
  assumes Q: "orth_mat Q"
  shows "(transpose Q ** a ** Q) *v (transpose Q *v p) = 0 \<longleftrightarrow> a *v p = 0"
proof -
  have "(transpose Q ** a ** Q) *v (transpose Q *v p)
      = transpose Q *v (a *v (Q *v (transpose Q *v p)))"
    by (simp add: matrix_vector_mul_assoc[symmetric] matrix_mul_assoc)
  also have "Q *v (transpose Q *v p) = p"
    by (rule orth_mat_surj[OF Q])
  finally have eq: "(transpose Q ** a ** Q) *v (transpose Q *v p)
      = transpose Q *v (a *v p)" .
  show ?thesis
  proof
    assume "(transpose Q ** a ** Q) *v (transpose Q *v p) = 0"
    then have "transpose Q *v (a *v p) = 0"
      by (simp add: eq)
    then have "Q *v (transpose Q *v (a *v p)) = 0"
      by simp
    then show "a *v p = 0"
      by (simp add: orth_mat_surj[OF Q])
  next
    assume "a *v p = 0"
    then show "(transpose Q ** a ** Q) *v (transpose Q *v p) = 0"
      by (simp add: eq)
  qed
qed

lemma feasible_conjugate:
  fixes p :: "real^'n"
  assumes Q: "orth_mat Q"
  shows "(\<lambda>a. transpose Q ** a ** Q) ` feasible k L p
       = feasible k L (transpose Q *v p)"
proof
  show "(\<lambda>a. transpose Q ** a ** Q) ` feasible k L p
      \<subseteq> feasible k L (transpose Q *v p)"
    using psd_conjugate[OF _ Q] eigen_lb_conjugate[OF _ Q]
      eigen_ub_conjugate[OF _ Q] kernel_conjugate[OF Q]
    by (auto simp: feasible_def)
next
  show "feasible k L (transpose Q *v p)
      \<subseteq> (\<lambda>a. transpose Q ** a ** Q) ` feasible k L p"
  proof
    fix b assume b: "b \<in> feasible k L (transpose Q *v p)"
    have OT: "orth_mat (transpose Q)"
      by (rule orth_mat_transpose[OF Q])
    define a where "a = Q ** b ** transpose Q"
    have ab: "transpose Q ** a ** Q = b"
    proof -
      have "transpose Q ** a ** Q = (transpose Q ** Q) ** b ** (transpose Q ** Q)"
        by (simp add: a_def matrix_mul_assoc)
      also have "\<dots> = b"
        using Q by (simp add: orth_mat_def)
      finally show ?thesis .
    qed
    have a_std: "a = transpose (transpose Q) ** b ** transpose Q"
      by (simp add: a_def)
    have "a \<in> feasible k L p"
    proof -
      have psd_a: "psd a"
        using b psd_conjugate[OF _ OT]
        by (auto simp: feasible_def a_std)
      have lb_a: "eigen_lb a (CARD('n) - k)"
        using b eigen_lb_conjugate[OF _ OT]
        by (auto simp: feasible_def a_std)
      have ub_a: "eigen_ub a L"
        using b eigen_ub_conjugate[OF _ OT]
        by (auto simp: feasible_def a_std)
      have ker: "a *v p = 0"
      proof -
        have "a *v (transpose (transpose Q) *v (transpose Q *v p)) = 0
            \<longleftrightarrow> b *v (transpose Q *v p) = 0"
          using kernel_conjugate[OF OT, of b "transpose Q *v p"]
          by (simp add: a_std)
        moreover have "transpose (transpose Q) *v (transpose Q *v p) = p"
          using orth_mat_surj[OF Q] by simp
        moreover have "b *v (transpose Q *v p) = 0"
          using b by (simp add: feasible_def)
        ultimately show ?thesis
          by simp
      qed
      show ?thesis
        using psd_a lb_a ub_a ker by (simp add: feasible_def)
    qed
    then show "b \<in> (\<lambda>a. transpose Q ** a ** Q) ` feasible k L p"
      using ab by (metis imageI)
  qed
qed

lemma trace_conjugate:
  fixes M Q a :: "real^'n^'n"
  shows "trace (M ** (transpose Q ** a ** Q)) = trace ((Q ** M ** transpose Q) ** a)"
proof -
  have "trace (M ** (transpose Q ** a ** Q))
      = trace ((M ** transpose Q ** a) ** Q)"
    by (simp add: matrix_mul_assoc)
  also have "\<dots> = trace (Q ** (M ** transpose Q ** a))"
    using trace_mul_sym[of "M ** transpose Q ** a" Q] by simp
  also have "\<dots> = trace ((Q ** M ** transpose Q) ** a)"
    by (simp add: matrix_mul_assoc)
  finally show ?thesis .
qed

theorem ell_op_orth_equivariant:
  fixes p :: "real^'n" and M Q :: "real^'n^'n"
  assumes Q: "orth_mat Q"
  shows "ell_op k L (transpose Q *v p) (transpose Q ** M ** Q)
       = ell_op k L p M"
proof -
  have img: "(\<lambda>a. - trace ((transpose Q ** M ** Q) ** a) / 2)
        ` feasible k L (transpose Q *v p)
      = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  proof -
    have "(\<lambda>a. - trace ((transpose Q ** M ** Q) ** a) / 2)
          ` feasible k L (transpose Q *v p)
        = (\<lambda>a. - trace ((transpose Q ** M ** Q) ** a) / 2)
          ` (\<lambda>a. transpose Q ** a ** Q) ` feasible k L p"
      by (simp add: feasible_conjugate[OF Q])
    also have "\<dots> = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    proof (rule image_image[THEN trans])
      have "- trace ((transpose Q ** M ** Q) ** (transpose Q ** a ** Q)) / 2
          = - trace (M ** a) / 2" for a
      proof -
        have "trace ((transpose Q ** M ** Q) ** (transpose Q ** a ** Q))
            = trace ((Q ** (transpose Q ** M ** Q) ** transpose Q) ** a)"
          by (rule trace_conjugate)
        also have "Q ** (transpose Q ** M ** Q) ** transpose Q
            = (Q ** transpose Q) ** M ** (Q ** transpose Q)"
          by (simp add: matrix_mul_assoc)
        also have "\<dots> = M"
          using Q by (simp add: orth_mat_def)
        finally show ?thesis
          by simp
      qed
      then show "(\<lambda>x. - trace ((transpose Q ** M ** Q) ** (transpose Q ** x ** Q)) / 2)
          ` feasible k L p = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
        by (intro image_cong refl)
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding ell_op_def
    by (rule arg_cong[OF img])
qed

text \<open>The dilation identity: scaling the Hessian argument scales \<open>F\<close>.\<close>

theorem ell_op_dilation:
  fixes p :: "real^'n" and M :: "real^'n^'n"
  assumes c: "0 < c" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p (c *\<^sub>R M) = c * ell_op k L p M"
proof -
  define A where "A = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  have A_ne: "A \<noteq> {}"
    using ne by (simp add: A_def)
  have A_bdd: "bdd_below A"
    unfolding A_def by (rule ell_op_bdd_below)
  have img: "(\<lambda>a. - trace ((c *\<^sub>R M) ** a) / 2) ` feasible k L p
      = (\<lambda>x. c * x) ` A"
    by (auto simp: A_def image_image scaleR_matrix_mult trace_scaleR)
  have inf_scale: "Inf ((\<lambda>x. c * x) ` A) = c * Inf A"
  proof (rule antisym)
    show "c * Inf A \<le> Inf ((\<lambda>x. c * x) ` A)"
    proof (rule cInf_greatest)
      show "(\<lambda>x. c * x) ` A \<noteq> {}"
        using A_ne by simp
      fix y assume "y \<in> (\<lambda>x. c * x) ` A"
      then obtain x where x: "x \<in> A" "y = c * x"
        by auto
      have "Inf A \<le> x"
        by (rule cInf_lower[OF x(1) A_bdd])
      then show "c * Inf A \<le> y"
        using c x(2) by (simp add: mult_left_mono less_imp_le)
    qed
    have bdd_img: "bdd_below ((\<lambda>x. c * x) ` A)"
    proof -
      obtain b where b: "\<And>x. x \<in> A \<Longrightarrow> b \<le> x"
        using A_bdd by (auto simp: bdd_below_def)
      show ?thesis
        by (rule bdd_belowI[of _ "c * b"])
          (use b c in \<open>auto simp: mult_left_mono less_imp_le\<close>)
    qed
    have le_all: "Inf ((\<lambda>x. c * x) ` A) / c \<le> x" if x: "x \<in> A" for x
    proof -
      have "Inf ((\<lambda>x. c * x) ` A) \<le> c * x"
        by (intro cInf_lower imageI x bdd_img)
      with c show ?thesis
        by (simp add: pos_divide_le_eq mult_ac)
    qed
    have "Inf ((\<lambda>x. c * x) ` A) / c \<le> Inf A"
      by (rule cInf_greatest[OF A_ne le_all])
    with c show "Inf ((\<lambda>x. c * x) ` A) \<le> c * Inf A"
      by (simp add: pos_divide_le_eq mult_ac)
  qed
  show ?thesis
    unfolding ell_op_def img A_def[symmetric]
    by (rule inf_scale)
qed

text \<open>The remaining ingredient of Eq. (1.10): every feasible \<open>a\<close> annihilates
  \<open>p\<close>, so \<open>tr(p p\<^sup>\<top> a) = p \<bullet> (a p) = 0\<close> and adding a multiple of \<open>p p\<^sup>\<top>\<close> to the
  Hessian argument leaves the objective --- hence \<open>F\<close> --- unchanged.\<close>

lemma trace_outer_prod_feasible:
  fixes p :: "real^'n"
  assumes a: "a \<in> feasible k L p"
  shows "trace (outer_prod p p ** a) = 0"
proof -
  have ap: "a *v p = 0"
    using a by (simp add: feasible_def)
  have "trace (outer_prod p p ** a) = trace (a ** outer_prod p p)"
    by (rule trace_mul_sym)
  also have "\<dots> = trace (outer_prod (a *v p) p)"
    by (simp add: mult_outer_prod)
  also have "\<dots> = 0"
    by (simp add: ap)
  finally show ?thesis .
qed

lemma ell_op_add_outer:
  fixes p :: "real^'n" and M :: "real^'n^'n"
  shows "ell_op k L p (M + c *\<^sub>R outer_prod p p) = ell_op k L p M"
proof -
  have "(\<lambda>a. - trace ((M + c *\<^sub>R outer_prod p p) ** a) / 2) ` feasible k L p
      = (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  proof (rule image_cong[OF refl])
    fix a :: "real^'n^'n" assume a: "a \<in> feasible k L p"
    have "trace ((M + c *\<^sub>R outer_prod p p) ** a)
        = trace (M ** a) + c * trace (outer_prod p p ** a)"
      by (simp add: matrix_add_rdistrib scaleR_matrix_mult trace_add trace_scaleR)
    then show "- trace ((M + c *\<^sub>R outer_prod p p) ** a) / 2
        = - trace (M ** a) / 2"
      by (simp add: trace_outer_prod_feasible[OF a])
  qed
  then show ?thesis
    by (simp add: ell_op_def)
qed

text \<open>Eq. (1.10) of Remark 1.1(b): the nonlinearity \<open>F\<close> is geometric.\<close>

theorem ell_op_geometric:
  fixes p :: "real^'n" and M :: "real^'n^'n"
  assumes c1: "0 < c1" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L (c1 *\<^sub>R p) (c1 *\<^sub>R M + c2 *\<^sub>R outer_prod p p)
       = c1 * ell_op k L p M"
proof -
  have "ell_op k L (c1 *\<^sub>R p) (c1 *\<^sub>R M + c2 *\<^sub>R outer_prod p p)
      = ell_op k L p (c1 *\<^sub>R M + c2 *\<^sub>R outer_prod p p)"
    using c1 by (intro ell_op_scale_p) simp
  also have "\<dots> = ell_op k L p (c1 *\<^sub>R M)"
    by (rule ell_op_add_outer)
  also have "\<dots> = c1 * ell_op k L p M"
    by (rule ell_op_dilation[OF c1 ne])
  finally show ?thesis .
qed

section \<open>Comparison implies uniqueness (Theorem 1.1, uniqueness part)\<close>

text \<open>The comparison principle is the content of the Crandall--Ishii
  doubling argument in the paper's proof of Theorem 1.1, valid under the
  hypothesis that \<open>K\<close> admits the expanding similarity transformations
  \<open>T\<^sub>\<iota>\<close>.  It is axiomatized here as the locale assumption; everything
  after it is proved.\<close>

locale comparison_principle =
  fixes k :: nat and L :: real and \<Omega> :: "(real^'n::finite) set"
  assumes comparison:
    "\<And>u w x. visc_subsol k L \<Omega> u \<Longrightarrow> visc_supersol k L \<Omega> w \<Longrightarrow>
       (\<forall>y \<in> closure \<Omega> - \<Omega>. u y \<le> w y) \<Longrightarrow> x \<in> \<Omega> \<Longrightarrow> u x \<le> w x"
begin

theorem viscosity_solution_unique:
  assumes u: "visc_sol k L \<Omega> u" and w: "visc_sol k L \<Omega> w"
    and bd: "\<And>x. x \<in> closure \<Omega> - \<Omega> \<Longrightarrow> u x = w x"
  shows "\<And>x. x \<in> \<Omega> \<Longrightarrow> u x = w x"
proof -
  fix x assume x: "x \<in> \<Omega>"
  have le1: "u x \<le> w x"
    using u w bd x
    by (intro comparison[of u w x]) (auto simp: visc_sol_def)
  have le2: "w x \<le> u x"
    using u w bd x
    by (intro comparison[of w u x]) (auto simp: visc_sol_def)
  from le1 le2 show "u x = w x"
    by simp
qed

end

text \<open>On the open ball, the explicit function of Eq. (3.9) is the unique
  viscosity solution with its boundary data: any other viscosity solution
  agreeing with it near the boundary coincides with it (Theorem 1.1,
  uniqueness, for Example 3.1).\<close>

theorem ball_v_unique_solution:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
    and cp: "comparison_principle k L (ball (0::real^'n) r)"
    and u: "visc_sol k L (ball 0 r) (u :: real^'n \<Rightarrow> real)"
    and bd: "\<And>x :: real^'n. x \<in> closure (ball 0 r) - ball 0 r
              \<Longrightarrow> u x = ball_v r k x"
  shows "\<And>x :: real^'n. x \<in> ball 0 r \<Longrightarrow> u x = ball_v r k x"
  by (rule comparison_principle.viscosity_solution_unique[OF cp u _ bd])
    (use ball_v_solves_pde_viscosity(1)[OF k L] in auto)

end
