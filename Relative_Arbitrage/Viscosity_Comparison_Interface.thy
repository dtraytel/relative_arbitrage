
(*<*)
theory Viscosity_Comparison_Interface
  imports Constraint_Set_Convexity
begin

(*>*)

text \<open>
  The uniqueness side of Theorem 1.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>
             (Lai/Shkolnikov/Soner), and the structural pieces of Lemma 3.1.

    Proved outright:
    \<^item> gradient-scaling invariance of F: the feasible set of Eq. (1.9), hence
      F itself, depends on the gradient argument p only through its kernel
      constraint, so F(c p, M) = F(p, M) for c \<open>\<noteq>\<close> 0 (part of Lemma 3.1's
      analysis of the p-dependence);
    \<^item> orthogonal equivariance and the dilation identity
          \<open>F(p, M) = c\<^sup>2 F(Q\<^sup>T p, c\<^sup>-\<^sup>2 Q\<^sup>T M Q)          (c \<noteq> 0, Q orthogonal)\<close>
      \<open>used to conjugate the PDE under the transformations T\<^sub>\<iota> of the\<close>
      uniqueness hypothesis of Theorem 1.1;
    \<^item> given a comparison principle, uniqueness of viscosity solutions with
      prescribed boundary values (the way Theorem 1.1's uniqueness statement
      follows from comparison).

    Axiomatized (as the locale assumption of \<open>comparison_principle\<close>):
    the comparison half itself.  Its proof in the paper runs through the
    Crandall--Ishii lemma (doubling of variables with quartic penalty and
    second-order jets), a deep result of viscosity theory with no Isabelle
    formalization, and is taken here as an interface assumption.\<close>
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

text \<open>Conjugation preserves each defining condition of the feasible set.
  Orthogonality is HOL-Analysis's own \<open>orthogonal_matrix\<close>.\<close>

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

text \<open>Eq. (1.10) of Remark 1.1(b): the nonlinearity \<open>F\<close> is geometric.\<close>

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

(*<*)
end
(*>*)
