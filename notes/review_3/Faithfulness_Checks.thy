(* Checked in PIDE on 2026-10-07 against the Relative_Arbitrage_Statement heap (0 errors,
   0 sorries).  Not part of any session: these are the proposed additions of
   notes/PLAN_RESTRUCTURING_3.md, phase 1 (statement and faithfulness evidence). *)
theory Faithfulness_Checks
  imports "Relative_Arbitrage_Statement.Paper_Readings"
begin

section \<open>Theorem 1.1 with the paper's hypotheses: existence for every compact K\<close>

theorem theorem_1_1_strong:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "(\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B)
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
       \<and> visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)
       \<and> (expandable K \<longrightarrow>
          (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x)))"
proof -
  have xeq: "\<And>z. xval k L K z = iexit_val k L K z"
    using iexit_val_eq_xval[OF compact_imp_closed[OF cK]] L1 by simp
  have veq: "v = (\<lambda>z. enn2real (iexit_val k L K z))"
    unfolding v_def by (simp add: xeq)
  obtain rK :: real where KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  have bnd: "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
  proof (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
    fix y
    have "iexit_val k L K y \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      by (rule clause_0_finite[OF kn L1 cK KB])
    also have "\<dots> \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (intro ennreal_leI divide_right_mono) auto
    finally show "xval k L K y \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (simp add: xeq)
  qed
  have usc: "\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c)"
    unfolding veq by (intro allI impI clause_1_upper_semicontinuous[OF kn L1 cK])
  have sub: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding veq
    by (rule visc_subsol_env_imp_env2[OF clause_3_boundary_subsolution[OF kn L1 cK]])
  have sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding veq
    by (rule visc_supersol_env_imp_env2[OF clause_3_boundary_supersolution[OF kn L1 k1 cK]])
  have uniq: "\<forall>x\<in>K. u x = v x"
    if expK: "expandable K"
      and h1: "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
      and h2: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
      and h3: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
      and h4: "visc_supersol_env2 k L K
             (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    for u :: "real^'n \<Rightarrow> real" and Bd
  proof (cases "K = {}")
    case True then show ?thesis by simp
  next
    case False
    show ?thesis unfolding veq
      using h1 h2 h3 h4 by (intro ballI clause_4_uniqueness[OF kn L1 k1 cK False expK]) blast+
  qed
  from bnd usc sub sup uniq show ?thesis by blast
qed

section \<open>F reads only the symmetric part of M\<close>

lemma trace_transpose_eq:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "trace (transpose A) = trace A"
  by (simp add: trace_def transpose_def)

lemma trace_transpose_mult_sym:
  fixes M a :: "real^'n::finite^'n"
  assumes "transpose a = a"
  shows "trace (transpose M ** a) = trace (M ** a)"
proof -
  have "trace (transpose M ** a) = trace (transpose (transpose a ** M))"
    by (simp add: matrix_transpose_mul)
  also have "\<dots> = trace (transpose a ** M)" by (simp only: trace_transpose_eq)
  also have "\<dots> = trace (M ** a)" using assms trace_mul_sym[of a M] by simp
  finally show ?thesis .
qed

theorem ell_op_sym_part:
  fixes M :: "real^'n::finite^'n"
  shows "ell_op k L p M = ell_op k L p ((1/2) *\<^sub>R (M + transpose M))"
proof -
  have "- trace (M ** a) / 2 = - trace (((1/2) *\<^sub>R (M + transpose M)) ** a) / 2"
    if "a \<in> feasible k L p" for a
  proof -
    have sym: "transpose a = a" using that by (simp add: feasible_def psd_def)
    show ?thesis
      by (simp add: scaleR_matrix_mult matrix_add_rdistrib trace_add trace_scaleR
            trace_transpose_mult_sym[OF sym])
  qed
  then show ?thesis unfolding ell_op_def by (intro arg_cong[where f = Inf] image_cong) auto
qed

text \<open>So the envelopes taken over all matrices agree with those over symmetric
  matrices, as Theorem_1_1_Statement asserts in prose.\<close>
section \<open>The literal (non-orthogonal) reading of Pi_m does not make S empty\<close>

definition Pi_lit_set :: "real^'n::finite^'n \<Rightarrow> nat \<Rightarrow> real set" where
  "Pi_lit_set a m = {trace (a ** P) | P. P ** P = P \<and> trace P = real m}"

theorem literal_reading_keeps_identity:
  "\<forall>m. k < m \<longrightarrow> m \<le> CARD('n::finite) \<longrightarrow>
      (\<forall>t \<in> Pi_lit_set (mat 1 :: real^'n^'n) m. real (m - k) \<le> t)"
  by (auto simp: Pi_lit_set_def of_nat_diff)

end
