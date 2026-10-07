section \<open>Theorem 1.1, assembled\<close>

(*<*)
theory Theorem_1_1
  imports
    Value_Function_Uniqueness
    Exit_Class_Infinite
    Exit_Class_Marginals
begin
(*>*)

text \<open>The last theory of the session.  It states the five clauses of Theorem 1.1
  of \<^cite>\<open>LaiShkolnikovSoner\<close> for the paper's own objects --- the value
  function \<^const>\<open>xval\<close> of Eq. (1.6) over the class \<^const>\<open>xclass\<close> of
  Eq. (1.7) --- with the paper's hypotheses: existence (clauses (0)--(3)) for
  every compact \<open>K\<close>, uniqueness (clause (4)) under the additional
  expandability hypothesis.  The statement session restates the conjunction.\<close>

text \<open>The paper's value function of Eq. (1.6), over the paper's class of Eq. (1.7), is
  the internal \<^const>\<open>iexit_val\<close> on every closed \<open>K\<close>.  Everything below is
  stated for \<^const>\<open>xval\<close> itself.\<close>

lemma xval_eq_iexit_val:
  fixes K :: "(real^'n::finite) set"
  assumes "closed K" and "1 \<le> L"
  shows "xval k L K = iexit_val k L K"
  using iexit_val_eq_xval[OF assms(1)] assms(2) by (intro ext) simp

subsection \<open>The five clauses\<close>

text \<open>Clauses (0)--(3) hold for every compact \<open>K\<close>; only clause (4) needs the
  expandability hypothesis, as in the paper.\<close>

theorem xval_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
  shows "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
proof -
  obtain rK :: real where KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  show ?thesis
  proof (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
    fix y
    have "iexit_val k L K y \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      by (rule iexit_val_le_ball_bound[OF kn L1 compact_imp_closed[OF cK] KB])
    also have "\<dots> \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (intro ennreal_leI divide_right_mono) auto
    finally show "xval k L K y \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (simp add: xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1])
  qed
qed

theorem xval_usc:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
    and lt: "enn2real (xval k L K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (xval k L K y) < c"
  using iexit_val_real_usc[OF kn L1 cK] lt
  by (simp add: xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1])

theorem xval_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
  shows "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (xval k L K x)})
      (\<lambda>z. enn2real (xval k L K z))"
  unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
  by (rule visc_subsol_env_imp_env2[OF iexit_val_subsol_bc[OF kn L1 cK]])

theorem xval_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  shows "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (xval k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (xval k L K z)))"
  unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
  by (rule visc_supersol_env_imp_env2[OF iexit_val_supersol_bc_K[OF kn L1 k1 cK]])

theorem xval_unique:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and expK: "expandable K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
           \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sup: "visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
           (lsc_envK K u)"
    and x: "x \<in> K"
  shows "u x = enn2real (xval k L K x)"
proof -
  have neK: "K \<noteq> {}" using x by blast
  show ?thesis
    unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
    by (rule iexit_val_uniqueness_K[OF kn L1 k1 cK neK expK usc bd sub sup x])
qed

subsection \<open>Theorem 1.1 as one formula\<close>

theorem theorem_1_1_assembled:
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
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x)))"
proof (intro conjI impI allI ballI)
  show "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
    by (rule xval_bounded[OF kn L1 cK])
next
  fix c z assume "v z < c"
  then show "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c"
    unfolding v_def by (rule xval_usc[OF kn L1 cK])
next
  show "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def by (rule xval_subsolution[OF kn L1 cK])
next
  show "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding v_def by (rule xval_supersolution[OF kn L1 k1 cK])
next
  fix u :: "real^'n \<Rightarrow> real" and Bd x
  assume expK: "expandable K"
    and usc: "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
    and bd: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and x: "x \<in> K"
  show "u x = v x"
    unfolding v_def
    by (rule xval_unique[OF kn L1 k1 cK expK _ _ sub sup x])
       (use usc bd in blast)+
qed

subsection \<open>Example 3.1\<close>

theorem example_3_1_xval:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L" and r0: "0 < r"
  shows "enn2real (xval k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  unfolding xval_eq_iexit_val[OF closed_cball L1]
  by (rule example_3_1_uncapped[OF k1 kn L1 r0])

(*<*)
end
(*>*)
