section \<open>Clause (2): the value function is a viscosity solution\<close>

(*<*)
theory Value_Function_Assembly
  imports
    Value_Function_Supersolution_Case_2
begin

(*>*)

section \<open>Clause (2): the value function is a viscosity solution\<close>

text \<open>\<open>enn2real \<circ> exit_val k L T K\<close> is a viscosity solution of Eq. (1.9) on
  \<open>interior K\<close>: an ordinary subsolution (@{thm [source] exit_val_visc_subsol_any})
  and, in the enveloped sense of Definition 3.1(b), a supersolution
  (@{thm [source] exit_val_supersol_lsc}), where the lower semicontinuous
  envelope replaces \<open>v\<close> because the plain supersolution property fails
  wherever \<open>v\<close> has an interior local minimum.  Both proofs are pathwise,
  built by Euler pasting of endpoint-frozen Gaussian kernels rather than
  stochastic integrals or SDE well-posedness.  The supersolution assumes
  the horizon does not bind on the interior, \<open>v\<^sub>*(x) < T/2\<close>, which for a
  bounded \<open>K\<close> holds automatically once \<open>T\<close> is large enough
  (@{thm [source] covariation_val_le_ball_bound}).\<close>

subsection \<open>The sharp ball lower bound at rate \<open>m - 1\<close>\<close>

text \<open>For any closed convex \<open>S\<close> with bounds \<open>B\<close>, \<open>D\<close> that contains the
  tangential rates of the subspace \<open>span (b ` {..<m})\<close>, the value at a point
  of that subspace is at least the deterministic time the tangential member
  needs to reach the sphere.  The paper's set contains them for
  \<open>m \<ge> n - k + 1\<close> (@{thm [source] tanpU_sq_sconstraint}).\<close>

theorem covariation_val_ball_lower_subspace:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T cc :: real
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and tan: "\<And>u. norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
    and cc0: "0 < cc" and ccT: "cc < T"
    and ccdf: "cc < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  shows "ennreal cc \<le> covariation_val S T K x"
proof -
  have "ennreal (cc + min 0 (T - cc)) \<le> covariation_val S T K x"
    by (rule covariation_val_ball_lower_gen[where y\<^sub>0 = 0 and \<beta> = 0,
          OF T0 B0 B D0 D Sc Sv tan Kc sub xnz _ orth m2 _ cc0 ccT])
      (use xin xfix ccdf in simp_all)
  then show ?thesis using ccT by simp
qed

text \<open>Letting \<open>cc \<longrightarrow> min T \<delta>\<close> removes the last slack.  This is the sharp
  interior lower bound Example 3.1 asks for: at rate \<open>m - 1\<close>, with no factor
  \<open>2\<close> and no \<open>T/2\<close> cap.\<close>

corollary covariation_val_ball_lower_sharp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T :: real
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and tan: "\<And>u. norm u \<le> 1 \<Longrightarrow> projmat b m *v u = u \<Longrightarrow>
      tanpU (projmat b m) u ** transpose (tanpU (projmat b m) u) \<in> S"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
  shows "ennreal (min T ((rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)))
      \<le> covariation_val S T K x"
proof -
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  define c0 where "c0 = min T \<delta>f"
  have r00: "0 < norm x" using xnz by simp
  have rB0: "0 < rB" using r00 xin by linarith
  have cn0: "0 < real m - 1"
  proof -
    have "(2::real) \<le> real m"
      using m2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis by linarith
  qed
  have sq_lt: "(norm x)\<^sup>2 < rB\<^sup>2"
    using r00 xin by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have c00: "0 < c0" unfolding c0_def using T0 df0 by simp
  define ccs where "ccs = (\<lambda>j :: nat. c0 - c0 / (2 * real (Suc j)))"
  have ccl: "0 < ccs j" for j
  proof -
    have "c0 / (2 * real (Suc j)) \<le> c0 / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> c0" using c00 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding ccs_def using c00 by linarith
  qed
  have ccu: "ccs j < c0" for j
  proof -
    have "0 < c0 / (2 * real (Suc j))" using c00 by simp
    then show ?thesis unfolding ccs_def by linarith
  qed
  have lim: "ccs \<longlonglongrightarrow> c0"
  proof -
    have eq: "(\<lambda>j. (c0 / 2) * inverse (real (Suc j)))
        = (\<lambda>j. c0 / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (c0 / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (c0 / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. c0 / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. c0 - c0 / (2 * real (Suc j))) \<longlonglongrightarrow> c0 - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding ccs_def by simp
  qed
  have le: "ennreal (ccs j) \<le> covariation_val S T K x" for j
  proof -
    have cT: "ccs j < T" using ccu[of j] unfolding c0_def by simp
    have cd: "ccs j < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
      using ccu[of j] unfolding c0_def \<delta>f_def[symmetric] by simp
    show ?thesis
      by (rule covariation_val_ball_lower_subspace[OF T0 B0 B D0 D Sc Sv tan Kc sub xnz xin orth
            m2 xfix ccl cT cd])
  qed
  have "(\<lambda>j. ennreal (ccs j)) \<longlonglongrightarrow> ennreal c0"
    by (rule tendsto_ennrealI[OF lim])
  then have "ennreal c0 \<le> covariation_val S T K x"
    by (rule tendsto_upperbound) (use le in auto)
  then show ?thesis unfolding c0_def \<delta>f_def .
qed

(*<*)
end
(*>*)
