

(*<*)
theory Brownian_Optimal_Boundary
  imports
    Brownian_Continuous
    Optimal_Exit_Time
begin

(*>*)

text \<open>
  The optimality locale of \<open>Optimal_Exit_Time\<close> is consistent.

    \<open>optimal_ball_market\<close> assumes the reverse inequality E[tau] >= v(x0) of
    Eq. (3.11), whose proof needs the time-changed spherical martingale and
    hence Ito calculus.  A locale that cannot be instantiated would make its
    theorem \<open>optimal_exit_time_value\<close> vacuous, so this theory exhibits an
    instance: the Brownian market started on the sphere and stopped
    immediately.  There v(x0) = 0 and the optimal exit time is 0, so the
    assumed inequality holds by \<open>ball_v_boundary\<close>; this is the boundary case
    of Example 3.1.

    A non-degenerate instance (Brownian motion stopped at the exit time of
    the ball, where E[tau] = v(x0) > 0) needs continuous-time optional
    sampling for the quadratic variation, i.e. exactly the Ito theory that
    is unavailable here.\<close>
section \<open>A Brownian market confined to the closed ball\<close>

text \<open>Stopped at time \<open>0\<close>, the Brownian market started at \<open>x0\<close> never
  leaves any ball containing \<open>x0\<close>, so it is a sufficiently volatile market
  for the compact set \<open>K = cball 0 r\<close> required by Example 3.1.\<close>

theorem Brownian_boundary_market:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and x0: "norm x0 \<le> r"
  shows "sufficiently_volatile_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
    (\<lambda>_ _. mat 1) k L (cball 0 r) x0 (\<lambda>_. 0)"
proof (rule Brownian_market_sufficiently_volatile[OF k L])
  show "(0 :: real) \<le> 0" by simp
  have start: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> 0 \<longrightarrow> cbmX x0 s \<omega> \<in> cball 0 r"
    using bmX_start[of x0] start
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s :: real assume "0 \<le> s" "s \<le> 0"
      then have "s = 0" by simp
      with elim x0 show "cbmX x0 s \<omega> \<in> cball 0 r"
        by (simp add: dist_norm)
    qed
  qed
qed

section \<open>The optimality locale is inhabited\<close>

text \<open>On the sphere the value function of Eq. (3.9) vanishes, so the
  assumed reverse inequality of \<open>optimal_ball_market\<close> is satisfied by the
  market that stops at once.  Hence that locale is consistent and its
  theorem \<open>optimal_exit_time_value\<close> is not vacuous.\<close>

theorem optimal_ball_market_boundary:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and x0: "norm x0 = r"
  shows "optimal_ball_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
    (\<lambda>_ _. mat 1) k L (cball 0 r) x0 (\<lambda>_. 0) r"
proof -
  have svm: "sufficiently_volatile_market
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
      (\<lambda>_ _. mat 1) k L (cball 0 r) x0 (\<lambda>_. 0)"
    using x0 by (intro Brownian_boundary_market k L) simp
  show ?thesis
  proof (intro optimal_ball_market.intro[OF svm]
      optimal_ball_market_axioms.intro)
    show "cball (0 :: real^'n) r = cball 0 r"
      by (rule refl)
    show "ennreal (ball_v r k x0)
        \<le> (\<integral>\<^sup>+\<omega>. ennreal 0 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
      using ball_v_boundary[OF x0, of k] by simp
  qed
qed



(*<*)
end
(*>*)
