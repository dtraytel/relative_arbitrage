(*
  Title:   Paper_Viscosity.thy
  Content: Towards clause (2) of Theorem 1.1 of arXiv:2512.17702 --- the
           viscosity subsolution property of `paper_v`.  This is the first
           batch of PLAN section 2.1.

  The operator of Eq. (1.9) is an INFIMUM,

      ell_op k L p M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p),

  so the subsolution inequality `ell_op k L (g x) H \<le> 1` needs only ONE
  feasible witness `a` with `- trace (H ** a) / 2 \<le> 1`.  That is what makes
  the reduction below short: everything except the production of the witness
  is bookkeeping, and the witness is exactly what Ito's formula for class
  members delivers.
*)

theory Paper_Viscosity
  imports Paper_DPP Relative_Arbitrage_PDE Envelopes
begin

section \<open>One witness suffices for the subsolution inequality\<close>

text \<open>\<^const>\<open>ell_op\<close> is an infimum over the feasible set, and
  @{thm [source] ell_op_bdd_below} says that infimum is over a set bounded
  below.  So a single feasible matrix beating the threshold settles the
  inequality --- there is no need to control the whole family.\<close>

lemma ell_op_le_of_witness:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p" and le: "- trace (M ** a) / 2 \<le> c"
  shows "ell_op k L p M \<le> c"
proof -
  have mem: "- trace (M ** a) / 2 \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    using a by blast
  have "ell_op k L p M \<le> - trace (M ** a) / 2"
    unfolding ell_op_def by (rule cInf_lower[OF mem ell_op_bdd_below])
  also have "\<dots> \<le> c" by (rule le)
  finally show ?thesis .
qed

corollary ell_op_le_one_of_witness:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p" and le: "- trace (M ** a) / 2 \<le> 1"
  shows "ell_op k L p M \<le> 1"
  by (rule ell_op_le_of_witness[OF a le])

section \<open>The DPP at the exit time of a ball\<close>

text \<open>The \<open>\<le>\<close> half of the DPP, @{thm [source] paper_v_cond_time}, asks of its
  random time only that it lie in \<open>[0,T]\<close> --- NOT that it be a
  \<^const>\<open>path_stopping_time\<close>.  That is what lets the SUBSOLUTION argument use
  the exit time of a ball directly.

  (The supersolution half is not so lucky: it consumes
  @{thm [source] paper_v_dpp_sup_ge_time}, whose \<open>\<theta>\<close> must be a path stopping
  time, and the exit time of a ball is one only for CONTINUOUS paths, while
  \<^const>\<open>path_stopping_time\<close> quantifies over all functions.  The fix is to
  restrict the congruence clause to the path space; that is a separate,
  small piece of work and it is recorded here so it is not rediscovered.)

  Combining with @{thm [source] enn2real_paper_v_horizon_cap} puts the
  conclusion in a form with NO varying horizon left: the value at the reduced
  horizon is the value at \<open>T\<close>, capped.\<close>

definition pball_exit :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  where "pball_exit T x \<epsilon> \<omega> = pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"

lemma pball_exit_nonneg:
  assumes T0: "0 \<le> T" shows "0 \<le> pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def by (rule pexit_nonneg[OF T0])

lemma pball_exit_le:
  assumes T0: "0 \<le> T" shows "pball_exit T x \<epsilon> \<omega> \<le> T"
  unfolding pball_exit_def by (rule pexit_le_T[OF T0])

theorem paper_v_cond_ball:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x y :: "real^'n"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> paper_pair_class k L T y"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
            (T - pball_exit T x \<epsilon> \<omega>)"
proof -
  have th0: "0 \<le> pball_exit T x \<epsilon> \<omega>" for \<omega> :: "'n pairpath"
    by (rule pball_exit_nonneg[OF T0])
  have thT: "pball_exit T x \<epsilon> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule pball_exit_le[OF T0])
  have "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    by (rule paper_v_cond_time[OF T0 L1 Kc P c th0 thT])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "c \<le> pball_exit T x \<epsilon> \<omega>
        + enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
            (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    have a: "0 \<le> T - pball_exit T x \<epsilon> \<omega>" using thT[of \<omega>] by simp
    have b: "T - pball_exit T x \<epsilon> \<omega> \<le> T" using th0[of \<omega>] by simp
    have "enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))
        = min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with h show "c \<le> pball_exit T x \<epsilon> \<omega>
        + min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)" by simp
  qed
qed

section \<open>The analytic input, isolated\<close>

text \<open>Everything above is unconditional.  What the subsolution proof still
  needs from \<^const>\<open>paper_pair_class\<close> is ONE statement, and it is exactly
  Ito's formula applied to a test function along a class member:

  for a test function \<open>\<phi>\<close> touching \<^const>\<open>paper_v\<close> from above at \<open>x\<close>, the
  DPP bound of @{thm [source] paper_v_cond_ball} forces the second-order
  expansion of \<open>\<phi>\<close> against the member's covariation to beat \<open>-2\<close>, and the
  covariation direction is feasible because a class member's \<open>d\<langle>X\<rangle>\<close> lies in
  \<^const>\<open>sconstraint\<close> and is orthogonal to the gradient at the touching
  point.

  We name that output as a predicate rather than assume Ito itself, so the
  interface is the smallest possible: a supplier only has to produce the
  WITNESS.  This is the same discipline
  @{thm [source] paper_pair_class_aglue} was built with --- hypotheses first,
  suppliers later --- and it means the reduction below can be checked now.\<close>

definition class_expansion_witness ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> bool"
  where
  "class_expansion_witness k L T K \<longleftrightarrow>
     (\<forall>x \<in> interior K. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>z \<in> ball x e.
           enn2real (paper_v k L T K z) - \<phi> z
             \<le> enn2real (paper_v k L T K x) - \<phi> x) \<longrightarrow>
        (\<exists>a \<in> feasible k L (g x). - trace (H ** a) / 2 \<le> 1))"

theorem paper_v_visc_subsol_of_witness:
  fixes K :: "(real^'n::finite) set"
  assumes W: "class_expansion_witness k L T K"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (paper_v k L T K z))"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>z \<in> ball x e.
        enn2real (paper_v k L T K z) - \<phi> z
          \<le> enn2real (paper_v k L T K x) - \<phi> x"
  from W[unfolded class_expansion_witness_def] x tf lm
  obtain a where a: "a \<in> feasible k L (g x)"
    and le: "- trace (H ** a) / 2 \<le> 1" by blast
  show "ell_op k L (g x) H \<le> 1" by (rule ell_op_le_one_of_witness[OF a le])
qed

section \<open>What remains for clause (2)\<close>

text \<open>Two suppliers, in this order.

  \<^item> \<open>class_expansion_witness\<close> --- Ito's formula for class members.  The
    class is defined by MARTINGALE properties, not by an SDE, so this is the
    statement that the compensated second-order expansion of a \<open>C\<^sup>2\<close> test function
    along the member is a martingale, proved from clause (iv) of (1.7) plus the covariation
    constraint (iii).  \<open>Stochastic_Integral\<close> and \<open>Ito_Covariation\<close> are the
    intended sources; \<open>Relative_Arbitrage_Ito.ito_formula_quadratic\<close> is the
    market-side analogue to imitate.  Feasibility of the limiting \<open>a\<close> is
    \<^const>\<open>sconstraint\<close> (clause (iii)) plus orthogonality to \<open>g x\<close>.

  \<^item> the SUPERSOLUTION half --- @{thm [source] paper_v_dpp_sup_ge_time} plus
    a weak solution of the SDE (3.24).  Note the caveat recorded above: its
    \<open>\<theta>\<close> must be a \<^const>\<open>path_stopping_time\<close>, and a ball exit time satisfies
    the congruence clause only along CONTINUOUS paths, so
    \<^const>\<open>path_stopping_time\<close> needs a path-space-restricted variant first.\<close>

end
