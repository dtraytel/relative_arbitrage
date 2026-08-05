(*
  Title:   Paper_Bridge.thy
  Content: The bridge from the repo's market witnesses to the paper's
           class (1.7) of arXiv:2512.17702.

           Per the paper's (1.7)-(1.8) the processes in P_x are NEVER
           stopped: the covariation constraint holds for a.e. t >= 0 and
           tau_K is merely a functional of the path.  A `stopped_market'
           witness is therefore NOT a class member -- its volatility
           vanishes after its stopping time, and 0 is not admissible.
           The faithful bridge CONTINUES the witness past the stopping
           time with an admissible volatility; `Paper_Class.acont' does
           that, and `Paper_Class.mat_1_in_sconstraint' supplies the
           value (legitimate exactly because the locale carries the
           paper's standing assumption L >= 1).

           This theory sits downstream of BOTH Paper_Class and the
           market stack, so that neither has to import the other.

  STATUS:  PIDE-verified (79 commands, overall_status ok).

           HISTORY: registering this NEW theory in ROOT wedged the
           running PIDE session -- the server snapshots ROOT at startup,
           so afterwards every theory reported "Malformed theory", and
           reverting the ROOT edit did NOT recover it.  A restart was
           required.  To add a theory mid-session, prefer adding an
           import to an existing theory instead.
*)

theory Paper_Bridge
  imports Paper_Class Section_2_Usc
begin

section \<open>Extracting the pointwise constraint from a market witness\<close>

text \<open>The locale's volatility hypotheses are stated as three separate
  almost-sure facts, each valid only up to the stopping time.  Combined
  and continued they give a single almost-sure statement holding for ALL
  times, which is the shape \<open>paper_pair_class\<close> asks for.\<close>

theorem stopped_market_acont_in_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
  shows "AE \<omega> in M. \<forall>s. 0 \<le> s
      \<longrightarrow> acont (\<lambda>u. acov u \<omega>) (tau \<omega>) s \<in> sconstraint k L"
proof -
  from SM have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding stopped_market_def by blast
  interpret SV: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L1: "1 \<le> L" by (rule SV.L_ge)
  show ?thesis
    using SV.acov_psd SV.acov_eigen_lb SV.acov_eigen_ub
  proof eventually_elim
    case (elim \<omega>)
    then have pd: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and lb: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega>
          \<Longrightarrow> eigen_lb (acov u \<omega>) (CARD('n) - k)"
      and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      by blast+
    \<comment> \<open>\<open>pd\<close>, not \<open>psd\<close>: naming a local fact after the constant \<open>psd\<close>
        is legal (facts and constants live in separate namespaces) but
        invites misreading in the \<open>unfolding\<close> step just below.\<close>
    have sv: "acov u \<omega> \<in> suff_volatile k" if "0 \<le> u" "u \<le> tau \<omega>" for u
      unfolding suff_volatile_def using pd[OF that] lb[OF that] by simp
    show ?case
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      show "acont (\<lambda>u. acov u \<omega>) (tau \<omega>) s \<in> sconstraint k L"
        by (rule acont_in_sconstraint[OF L1 sv ub s])
    qed
  qed
qed

text \<open>In particular the continued volatility of a market witness never
  leaves the constraint set, whereas the witness's own volatility does the
  moment it is stopped -- which is precisely the mismatch this theory
  exists to repair.\<close>

section \<open>Integrability of the continued volatility\<close>

text \<open>To build the running covariation \<open>Yint\<close> from a witness the continued
  volatility must be INTEGRABLE on bounded intervals.  Boundedness is free:
  on \<open>[0, tau \<omega>]\<close> the locale's \<open>psd\<close> + \<open>eigen_ub L\<close> bound every entry by \<open>L\<close>
  (via \<open>sconstraint_norm_le\<close>), and after \<open>tau \<omega>\<close> the continuation is the
  constant \<open>mat 1\<close>.  What the locale does NOT supply is MEASURABILITY of
  \<open>acov\<close> in the TIME variable: \<open>acov_trace_integrable\<close> covers only the
  trace, and \<open>coord_Z\<close> only the diagonal entries.

  So time-measurability is an explicit hypothesis here.  That is faithful
  rather than a weakening: the paper's (1.7) constrains \<open>d\<langle>X\<^sub>i,X\<^sub>j\<rangle>(t)/dt\<close>,
  which presupposes the covariation density exists as a measurable object
  in \<open>t\<close>.  Recorded in PLAN\_THEOREM\_1\_1.md as a gap in the locale, to be
  closed there rather than assumed away here.\<close>

lemma acont_bounded:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes L1: "1 \<le> L"
    and sv: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> acov u \<omega> \<in> suff_volatile k"
    and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> eigen_ub (acov u \<omega>) L"
    and u: "0 \<le> u"
  shows "norm (acont (\<lambda>r. acov r \<omega>) tv u) \<le> real CARD('n) * L"
proof (rule sconstraint_norm_le)
  show "0 \<le> L" using L1 by simp
  show "acont (\<lambda>r. acov r \<omega>) tv u \<in> sconstraint k L"
    by (rule acont_in_sconstraint[OF L1 sv ub u])
qed

theorem stopped_market_acont_integrable:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and meas: "AE \<omega> in M. (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
        \<in> borel_measurable lborel"
    and st: "0 \<le> s" "s \<le> t"
  shows "AE \<omega> in M.
      set_integrable lborel {s..t} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
proof -
  from SM have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding stopped_market_def by blast
  interpret SV: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L1: "1 \<le> L" by (rule SV.L_ge)
  have Bnn: "0 \<le> real CARD('n) * L" using L1 by simp
  show ?thesis
    using SV.acov_psd SV.acov_eigen_lb SV.acov_eigen_ub meas
  proof eventually_elim
    case (elim \<omega>)
    then have pd: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and lb: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega>
          \<Longrightarrow> eigen_lb (acov u \<omega>) (CARD('n) - k)"
      and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      and m: "(\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u) \<in> borel_measurable lborel"
      by blast+
    have sv: "acov u \<omega> \<in> suff_volatile k" if "0 \<le> u" "u \<le> tau \<omega>" for u
      unfolding suff_volatile_def using pd[OF that] lb[OF that] by simp
    \<comment> \<open>the conclusion must drive the unification here: an \<^verbatim>\<open>OF\<close> chain on
        \<^verbatim>\<open>acont_bounded\<close> reports "multiple unifiers".\<close>
    have bnd: "norm (acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u) \<le> real CARD('n) * L"
      if u0: "0 \<le> u" for u
    proof (rule acont_bounded)
      show "1 \<le> L" by (rule L1)
      show "\<And>v. 0 \<le> v \<Longrightarrow> v \<le> tau \<omega> \<Longrightarrow> acov v \<omega> \<in> suff_volatile k"
        by (rule sv)
      show "\<And>v. 0 \<le> v \<Longrightarrow> v \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov v \<omega>) L"
        by (rule ub)
      show "0 \<le> u" by (rule u0)
    qed
    have dom: "integrable lborel
        (\<lambda>u. indicat_real {s..t} u * (real CARD('n) * L))"
    proof -
      have "integrable lborel (indicat_real {s..t})"
        by (rule integrable_real_indicator)
          (use st in \<open>auto simp: emeasure_lborel_Icc\<close>)
      then show ?thesis by simp
    qed
    show ?case
      unfolding set_integrable_def
    \<comment> \<open>\<^verbatim>\<open>Bochner_Integration.\<close> is required: the bare name resolves to the
        Henstock lemma about \<^verbatim>\<open>integrable_on cbox\<close>, exactly as for
        \<^verbatim>\<open>integrable_const\<close>.\<close>
    proof (rule Bochner_Integration.integrable_bound[OF dom])
      show "(\<lambda>u. indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
          \<in> borel_measurable lborel"
        using m by measurable
      show "AE u in lborel.
          norm (indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
          \<le> norm (indicat_real {s..t} u * (real CARD('n) * L))"
      proof (intro AE_I2)
        fix u :: real
        show "norm (indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
            \<le> norm (indicat_real {s..t} u * (real CARD('n) * L))"
        proof (cases "u \<in> {s..t}")
          case True
          then have u0: "0 \<le> u" using st by simp
          show ?thesis using bnd[OF u0] True Bnn by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

corollary stopped_market_acov_leaves_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and s: "\<omega> \<in> space M" "tau \<omega> < s"
  shows "acov s \<omega> = 0"
  using SM s unfolding stopped_market_def by blast

end
