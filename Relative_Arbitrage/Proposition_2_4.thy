section \<open>Proposition 2.4: the dynamic programming equality, with attainment\<close>

(*<*)
theory Proposition_2_4
  imports Dynamic_Programming_Assembly
begin
(*>*)

text \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close>, Eq. (2.9), for the
  horizon-\<open>T\<close> value \<open>exit_val\<close>: at a deterministic time \<open>0 \<le> r < T\<close>
  (\<open>exit_val_dpp\<close>) and at a path stopping time \<open>\<theta>\<close> with values in
  \<open>[0,T]\<close> (\<open>exit_val_dpp_time\<close>).  Every optimiser of the value function
  attains the supremum, so the supremum is a maximum.

  Both summands are read off the first piece: \<open>\<theta> \<and> \<tau>\<^sub>K\<close> is the exit time
  capped at \<open>\<theta>\<close>, and the indicator \<open>1\<^bsub>{\<theta> \<le> \<tau>\<^sub>K}\<^esub>\<close> is
  \<open>pexit \<theta> K \<dots> = \<theta> \<and> fst (\<omega> \<theta>) \<in> K\<close>, exact for the capped exit time and
  needing no path continuity.

  What is not proved here.  The paper states (2.9) for \<open>v\<close> on \<open>[0,\<infinity>)\<close> at
  arbitrary stopping times of the natural filtration of \<open>X\<close>.  The transfer
  needs the identification of \<open>v\<close> with \<open>exit_val\<close> at large horizons, the
  transport of essential infima between the two classes, Galmarino's test for
  the coordinate filtration on continuous paths, and a limit argument for
  unbounded \<open>\<theta>\<close>.\<close>

text \<open>The \<open>\<le>\<close> half, one class member at a time, at an arbitrary time
  function \<open>\<theta>\<close> with values in \<open>[0,T]\<close> (no stopping-time property and no
  measurability is needed): the essential infimum of the exit time under
  \<open>P\<close> is below the essential infimum of the DPP integrand under the same
  \<open>P\<close>.  The conditioning step is @{thm [source] exit_val_cond_time}.\<close>

lemma exit_val_dpp_ess_inf_mono_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
          + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
             then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
proof -
  have PP: "prob_space P" by (rule exit_class_prob[OF P])
  have taule: "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> T" for \<omega> :: "'n pairpath"
    by (rule pexit_le_T[OF T0])
  have fin: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) < \<top>"
  proof -
    have "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) \<le> ennreal T"
      by (rule ess_inf_time_le_const[OF PP taule])
    moreover have "(ennreal T :: ennreal) < \<top>" by simp
    ultimately show ?thesis by (rule order.strict_trans1)
  qed
  define c where
    "c = enn2real (ess_inf_time P (\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))))"
  have ceq: "ennreal c = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding c_def by (rule ennreal_enn2real[OF fin])
  have aeT: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono[OF ess_inf_time_AE
      [of P "\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have "ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))" using ceq by simp
    then show "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  \<comment> \<open>the conditioning statement at the time \<open>\<theta>\<close>\<close>
  have aeS: "AE \<omega> in P. c \<le> \<theta> \<omega>
      + enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    by (rule exit_val_cond_time[OF T0 L1 Kc P aeT th0 thT])
  have aeg: "AE \<omega> in P. ennreal c \<le> ennreal (pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    using aeT aeS
  proof eventually_elim
    case (elim \<omega>)
    have "c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
    proof (cases "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K")
      case True
      then show ?thesis using elim(2) by simp
    next
      case False
      \<comment> \<open>off the survival event the horizon cap at \<open>\<theta>\<close> is invisible\<close>
      have eq: "pexit T K (\<lambda>t. fst (\<omega> t)) = pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))"
        by (rule pexit_cap_eq[OF th0 thT False])
      have z: "(if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
          then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0) = 0"
        using False by (rule if_not_P)
      show ?thesis using elim(1) eq z by simp
    qed
    then show ?case by (rule ennreal_leI)
  qed
  have "ennreal c \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    by (rule ess_inf_timeI[OF aeg])
  then show ?thesis unfolding ceq .
qed

text \<open>Hence the \<open>\<le>\<close> half of (2.9) at an arbitrary time function.\<close>

theorem exit_val_dpp_le_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "exit_val k L T K x
      \<le> (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
proof -
  have pv: "exit_val k L T K x = (SUP Q \<in> exit_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding exit_val_def ..
  show ?thesis
    unfolding pv
    by (rule SUP_subset_mono[OF order.refl])
       (rule exit_val_dpp_ess_inf_mono_time[OF T0 L1 Kc _ th0 thT])
qed

subsection \<open>Step 1: the equality at a deterministic time\<close>

lemma exit_val_dpp_ess_inf_mono:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  show ?thesis
    by (rule exit_val_dpp_ess_inf_mono_time[where \<theta> = "\<lambda>_. r", OF T0 L1 Kc P r rT])
qed

text \<open>Proposition 2.4, Eq. (2.9), at a deterministic time \<open>0 \<le> r < T\<close>.\<close>

theorem exit_val_dpp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "exit_val k L T K x
      = (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))"
proof (rule antisym)
  have rT': "r \<le> T" using rT by simp
  have pv: "exit_val k L T K x = (SUP Q \<in> exit_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding exit_val_def ..
  show "exit_val k L T K x
      \<le> (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))"
    unfolding pv
    by (rule SUP_subset_mono[OF order.refl])
       (rule exit_val_dpp_ess_inf_mono[OF r rT' L1 Kc])
  show "(SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))
      \<le> exit_val k L T K x"
    by (rule exit_val_dpp_sup_ge[OF r rT L1 Kc])
qed

text \<open>Attainment: every optimizer of the value function attains the
  supremum in (2.9).\<close>

theorem exit_val_dpp_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> exit_class k L T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      = exit_val k L T K x"
proof (rule antisym)
  have rT': "r \<le> T" using rT by simp
  show "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      \<le> exit_val k L T K x"
    by (rule exit_val_dpp_ge[OF r rT L1 Kc P])
  show "exit_val k L T K x
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
    unfolding opt[symmetric] by (rule exit_val_dpp_ess_inf_mono[OF r rT' L1 Kc P])
qed

text \<open>Optimizers exist (@{thm [source] exit_val_attained}), so the supremum
  in (2.9) is a maximum.\<close>

corollary exit_val_dpp_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "\<exists>P \<in> exit_class k L T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      = exit_val k L T K x"
proof -
  have T0: "0 < T" using r rT by simp
  show ?thesis
    using exit_val_attained[where k = k, OF T0 L1 Kc]
      exit_val_dpp_optimizer[OF r rT L1 Kc] by blast
qed

subsection \<open>Step 2: the equality at a stopping time\<close>

text \<open>Proposition 2.4, Eq. (2.9), at a path stopping time \<open>\<theta>\<close> with values
  in \<open>[0,T]\<close>.  The \<open>\<ge>\<close> half is @{thm [source] exit_val_dpp_sup_ge_time}; the
  \<open>\<le>\<close> half is @{thm [source] exit_val_dpp_le_time}.\<close>

theorem exit_val_dpp_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "exit_val k L T K x
      = (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
proof (rule antisym)
  have T0': "0 \<le> T" using T0 by simp
  show "exit_val k L T K x
      \<le> (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
    by (rule exit_val_dpp_le_time[OF T0' L1 Kc
          path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st]])
  show "(SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))
      \<le> exit_val k L T K x"
    by (rule exit_val_dpp_sup_ge_time[OF T0 L1 Kc st thM])
qed

theorem exit_val_dpp_time_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real" and P :: "('n pairpath) measure"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and P: "P \<in> exit_class k L T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = exit_val k L T K x"
proof (rule antisym)
  have T0': "0 \<le> T" using T0 by simp
  have "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      \<le> (SUP Q \<in> exit_class k L T x. ess_inf_time Q
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
    using P by (rule SUP_upper)
  also have "\<dots> \<le> exit_val k L T K x"
    by (rule exit_val_dpp_sup_ge_time[OF T0 L1 Kc st thM])
  finally show "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      \<le> exit_val k L T K x" .
  show "exit_val k L T K x
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    unfolding opt[symmetric]
    by (rule exit_val_dpp_ess_inf_mono_time[OF T0' L1 Kc P
          path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st]])
qed

corollary exit_val_dpp_time_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "\<exists>P \<in> exit_class k L T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = exit_val k L T K x"
  using exit_val_attained[where k = k, OF T0 L1 Kc]
    exit_val_dpp_time_optimizer[OF T0 L1 Kc st thM] by blast

(*<*)
end
(*>*)
