section \<open>The dynamic programming principle for an abstract constraint set\<close>

(*<*)
theory Dynamic_Programming_Principle
  imports Dynamic_Programming_Assembly
begin
(*>*)

text \<open>The dynamic programming principle of Proposition 2.4 of
  \<^cite>\<open>LaiShkolnikovSoner\<close>, Eq. (2.9), for the horizon-\<open>T\<close> value
  \<^const>\<open>covariation_val\<close> of an abstract constraint set \<open>S\<close>: at a
  deterministic time \<open>0 \<le> r < T\<close> (\<open>covariation_val_dpp\<close>) and at a path
  stopping time \<open>\<theta>\<close> with values in \<open>[0,T]\<close> (\<open>covariation_val_dpp_time\<close>).
  Every optimiser attains the supremum, so the supremum is a maximum.  \<open>S\<close>
  is closed and convex (the class is closed under cutting and pasting), has
  a norm bound \<open>B\<close> and a diagonal bound \<open>D\<close> (the class is compact, so the
  value is upper semicontinuous and attained), and holds some covariation
  rate \<open>\<sigma> \<sigma>\<^sup>T\<close> (the class is nonempty and the value monotone in the
  horizon).

  Both summands are read off the first piece: \<open>\<theta> \<and> \<tau>\<^sub>K\<close> is the exit time
  capped at \<open>\<theta>\<close>, and the indicator \<open>1\<^bsub>{\<theta> \<le> \<tau>\<^sub>K}\<^esub>\<close> is
  \<open>pexit \<theta> K \<dots> = \<theta> \<and> fst (\<omega> \<theta>) \<in> K\<close>, exact for the capped exit time and
  needing no path continuity.\<close>

text \<open>The \<open>\<le>\<close> half, one class member at a time, at an arbitrary time
  function \<open>\<theta>\<close> with values in \<open>[0,T]\<close> (no stopping-time property and no
  measurability is needed): the essential infimum of the exit time under
  \<open>P\<close> is below the essential infimum of the DPP integrand under the same
  \<open>P\<close>.  The conditioning step is @{thm [source] covariation_val_cond_time}.\<close>

lemma covariation_val_dpp_ess_inf_mono_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and P :: "('n pairpath) measure" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and P: "P \<in> covariation_class S T x"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
          + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
             then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
proof -
  have PP: "prob_space P" by (rule covariation_class_prob[OF P])
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
      + enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    by (rule covariation_val_cond_time[OF T0 B0 B D0 D Sc Sv SST Kc P aeT th0 thT])
  have aeg: "AE \<omega> in P. ennreal c \<le> ennreal (pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    using aeT aeS
  proof eventually_elim
    case (elim \<omega>)
    have "c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
    proof (cases "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K")
      case True
      then show ?thesis using elim(2) by simp
    next
      case False
      \<comment> \<open>off the survival event the horizon cap at \<open>\<theta>\<close> is invisible\<close>
      have eq: "pexit T K (\<lambda>t. fst (\<omega> t)) = pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))"
        by (rule pexit_cap_eq[OF th0 thT False])
      have z: "(if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
          then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0) = 0"
        using False by (rule if_not_P)
      show ?thesis using elim(1) eq z by simp
    qed
    then show ?case by (rule ennreal_leI)
  qed
  have "ennreal c \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    by (rule ess_inf_timeI[OF aeg])
  then show ?thesis unfolding ceq .
qed

text \<open>Hence the \<open>\<le>\<close> half of the principle at an arbitrary time function.\<close>

theorem covariation_val_dpp_le_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "covariation_val S T K x
      \<le> (SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
proof -
  have pv: "covariation_val S T K x = (SUP Q \<in> covariation_class S T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding covariation_val_def ..
  show ?thesis
    unfolding pv
    by (rule SUP_subset_mono[OF order.refl])
       (rule covariation_val_dpp_ess_inf_mono_time[OF T0 B0 B D0 D Sc Sv SST Kc _ th0 thT])
qed

subsection \<open>Step 1: the equality at a deterministic time\<close>

lemma covariation_val_dpp_ess_inf_mono:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and P: "P \<in> covariation_class S T x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  show ?thesis
    by (rule covariation_val_dpp_ess_inf_mono_time[where \<theta> = "\<lambda>_. r", OF T0 B0 B D0 D Sc Sv SST Kc P r rT])
qed

text \<open>The principle at a deterministic time \<open>0 \<le> r < T\<close>.\<close>

theorem covariation_val_dpp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
  shows "covariation_val S T K x
      = (SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0)))"
proof (rule antisym)
  have rT': "r \<le> T" using rT by simp
  have pv: "covariation_val S T K x = (SUP Q \<in> covariation_class S T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding covariation_val_def ..
  show "covariation_val S T K x
      \<le> (SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0)))"
    unfolding pv
    by (rule SUP_subset_mono[OF order.refl])
       (rule covariation_val_dpp_ess_inf_mono[OF r rT' B0 B D0 D Sc Sv SST Kc])
  show "(SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0)))
      \<le> covariation_val S T K x"
    by (rule covariation_val_dpp_sup_ge[OF r rT B0 B D0 D Sc Sv SST Kc])
qed

text \<open>Attainment: every optimizer of the value function attains the
  supremum in the principle.\<close>

theorem covariation_val_dpp_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and P: "P \<in> covariation_class S T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0))
      = covariation_val S T K x"
proof (rule antisym)
  have rT': "r \<le> T" using rT by simp
  show "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0))
      \<le> covariation_val S T K x"
    by (rule covariation_val_dpp_ge[OF r rT B0 B D0 D Sc Sv SST Kc P])
  show "covariation_val S T K x
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0))"
    unfolding opt[symmetric] by (rule covariation_val_dpp_ess_inf_mono[OF r rT' B0 B D0 D Sc Sv SST Kc P])
qed

text \<open>Optimizers exist (@{thm [source] covariation_val_attained}), so the supremum
  in the principle is a maximum.\<close>

corollary covariation_val_dpp_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
  shows "\<exists>P \<in> covariation_class S T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (covariation_val S (T - r) K (fst (\<omega> r))) else 0))
      = covariation_val S T K x"
proof -
  have T0: "0 < T" using r rT by simp
  have att: "\<exists>P \<in> covariation_class S T x.
        ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x"
    by (rule covariation_val_attained[OF T0 B0 B D0 D Sc SST Kc])
  show ?thesis
    using att covariation_val_dpp_optimizer[OF r rT B0 B D0 D Sc Sv SST Kc] by blast
qed

subsection \<open>Step 2: the equality at a stopping time\<close>

text \<open>The principle at a path stopping time \<open>\<theta>\<close> with values
  in \<open>[0,T]\<close>.  The \<open>\<ge>\<close> half is @{thm [source] covariation_val_dpp_sup_ge_time}; the
  \<open>\<le>\<close> half is @{thm [source] covariation_val_dpp_le_time}.\<close>

theorem covariation_val_dpp_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "covariation_val S T K x
      = (SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
proof (rule antisym)
  have T0': "0 \<le> T" using T0 by simp
  show "covariation_val S T K x
      \<le> (SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
    by (rule covariation_val_dpp_le_time[OF T0' B0 B D0 D Sc Sv SST Kc
          path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st]])
  show "(SUP P \<in> covariation_class S T x. ess_inf_time P
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))
      \<le> covariation_val S T K x"
    by (rule covariation_val_dpp_sup_ge_time[OF T0 B0 B D0 D Sc Sv SST Kc st thM])
qed

theorem covariation_val_dpp_time_optimizer:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real" and P :: "('n pairpath) measure"
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and P: "P \<in> covariation_class S T x"
    and opt: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = covariation_val S T K x"
proof (rule antisym)
  have T0': "0 \<le> T" using T0 by simp
  have "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      \<le> (SUP Q \<in> covariation_class S T x. ess_inf_time Q
          (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))"
    using P by (rule SUP_upper)
  also have "\<dots> \<le> covariation_val S T K x"
    by (rule covariation_val_dpp_sup_ge_time[OF T0 B0 B D0 D Sc Sv SST Kc st thM])
  finally show "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      \<le> covariation_val S T K x" .
  show "covariation_val S T K x
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    unfolding opt[symmetric]
    by (rule covariation_val_dpp_ess_inf_mono_time[OF T0' B0 B D0 D Sc Sv SST Kc P
          path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st]])
qed

corollary covariation_val_dpp_time_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
  shows "\<exists>P \<in> covariation_class S T x.
      ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x
    \<and> ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (covariation_val S (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      = covariation_val S T K x"
proof -
  have att: "\<exists>P \<in> covariation_class S T x.
        ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x"
    by (rule covariation_val_attained[OF T0 B0 B D0 D Sc SST Kc])
  show ?thesis
    using att covariation_val_dpp_time_optimizer[OF T0 B0 B D0 D Sc Sv SST Kc st thM] by blast
qed

(*<*)
end
(*>*)
