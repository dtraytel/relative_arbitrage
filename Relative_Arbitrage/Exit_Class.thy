
(*<*)
theory Exit_Class
  imports
    "Relative_Arbitrage_Equation.Constraint_Set_Convexity" "Relative_Arbitrage_Equation.Operator_Formula" "Path_Space_Operations.Pair_Path_Laws"
begin

(*>*)

text \<open>
  Encodes the class \<open>P\<^sub>x\<close> of Eq. (1.7) as laws of the pair
  \<open>(X, \<langle>X\<rangle>)\<close> on the path space, following the paper's own proof of
  Lemma 2.3. The covariation is carried as a second, uniformly Lipschitz
  path component whose difference quotients lie in the compact convex
  constraint set \<open>S = Pi_constraint k \<inter> {eigen_ub L}\<close>. Lemma 2.1, in
  the exact form \<open>lemma_2_1_exact\<close>, identifies \<open>S\<close> with the convex hull
  of the unconvexified sufficient-volatility set of Eq. (1.4).\<close>
section \<open>The constraint set of Eq. (1.5) with the technical cap\<close>

definition sconstraint :: "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite^'n) set" where
  "sconstraint k L = Pi_constraint k \<inter> {a. eigen_ub a L}"

text \<open>\<open>quadform_convex_comb\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma convex_eigen_ub:
  "convex {a :: real^'n::finite^'n. eigen_ub a L}"
proof (rule convexI)
  fix a b :: "real^'n^'n" and s t :: real
  assume ab: "a \<in> {a. eigen_ub a L}" "b \<in> {a. eigen_ub a L}"
    and st: "0 \<le> s" "0 \<le> t" "s + t = 1"
  have "x \<bullet> ((s *\<^sub>R a + t *\<^sub>R b) *v x) \<le> L * (x \<bullet> x)" for x
  proof -
    have "x \<bullet> ((s *\<^sub>R a + t *\<^sub>R b) *v x)
        = s * (x \<bullet> (a *v x)) + t * (x \<bullet> (b *v x))"
      by (rule quadform_convex_comb)
    also have "\<dots> \<le> s * (L * (x \<bullet> x)) + t * (L * (x \<bullet> x))"
      using ab st by (intro add_mono mult_left_mono) (auto simp: eigen_ub_def)
    also have "\<dots> = L * (x \<bullet> x)"
    proof -
      have "s * (L * (x \<bullet> x)) + t * (L * (x \<bullet> x)) = (s + t) * (L * (x \<bullet> x))"
        by (simp add: algebra_simps)
      then show ?thesis using st by simp
    qed
    finally show ?thesis .
  qed
  then show "s *\<^sub>R a + t *\<^sub>R b \<in> {a. eigen_ub a L}"
    by (simp add: eigen_ub_def)
qed

theorem sconstraint_convex: "convex (sconstraint k L :: (real^'n::finite^'n) set)"
  unfolding sconstraint_def
  by (intro convex_Int Pi_constraint_convex convex_eigen_ub)

subsection \<open>Closedness\<close>

text \<open>\<open>Pi_proj a m\<close> is an infimum over the rank-\<open>m\<close> projections, so on the
  psd cone the condition \<open>c \<le> Pi_proj a m\<close> is exactly the family of linear
  inequalities \<open>c \<le> trace (a ** P)\<close> --- one closed half-space per \<open>P\<close>.\<close>

lemma Pi_proj_ge_iff:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and m: "m \<le> CARD('n)"
  shows "c \<le> Pi_proj a m
      \<longleftrightarrow> (\<forall>P :: real^'n^'n. is_proj P \<longrightarrow> trace P = real m \<longrightarrow> c \<le> trace (a ** P))"
proof
  assume "c \<le> Pi_proj a m"
  then show "\<forall>P :: real^'n^'n. is_proj P \<longrightarrow> trace P = real m
      \<longrightarrow> c \<le> trace (a ** P)"
    using Pi_proj_le[OF a] by (metis order_trans)
next
  assume "\<forall>P :: real^'n^'n. is_proj P \<longrightarrow> trace P = real m
      \<longrightarrow> c \<le> trace (a ** P)"
  then show "c \<le> Pi_proj a m" by (intro Pi_proj_ge[OF m]) blast
qed

text \<open>\<open>continuous_on_trace_mult_right\<close>, \<open>closed_trace_proj_halfspace\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma closed_Pi_constraint:
  "closed (Pi_constraint k :: (real^'n::finite^'n) set)"
proof -
  have eq: "(Pi_constraint k :: (real^'n^'n) set)
      = {a. psd a}
        \<inter> (\<Inter>m \<in> {m. k < m \<and> m \<le> CARD('n)}.
             \<Inter>P \<in> {P :: real^'n^'n. is_proj P \<and> trace P = real m}.
               {a. real (m - k) \<le> trace (a ** P)})"
  proof (intro set_eqI iffI)
    fix a :: "real^'n^'n" assume "a \<in> Pi_constraint k"
    then have a: "psd a"
      and pi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> real (m - k) \<le> Pi_proj a m"
      by (auto simp: Pi_constraint_def)
    show "a \<in> {a. psd a}
        \<inter> (\<Inter>m \<in> {m. k < m \<and> m \<le> CARD('n)}.
             \<Inter>P \<in> {P :: real^'n^'n. is_proj P \<and> trace P = real m}.
               {a. real (m - k) \<le> trace (a ** P)})"
      using a pi Pi_proj_ge_iff[OF a] by auto
  next
    fix a :: "real^'n^'n"
    assume "a \<in> {a. psd a}
        \<inter> (\<Inter>m \<in> {m. k < m \<and> m \<le> CARD('n)}.
             \<Inter>P \<in> {P :: real^'n^'n. is_proj P \<and> trace P = real m}.
               {a. real (m - k) \<le> trace (a ** P)})"
    then have a: "psd a"
      and tr: "\<And>m P. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> is_proj P \<Longrightarrow> trace P = real m
          \<Longrightarrow> real (m - k) \<le> trace (a ** P)"
      by auto
    show "a \<in> Pi_constraint k"
      unfolding Pi_constraint_def
      using a Pi_proj_ge_iff[OF a] tr by auto
  qed
  show ?thesis
    unfolding eq
    by (intro closed_Int closed_psd closed_INT ballI
        closed_trace_proj_halfspace)
qed

theorem closed_sconstraint: "closed (sconstraint k L :: (real^'n::finite^'n) set)"
  unfolding sconstraint_def
  by (intro closed_Int closed_Pi_constraint closed_eigen_ub)

subsection \<open>Boundedness, hence compactness\<close>

lemma psd_eigen_ub_diag:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and ub: "eigen_ub a L"
  shows "0 \<le> a $ i $ i" and "a $ i $ i \<le> L"
  by (rule psd_diag_nonneg[OF a]) (rule eigen_ub_diag[OF ub])

theorem sconstraint_norm_le:
  fixes a :: "real^'n::finite^'n"
  assumes L: "0 \<le> L" and as: "a \<in> sconstraint k L"
  shows "norm a \<le> real CARD('n) * L"
  using as psd_eigen_ub_norm_le[OF _ _ L] by (auto simp: sconstraint_def Pi_constraint_def)

theorem bounded_sconstraint:
  assumes L: "0 \<le> L"
  shows "bounded (sconstraint k L :: (real^'n::finite^'n) set)"
  by (rule boundedI) (use sconstraint_norm_le[OF L] in blast)

section \<open>The pair path space and its coordinate processes\<close>

text \<open>Paths take values in \<open>real^'n \<times> real^'n^'n\<close>: the process together
  with its running covariation. \<open>path_law\<close>, \<open>path_metric\<close> and the
  tightness machinery are polymorphic in the value type, so the whole
  Section-2 toolchain applies verbatim.\<close>


definition exit_class ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n::finite
     \<Rightarrow> (('n pairpath) measure) set"
  where
  "exit_class k L T x = {Q.
     prob_space Q \<and>
     sets Q = sets (path_borel T :: ('n pairpath) measure) \<and>
     (AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))
          \<in> sconstraint k L) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. fst (\<omega> (min t T))) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))}"

text \<open>The class is the constrained-covariation class of
  @{theory Path_Space_Operations.Pair_Path_Laws} at the constraint set of
  Eq. (1.5): the paper contributes \<open>sconstraint k L\<close> and nothing else to the
  definition.  Everything below that reads only one clause of the class is
  the generic statement specialised through this equation.\<close>

theorem exit_class_eq_covariation:
  "exit_class k L T x = covariation_class (sconstraint k L) T x"
  by (simp add: exit_class_def covariation_class_def)

text \<open>Projections out of the definition, used throughout.\<close>

lemma exit_class_prob:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "prob_space Q"
  using Q unfolding exit_class_eq_covariation by (rule covariation_class_prob)

lemma exit_class_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  using Q unfolding exit_class_eq_covariation by (rule covariation_class_sets)

lemma exit_class_start:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  using Q unfolding exit_class_eq_covariation by (rule covariation_class_start)


lemma exit_class_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  using Q unfolding exit_class_eq_covariation by (rule covariation_class_martingale_fst)


lemma closedin_diffquot_constraint:
  fixes s t :: real
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}" and S: "closed S"
  shows "closedin (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
proof -
  have "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> topspace (mtopology_of (path_metric T :: ('n pairpath) metric)).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
    by (intro closedin_continuous_map_preimage_gen[where Y = euclidean, simplified]
        continuous_map_diffquot[OF s t] S closedin_topspace)
  then show ?thesis
    by simp
qed

text \<open>The whole difference-quotient clause, over all pairs at once, is a
  closed set too: an intersection of the closed sets above.  So it is
  measurable and passes to weak limits in one step, with no reduction to
  rational pairs.\<close>

lemma closedin_diffquot_constraint_all:
  assumes S: "closed S"
  shows "closedin (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
           (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?D = "\<lambda>(s, t). {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
  have "closedin ?X (\<Inter> (insert (topspace ?X) (?D ` {(s, t). 0 \<le> s \<and> s < t \<and> t \<le> T})))"
    by (intro closedin_Inter)
      (auto intro!: closedin_diffquot_constraint[OF _ _ S] closedin_topspace[of ?X, simplified])
  moreover have "\<Inter> (insert (topspace ?X) (?D ` {(s, t). 0 \<le> s \<and> s < t \<and> t \<le> T}))
      = {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
           (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
    by auto
  ultimately show ?thesis by simp
qed

lemma diffquot_all_sets:
  assumes S: "closed S"
  shows "{\<omega> \<in> space (path_borel T :: ('n::finite pairpath) measure).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}
    \<in> sets (path_borel T :: ('n pairpath) measure)"
  using borel_of_closed[OF closedin_diffquot_constraint_all[OF S]] by (simp add: space_borel_of)

text \<open>\<open>diffquot_all_of_rational\<close> lives in @{theory Continuous_Path_Spaces.Difference_Quotients}.\<close>


section \<open>From difference quotients to the density\<close>

text \<open>\<open>diffquot_lipschitz\<close> lives in @{theory Continuous_Path_Spaces.Difference_Quotients}.\<close>


text \<open>The density statement of Eq. (1.7): the difference-quotient constraint
  makes \<open>Y\<close> Lipschitz, hence of bounded variation, hence differentiable
  off a negligible set by \<open>Lebesgue_differentiation_thm\<close>; at every point
  of differentiability the derivative lies in the constraint set.\<close>

subsection \<open>Averages of constrained densities stay constrained\<close>

text \<open>The mathematical heart of the covariation condition, using the
  paper's Lemma 2.1: if a density takes values in a closed convex set, so
  does its average over any interval --- the difference quotient of
  \<open>Y t = \<integral>\<^sub>0\<^sup>t a\<close>. The proof is separation: an average outside \<open>S\<close>
  would be separated by a hyperplane, but the same linear functional under
  the integral cannot cross it.

  Stated for any closed convex set; the application takes
  \<open>S = sconstraint k L\<close>, whose members arrive as \<open>suff_volatile\<close>
  densities via \<open>lemma_2_1_easy\<close>.\<close>

text \<open>A market witness's volatility is a \<open>suff_volatile\<close> density with the
  \<open>eigen_ub\<close> cap; \<open>lemma_2_1_easy\<close> (the easy inclusion of Lemma 2.1)
  puts each value in \<open>sconstraint k L\<close>, and the average lemma then puts
  the difference quotient of \<open>Y t = \<integral>\<^sub>0\<^sup>t a\<close> there too.\<close>

lemma suff_volatile_cap_in_sconstraint:
  fixes a :: "real^'n::finite^'n"
  assumes sv: "a \<in> suff_volatile k" and ub: "eigen_ub a L"
  shows "a \<in> sconstraint k L"
  unfolding sconstraint_def
  using sv ub hull_subset[of "suff_volatile k"] lemma_2_1_easy by auto

subsection \<open>The constraint set is inhabited\<close>

text \<open>The paper's standing assumption \<open>L \<ge> 1\<close> (Theorem 1.1) makes the
  identity matrix admissible: \<open>\<Pi>\<^sub>m(I) = m \<ge> m - k\<close> and
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(I) = 1 \<le> L\<close>. Since (1.7)'s constraint holds for a.e.
  \<open>t \<ge> 0\<close> with the process never stopped, the bridge from a stopped
  market witness must continue its volatility past the stopping time with
  an admissible value; \<open>mat 1\<close> serves that role.\<close>


lemma Pi_proj_mat_1:
  assumes m: "m \<le> CARD('n::finite)"
  shows "real m \<le> Pi_proj (mat 1 :: real^'n^'n) m"
proof (rule Pi_proj_ge[OF m])
  fix P :: "real^'n^'n"
  assume P: "is_proj P" "trace P = real m"
  have "trace ((mat 1 :: real^'n^'n) ** P) = trace P"
    by simp
  then show "real m \<le> trace ((mat 1 :: real^'n^'n) ** P)"
    using P by simp
qed

theorem mat_1_in_sconstraint:
  assumes L: "1 \<le> L"
  shows "(mat 1 :: real^'n::finite^'n) \<in> sconstraint k L"
  unfolding sconstraint_def Pi_constraint_def
proof (intro IntI CollectI conjI allI impI psd_mat_1)
  fix m
  assume m: "k < m" "m \<le> CARD('n)"
  have "real (m - k) \<le> real m" by simp
  also have "\<dots> \<le> Pi_proj (mat 1 :: real^'n^'n) m"
    by (rule Pi_proj_mat_1[OF m(2)])
  finally show "real (m - k) \<le> Pi_proj (mat 1 :: real^'n^'n) m" .
next
  show "eigen_ub (mat 1 :: real^'n^'n) L"
    unfolding eigen_ub_def
  proof (intro allI)
    fix x :: "real^'n"
    have "x \<bullet> ((mat 1 :: real^'n^'n) *v x) = x \<bullet> x"
      by simp
    also have "\<dots> \<le> L * (x \<bullet> x)"
    proof -
      have "1 * (x \<bullet> x) \<le> L * (x \<bullet> x)"
        using L inner_ge_zero[of x] by (rule mult_right_mono)
      then show ?thesis by simp
    qed
    finally show "x \<bullet> ((mat 1 :: real^'n^'n) *v x) \<le> L * (x \<bullet> x)" .
  qed
qed

subsection \<open>Continuing a stopped volatility past its stopping time\<close>

text \<open>Per (1.7)--(1.8) the paper's processes are never stopped, so a market
  witness --- whose volatility vanishes after its stopping time --- must be
  continued to become a class member, via \<open>mat 1\<close>, admissible since
  \<open>L \<ge> 1\<close> (\<open>mat_1_in_sconstraint\<close>). The exit time \<open>\<tau>\<^sub>K\<close> is untouched:
  by (1.8) it depends only on the path up to the first exit from \<open>K\<close>.\<close>


theorem exit_class_Y_bounded_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>t\<in>{0..T}. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
proof (rule covariation_class_Y_bounded_ae[OF T])
  show "0 \<le> real CARD('n) * L" using L by simp
  show "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    by (rule sconstraint_norm_le[OF L])
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed

lemma sconstraint_diag:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> sconstraint k L"
  shows "0 \<le> a $ i $ i" and "a $ i $ i \<le> L"
proof -
  have p: "psd a" and u: "eigen_ub a L"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  show "0 \<le> a $ i $ i" by (rule psd_eigen_ub_diag(1)[OF p u])
  show "a $ i $ i \<le> L" by (rule psd_eigen_ub_diag(2)[OF p u])
qed

text \<open>The two numbers of \<open>sconstraint k L\<close> that the generic class lemmas
  read: a norm bound \<open>CARD('n) \<sqdot> L\<close> and a two-sided bound \<open>[0, L]\<close> on the
  diagonal, in the order those lemmas take them.\<close>

lemma sconstraint_bounds:
  fixes L :: real
  assumes L: "0 \<le> L"
  shows "0 \<le> real CARD('n::finite) * L"
    and "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    and "0 \<le> L"
    and "\<And>(a :: real^'n^'n) j. a \<in> sconstraint k L \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> L"
  using L sconstraint_norm_le[OF L] sconstraint_diag by auto

lemma exit_class_eval_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> borel_measurable Q"
  by (rule pair_law_eval_measurable[OF exit_class_sets[OF Q]])

lemma exit_class_Y_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ j)"
proof (rule covariation_class_Y_entry_integrable)
  show "0 \<le> real CARD('n) * L" using L by simp
  show "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    by (rule sconstraint_norm_le[OF L])
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)

lemma exit_class_compensated_martingale:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof (rule covariation_class_martingale_compensated)
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed

lemma exit_class_compensated_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
proof (rule covariation_class_compensated_integrable)
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)

lemma exit_class_compensated_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ j)"
proof (rule covariation_class_compensated_entry_integrable)
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)


theorem exit_class_sq_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
proof (rule covariation_class_sq_integrable)
  show "0 \<le> real CARD('n) * L" using L by simp
  show "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    by (rule sconstraint_norm_le[OF L])
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)

theorem exit_class_compensated_mean:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) = outerp x"
proof (rule covariation_class_compensated_mean)
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)

theorem exit_class_sq_mean_le:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T"
proof (rule covariation_class_sq_mean_le)
  show "0 \<le> real CARD('n) * L" using L by simp
  show "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    by (rule sconstraint_norm_le[OF L])
  show "Q \<in> covariation_class (sconstraint k L) T x"
    using Q unfolding exit_class_eq_covariation .
qed (use assms in auto)


text \<open>The starting point is a closed condition too: evaluation at time \<open>0\<close>
  is continuous and \<open>{(x, 0)}\<close> is closed.\<close>


lemma covariation_class_start_full_mass:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> covariation_class S T x"
  shows "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)} = 1"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule covariation_class_sets[OF Q])
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have mm: "{\<omega> \<in> space Q. \<omega> 0 = (x, 0)} \<in> sets Q"
    unfolding sp setsQ by (rule borel_of_closed[OF closedin_start_point[OF T]])
  have ae: "AE \<omega> in Q. \<omega> 0 = (x, 0)"
    using covariation_class_start[OF Q] by (rule eventually_mono) (simp add: prod_eq_iff)
  show ?thesis using P.prob_Collect_eq_1[OF mm] ae unfolding sp by blast
qed

subsection \<open>Both closed clauses pass to the weak limit\<close>

text \<open>Both clauses are closed sets of paths
  (@{thm [source] closedin_start_point},
  @{thm [source] closedin_diffquot_constraint_all}), so portmanteau
  (@{thm [source] weak_conv_closed_full_measure}) carries each to the weak
  limit.\<close>

theorem covariation_class_start_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T"
    and mem: "\<And>i. Qi i \<in> covariation_class S T x"
    and wc: "weak_conv_on Qi Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  interpret P: prob_space Q by (rule prob)
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have mm: "{\<omega> \<in> space Q. \<omega> 0 = (x, 0)} \<in> sets Q"
    unfolding sp setsQ by (rule borel_of_closed[OF closedin_start_point[OF T]])
  have "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)} = 1"
  proof (rule weak_conv_closed_full_measure[OF wc closedin_start_point[OF T]])
    show "prob_space Q" by (rule prob)
    show "\<And>i. measure (Qi i)
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). \<omega> 0 = (x, 0)} = 1"
      by (rule covariation_class_start_full_mass[OF T mem])
  qed
  then have "AE \<omega> in Q. \<omega> 0 = (x, 0)"
    using P.prob_Collect_eq_1[OF mm] unfolding sp by blast
  then show ?thesis by (rule eventually_mono) (simp add: prod_eq_iff)
qed

theorem covariation_class_diffquot_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes S: "closed S" and mem: "\<And>i. Qi i \<in> covariation_class S T x"
    and wc: "weak_conv_on Qi Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S"
proof -
  let ?D = "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S}"
  have iff: "(AE \<omega> in M. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S)
      \<longleftrightarrow> measure M ?D = 1"
    if M: "prob_space M" "sets M = sets (path_borel T :: ('n pairpath) measure)"
    for M :: "('n pairpath) measure"
  proof -
    interpret P: prob_space M by (rule M(1))
    have sp: "space M = mspace (path_metric T :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF M(2)])
    have "{\<omega> \<in> space M. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> S} \<in> sets M"
      unfolding M(2) sets_eq_imp_space_eq[OF M(2)] by (rule diffquot_all_sets[OF S])
    from P.prob_Collect_eq_1[OF this] show ?thesis unfolding sp by blast
  qed
  have "measure Q ?D = 1"
  proof (rule weak_conv_closed_full_measure
      [OF wc closedin_diffquot_constraint_all[OF S] _ prob])
    show "measure (Qi i) ?D = 1" for i
      using iff[OF covariation_class_prob[OF mem[of i]] covariation_class_sets[OF mem[of i]]]
        covariation_class_diffquot[OF mem[of i]] by blast
  qed
  then show ?thesis using iff[OF prob setsQ] by simp
qed

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition exit_val ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "exit_val k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` exit_class k L T x)"

text \<open>Eq. (1.6) is the generic value functional at the constraint set of
  Eq. (1.5); and it is monotone in that set, which is the shape in which a
  reader can compare this problem with a differently constrained one.\<close>

theorem exit_val_eq_covariation_val:
  "exit_val k L T K x = covariation_val (sconstraint k L) T K x"
  by (simp add: exit_val_def covariation_val_def exit_class_eq_covariation)

(*<*)
end
(*>*)
