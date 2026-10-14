section \<open>The control problem of Eqs. (1.5)--(1.7)\<close>

(*<*)
theory Control_Problem
  imports
    "Relative_Arbitrage_Equation.Constraint_Set_Convexity" "Relative_Arbitrage_Equation.Operator_Formula"
    "Covariation_Constrained_Martingales.Covariation_Class_Optimizer"
begin

(*>*)

text \<open>
  The constraint set of Eq. (1.5), the class of Eq. (1.7) and the value
  function of Eq. (1.6), at a finite horizon, with the compactness of the
  class.  The class \<open>P\<^sub>x\<close> of Eq. (1.7) is encoded as laws of the pair
  \<open>(X, \<langle>X\<rangle>)\<close> on the path space, following the paper's own proof of
  Lemma 2.3. The covariation is carried as a second, uniformly Lipschitz
  path component whose difference quotients lie in the compact convex
  constraint set \<open>S = Pi_constraint k \<inter> {eigen_ub L}\<close>. Lemma 2.1, in
  the exact form \<open>lemma_2_1_exact\<close>, identifies \<open>S\<close> with the convex hull
  of the unconvexified sufficient-volatility set of Eq. (1.4).\<close>

section \<open>The constraint set of Eq. (1.5) with the technical cap\<close>

definition sconstraint :: "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite^'n) set" where
  "sconstraint k L = Pi_constraint k \<inter> {a. eigen_ub a L}"

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

section \<open>The class of Eq. (1.7) on the pair path space\<close>

text \<open>Paths take values in \<open>real^'n \<times> real^'n^'n\<close>: the process together
  with its running covariation.  \<open>path_law\<close>, \<open>path_metric\<close> and the
  tightness results are polymorphic in the value type, so they apply to
  this path space as they stand.\<close>


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

section \<open>Members of the constraint set\<close>

text \<open>The class constrains the difference quotients of the covariation, while
  Eq. (1.7) constrains its density.  For a closed, convex and bounded
  constraint set the two readings are the same (\<open>dq_iff_density\<close>, in the
  session \<open>Covariation_Constrained_Martingales\<close>).  A density value is
  admissible when it lies in \<open>sconstraint k L\<close>, and by the easy inclusion of
  Lemma 2.1 (\<open>lemma_2_1_easy\<close>) every sufficiently volatile matrix with the
  \<open>eigen_ub\<close> cap does.\<close>

lemma suff_volatile_cap_in_sconstraint:
  fixes a :: "real^'n::finite^'n"
  assumes sv: "a \<in> suff_volatile k" and ub: "eigen_ub a L"
  shows "a \<in> sconstraint k L"
  unfolding sconstraint_def
  using sv ub hull_subset[of "suff_volatile k"] lemma_2_1_easy by auto

subsection \<open>The constraint set is inhabited\<close>

text \<open>The paper's standing assumption \<open>L \<ge> 1\<close> (Theorem 1.1) makes the
  identity matrix admissible: \<open>\<Pi>\<^sub>m(I) = m \<ge> m - k\<close> and
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(I) = 1 \<le> L\<close>.\<close>

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

text \<open>In the form the generic class lemmas read it: they ask for some
  \<open>\<sigma> \<sigma>\<^sup>T\<close> in the constraint set, a constant volatility from which they
  build members of the class, and the identity is \<open>\<sigma> \<sigma>\<^sup>T\<close> for \<open>\<sigma> = I\<close>.\<close>

lemma mat_1_rate_in_sconstraint:
  assumes L: "1 \<le> L"
  shows "mat 1 ** transpose (mat 1) \<in> (sconstraint k L :: (real^'n::finite^'n) set)"
  using mat_1_in_sconstraint[OF L] by simp

subsection \<open>Bounds on the entries\<close>

text \<open>A member of \<open>sconstraint k L\<close> is positive semidefinite with largest
  eigenvalue at most \<open>L\<close>, so its diagonal entries lie in \<open>[0, L]\<close>.\<close>


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

lemma sconstraint_psd_entry:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> sconstraint k L"
  shows "psd a" and "\<bar>a $ i $ j\<bar> \<le> L"
proof -
  have p: "psd a" and u: "eigen_ub a L"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  show "psd a" by (rule p)
  show "\<bar>a $ i $ j\<bar> \<le> L" by (rule psd_eigen_ub_entry_abs_le[OF p u])
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

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition exit_val ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "exit_val k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` exit_class k L T x)"

text \<open>Eq. (1.6) is the generic value functional at the constraint set of
  Eq. (1.5).  Through this equation, the monotonicity of that functional in the
  constraint set (\<open>covariation_val_mono_class\<close>) compares this problem with a
  differently constrained one.\<close>

theorem exit_val_eq_covariation_val:
  "exit_val k L T K x = covariation_val (sconstraint k L) T K x"
  by (simp add: exit_val_def covariation_val_def exit_class_eq_covariation)

section \<open>The class at the constraint set of Eq. (1.5)\<close>

text \<open>The results of the session \<open>Covariation_Constrained_Martingales\<close>
  for an abstract constraint set, at \<open>sconstraint k L\<close>, which supplies their
  norm bound \<open>CARD('n) \<sqdot> L\<close> and diagonal bound \<open>[0, L]\<close>
  (@{thm [source] sconstraint_bounds}): the fourth moment of the increments
  with the paper's constant \<open>8L\<^sup>2\<close>, and the closedness and tightness behind
  Lemma 2.3.\<close>

theorem exit_class_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
  by (rule covariation_class_fourth_moment[OF T sconstraint_bounds[OF L] setsQ
        Q[unfolded exit_class_eq_covariation] st stt ttT])

theorem exit_class_weak_closed:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "Q \<in> exit_class k L T x"
  unfolding exit_class_eq_covariation
  by (rule covariation_class_weak_closed[OF T sconstraint_bounds[OF L] closed_sconstraint
        mem[unfolded exit_class_eq_covariation] wc prob setsQ])

theorem tight_on_set_paper_pair_class:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> N \<in> exit_class k L T x"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
  by (rule covariation_class_tight_on_set[OF T sconstraint_bounds[OF L]
        mem[unfolded exit_class_eq_covariation]])

text \<open>For the paper's constraint set this is Lemma 2.3's compactness.\<close>

theorem exit_class_compactin_weak:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (exit_class k L T x)"
  unfolding exit_class_eq_covariation
  by (rule covariation_class_compactin_weak[OF T sconstraint_bounds[OF L] closed_sconstraint])

text \<open>The paper's constraint set carries
  \<open>\<theta> = n - k\<close>: the identity is a rank-\<open>n\<close> projection, so
  \<open>Pi_proj a n \<le> trace a\<close>, and the constraint's own bound at \<open>m = n\<close> is
  \<open>n - k\<close>.\<close>

lemma sconstraint_trace_ge:
  fixes a :: "real^'n::finite^'n"
  assumes k: "k < CARD('n)" and a: "a \<in> sconstraint k L"
  shows "real (CARD('n) - k) \<le> trace a"
proof -
  have p: "psd a"
    and pi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> real (m - k) \<le> Pi_proj a m"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  have "real (CARD('n) - k) \<le> Pi_proj a CARD('n)" using k by (intro pi) auto
  also have "\<dots> \<le> trace (a ** mat 1)"
    by (rule Pi_proj_le[OF p]) (simp_all add: is_proj_def trace_I)
  also have "\<dots> = trace a" by simp
  finally show ?thesis .
qed

text \<open>The two numbers of \<open>sconstraint k L\<close> that the exit-time estimates read:
  the norm bound \<open>CARD('n) \<sqdot> L\<close> and the trace lower bound \<open>n - k\<close>, in the
  order those lemmas take them.  The trace lower bound is the rate in the
  expected exit-time bound of Eq. (3.10).\<close>

lemma sconstraint_trace_bounds:
  fixes L :: real
  assumes k: "k < CARD('n::finite)" and L: "0 \<le> L"
  shows "0 \<le> real CARD('n) * L"
    and "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> norm a \<le> real CARD('n) * L"
    and "0 < real (CARD('n) - k)"
    and "\<And>a :: real^'n^'n. a \<in> sconstraint k L \<Longrightarrow> real (CARD('n) - k) \<le> trace a"
  using sconstraint_bounds(1,2)[OF L] k sconstraint_trace_ge[OF k] by auto

(*<*)
end
(*>*)
