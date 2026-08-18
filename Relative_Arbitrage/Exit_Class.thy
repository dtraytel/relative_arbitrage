
(*<*)
theory Exit_Class
  imports "Continuous_Path_Spaces.Path_Space" "Continuous_Path_Spaces.Path_Tightness" Exit_Semicontinuity Operator_Formula
    Viscosity_Solutions "Continuous_Time_Martingales.Martingale_Algebra"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
    "Continuous_Path_Spaces.Holder_Interpolation"
    "Continuous_Path_Spaces.Increment_Moments"
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

text \<open>For a psd matrix the eigenvalue cap bounds every entry: the diagonal
  directly (test on \<open>axis i 1\<close>), the off-diagonal by the psd inequality on
  \<open>axis i 1 \<plusminus> axis j 1\<close> (a two-sided form of Cauchy--Schwarz).\<close>

lemma psd_eigen_ub_diag:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and ub: "eigen_ub a L"
  shows "0 \<le> a $ i $ i" and "a $ i $ i \<le> L"
proof -
  have q: "axis i (1 :: real) \<bullet> (a *v axis i (1 :: real)) = a $ i $ i"
    by (simp add: inner_axis_one matrix_vector_axis_one)
  have nn: "axis i (1 :: real) \<bullet> axis i (1 :: real) = 1"
    unfolding inner_axis_one by (simp add: axis_def)
  show "0 \<le> a $ i $ i"
    using a[unfolded psd_def, THEN conjunct2, rule_format, of "axis i 1"] q
    by simp
  have "a $ i $ i \<le> L * (axis i (1 :: real) \<bullet> axis i (1 :: real))"
    using ub[unfolded eigen_ub_def, rule_format, of "axis i 1"] q by simp
  then show "a $ i $ i \<le> L" unfolding nn by simp
qed

lemma psd_eigen_ub_entry_abs_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and ub: "eigen_ub a L"
  shows "\<bar>a $ i $ j\<bar> \<le> L"
proof -
  have sym: "transpose a = a" using a by (simp add: psd_def)
  have psda: "0 \<le> x \<bullet> (a *v x)" for x using a by (simp add: psd_def)
  have dii: "a $ i $ i \<le> L" and djj: "a $ j $ j \<le> L"
    by (rule psd_eigen_ub_diag(2)[OF a ub])+
  have plus: "0 \<le> a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    using psda[of "axis i 1 + axis j 1"]
    unfolding quadform_axis_pair[OF sym] .
  have minus: "0 \<le> a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    using psda[of "axis i 1 - axis j 1"]
    unfolding quadform_axis_pair_minus[OF sym] .
  have "2 * \<bar>a $ i $ j\<bar> \<le> a $ i $ i + a $ j $ j"
    using plus minus by (simp add: abs_le_iff)
  also have "\<dots> \<le> 2 * L" using dii djj by simp
  finally show ?thesis by simp
qed

theorem sconstraint_norm_le:
  fixes a :: "real^'n::finite^'n"
  assumes L: "0 \<le> L" and as: "a \<in> sconstraint k L"
  shows "norm a \<le> real CARD('n) * L"
proof -
  have a: "psd a" and ub: "eigen_ub a L"
    using as by (auto simp: sconstraint_def Pi_constraint_def)
  have entry: "\<bar>a $ i $ j\<bar> \<le> L" for i j
    by (rule psd_eigen_ub_entry_abs_le[OF a ub])
  have sq: "a \<bullet> a \<le> (real CARD('n) * L)^2"
  proof -
    have "a \<bullet> a = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). a $ i $ j * a $ i $ j)"
      unfolding inner_vec_def by simp
    also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). L * L)"
    proof (intro sum_mono)
      fix i j :: 'n
      have "a $ i $ j * a $ i $ j = \<bar>a $ i $ j\<bar> * \<bar>a $ i $ j\<bar>"
        by (simp add: abs_mult[symmetric])
      also have "\<dots> \<le> L * L"
        using entry[of i j] by (intro mult_mono) auto
      finally show "a $ i $ j * a $ i $ j \<le> L * L" .
    qed
    also have "\<dots> = (real CARD('n) * L)^2"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have "norm a = sqrt (a \<bullet> a)" by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> \<le> sqrt ((real CARD('n) * L)^2)"
    using sq by (intro real_sqrt_le_mono)
  also have "\<dots> = real CARD('n) * L"
    using L by simp
  finally show "norm a \<le> real CARD('n) * L" .
qed

theorem bounded_sconstraint:
  assumes L: "0 \<le> L"
  shows "bounded (sconstraint k L :: (real^'n::finite^'n) set)"
  by (rule boundedI) (use sconstraint_norm_le[OF L] in blast)

section \<open>The pair path space and its coordinate processes\<close>

text \<open>Paths take values in \<open>real^'n \<times> real^'n^'n\<close>: the process together
  with its running covariation. \<open>path_law\<close>, \<open>path_metric\<close> and the
  tightness machinery are polymorphic in the value type, so the whole
  Section-2 toolchain applies verbatim.\<close>

definition outerp :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "outerp x = (\<chi> i j. x $ i * x $ j)"

type_synonym 'n pairpath = "real \<Rightarrow> (real^'n) \<times> (real^'n^'n)"

abbreviation pairX :: "real \<Rightarrow> ('n::finite) pairpath \<Rightarrow> real^'n"
  where "pairX t \<omega> \<equiv> fst (\<omega> t)"

abbreviation pairY :: "real \<Rightarrow> ('n::finite) pairpath \<Rightarrow> real^'n^'n"
  where "pairY t \<omega> \<equiv> snd (\<omega> t)"

section \<open>The class \<open>P\<^sub>x\<close> of Eq. (1.7), capped at horizon \<open>T\<close>\<close>

text \<open>Operational reading of (1.7), equivalent by compensator uniqueness: a
  law of \<open>(X, Y)\<close> where \<open>X\<close> is a martingale from \<open>x\<close>, \<open>Y\<close> starts at \<open>0\<close>
  with difference quotients in the constraint set (so \<open>Y\<close> is Lipschitz and
  a.e. differentiable into \<open>S\<close>), and \<open>X X\<^sup>T - Y\<close> is a martingale, making
  \<open>Y\<close> the quadratic covariation. The cap at \<open>T\<close> is invisible once \<open>T\<close>
  exceeds the uniform exit-time bound (Lemma 1.9 / Eq. (3.10)).

  The martingale clauses must stop the process at \<open>T\<close>: points of
  \<^term>\<open>mspace (path_metric T)\<close> are extensional on \<open>{0..T}\<close>, so an
  unstopped clause would force the coordinate process to be almost surely
  constant, emptying the class for every \<open>T > 0\<close>. Stopping at \<open>T\<close>
  captures exactly (1.7) on \<open>[0,T]\<close>.\<close>

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

text \<open>Projections out of the definition, used throughout.\<close>

lemma exit_class_prob:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "prob_space Q"
  using Q unfolding exit_class_def by blast

lemma exit_class_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  using Q unfolding exit_class_def by blast

lemma space_of_path_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "space Q = mspace (path_metric T :: ('n pairpath) metric)"
  using sets_eq_imp_space_eq[OF assms] by (simp add: space_borel_of)

section \<open>The constraint passes to weak limits, without Skorokhod\<close>

text \<open>The paper passes the covariation constraint to the limit law via
  Skorokhod's representation theorem; this instead uses the closed-set half
  of the portmanteau theorem (\<open>weak_conv_closed_full_mass\<close>). For fixed
  times \<open>s < t\<close> the difference quotient is a continuous function of the
  path and the constraint set is closed, so
  \<open>{\<omega>. (Y t \<omega> - Y s \<omega>)/(t - s) \<in> S}\<close> is closed and has full mass under
  every approximating law, hence under the limit.\<close>

lemma continuous_map_diffquot:
  fixes s t :: real
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}"
  shows "continuous_map (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      euclidean (\<lambda>\<omega>. (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
proof -
  have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  moreover have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> s)"
    by (rule continuous_map_path_eval[OF s])
  moreover have sndc:
    "continuous_map euclidean euclidean
       (snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)"
    by (simp add: continuous_on_snd)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s))"
    by (intro continuous_map_diff)
      (auto intro: continuous_map_compose[OF _ sndc, unfolded o_def])
  moreover have scl: "continuous_map euclidean euclidean
      (\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)"
    by (simp add:
        continuous_on_scaleR)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      ((\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)
        \<circ> (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s)))"
    by (intro continuous_map_compose)
  then show ?thesis by (simp add: o_def)
qed

lemma closedin_diffquot_constraint:
  fixes s t :: real
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}"
  shows "closedin (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L}"
proof -
  have "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> topspace (mtopology_of (path_metric T :: ('n pairpath) metric)).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L}"
    by (intro closedin_continuous_map_preimage_gen[where Y = euclidean, simplified]
        continuous_map_diffquot[OF s t] closed_sconstraint closedin_topspace)
  then show ?thesis
    by simp
qed

text \<open>\<open>diffquot_all_of_rational\<close> lives in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>


section \<open>From difference quotients to the density\<close>

text \<open>\<open>diffquot_lipschitz\<close> lives in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>


text \<open>The density statement of Eq. (1.7): the difference-quotient constraint
  makes \<open>Y\<close> Lipschitz, hence of bounded variation, hence differentiable
  off a negligible set by \<open>Lebesgue_differentiation_thm\<close>; at every point
  of differentiability the derivative lies in the constraint set.\<close>

text \<open>The weak-limit transfer itself: a single difference-quotient
  constraint, holding almost surely under every approximating law, holds
  almost surely under the weak limit. (The a.s. statements are read as
  full mass of the closed set, which is how the class is phrased.)\<close>

theorem diffquot_constraint_weak_limit:
  fixes \<Lambda>i :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and \<Lambda> :: "('n pairpath) measure"
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}"
    and wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and probs: "\<And>i. prob_space (\<Lambda>i i)" and prob: "prob_space \<Lambda>"
    and full: "\<And>i. measure (\<Lambda>i i)
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L} = 1"
  shows "measure \<Lambda>
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L} = 1"
  by (rule weak_conv_closed_full_mass
      [OF wc closedin_diffquot_constraint[OF s t] probs prob full])

subsection \<open>Averages of constrained densities stay constrained\<close>

text \<open>The mathematical heart of the covariation condition, using the
  paper's Lemma 2.1: if a density takes values in a closed convex set, so
  does its average over any interval --- the difference quotient of
  \<open>Y t = \<integral>₀ᵗ a\<close>. The proof is separation: an average outside \<open>S\<close>
  would be separated by a hyperplane, but the same linear functional under
  the integral cannot cross it.

  Stated for any closed convex set; the application takes
  \<open>S = sconstraint k L\<close>, whose members arrive as \<open>suff_volatile\<close>
  densities via \<open>lemma_2_1_easy\<close>.\<close>

text \<open>A market witness's volatility is a \<open>suff_volatile\<close> density with the
  \<open>eigen_ub\<close> cap; \<open>lemma_2_1_easy\<close> (the easy inclusion of Lemma 2.1)
  puts each value in \<open>sconstraint k L\<close>, and the average lemma then puts
  the difference quotient of \<open>Y t = \<integral>₀ᵗ a\<close> there too.\<close>

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

lemma psd_mat_1: "psd (mat 1 :: real^'n::finite^'n)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (mat 1 :: real^'n^'n) = mat 1"
    by simp
  fix x :: "real^'n"
  show "0 \<le> x \<bullet> (mat 1 *v x)"
    by simp
qed

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

definition acont :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "acont a tv s = (if s \<le> tv then a s else mat 1)"

text \<open>Time-measurability is inherited by the continuation: the locale
  assumption \<open>acov_time_measurable\<close> is stated on the nonnegative axis
  only, matching (1.7)'s "a.e. \<open>t \<ge> 0\<close>", and nothing more is available
  since for \<open>u < 0 \<le> tv\<close> the continuation still reads \<open>a u\<close>.

  A trap: \<^const>\<open>lborel\<close> is polymorphic and \<^typ>\<open>real^'n^'n\<close> carries
  an \<^class>\<open>ord\<close> instance, so an unannotated binder in
  \<open>(\<lambda>u. \<dots>) \<in> borel_measurable lborel\<close> can silently elaborate at the
  matrix type instead of \<open>real\<close>. Pin \<open>lborel :: real measure\<close> and
  annotate every binder.\<close>

lemma acont_set_borel_measurable:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes a: "set_borel_measurable lborel {0..} a"
  shows "set_borel_measurable lborel {0..} (acont a tv)"
proof -
  have "(\<lambda>u::real. indicat_real {0..} u *\<^sub>R acont a tv u)
      = (\<lambda>u::real. if u \<le> tv then indicat_real {0..} u *\<^sub>R a u
             else (if u < 0 then 0 else (mat 1 :: real^'n^'n)))"
    by (rule ext) (simp add: acont_def)
  moreover have "(\<lambda>u::real. if u \<le> tv then indicat_real {0..} u *\<^sub>R a u
             else (if u < 0 then 0 else (mat 1 :: real^'n^'n)))
      \<in> borel_measurable (lborel :: real measure)"
  proof (rule measurable_If)
    show "(\<lambda>u::real. indicat_real {0..} u *\<^sub>R a u)
        \<in> borel_measurable (lborel :: real measure)"
      using a unfolding set_borel_measurable_def .
    \<comment> \<open>the \<^verbatim>\<open>if u < 0\<close> form, not an indicator: the \<open>measurable\<close>
        method reduces the branch condition to \<open>open {..<0}\<close>, whereas the
        indicator form leaves the FALSE goal \<open>open {0..}\<close>.\<close>
    show "(\<lambda>u::real. if u < 0 then 0 else (mat 1 :: real^'n^'n))
        \<in> borel_measurable (lborel :: real measure)"
      by measurable
    show "{u \<in> space (lborel :: real measure). u \<le> tv} \<in> sets lborel"
      by simp
  qed
  ultimately show ?thesis unfolding set_borel_measurable_def by simp
qed

text \<open>Hence the continued volatility has all its difference quotients in the
  constraint set --- which is exactly the covariation condition of
  \<open>exit_class\<close>, holding for every \<open>0 \<le> s < t\<close> with no stopping
  caveat, as (1.7) demands.\<close>

subsection \<open>The running covariation built from a continued volatility\<close>

text \<open>The volatility side of the bridge: \<open>Yint a t = \<integral>₀ᵗ a\<close> starts at
  \<open>0\<close>, has increments given by interval integrals, and --- for the
  continued density --- difference quotients in the constraint set for every
  \<open>0 \<le> s < t\<close>: the covariation half of \<open>exit_class\<close>.\<close>

definition Yint :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "Yint a t = set_lebesgue_integral lborel {0..t} a"

subsection \<open>What the class gives the tightness argument for free\<close>

text \<open>The \<open>Y\<close>-side of the pair tightness costs nothing: the class's
  difference quotients lie a.s. in \<open>sconstraint k L\<close>, whose elements have
  norm at most \<open>n\<sqdot>L\<close> (\<open>sconstraint_norm_le\<close>), so \<open>diffquot_lipschitz\<close>
  makes \<open>Y\<close> a.s. \<open>n\<sqdot>L\<close>-Lipschitz --- the \<open>Y\<close>-event of
  \<open>pair_holder_charge_split\<close> with probability one, leaving only the
  \<open>X\<close>-side Hoelder estimate.\<close>

theorem exit_class_lipschitz_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. (real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  have B0: "0 \<le> real CARD('n) * L" using L by simp
  show ?thesis
  proof (rule AE_mp[OF dq], rule AE_I2, intro impI)
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    show "(real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    proof (rule diffquot_lipschitz[OF B0])
      fix a :: "real^'n^'n"
      assume "a \<in> sconstraint k L"
      then show "norm a \<le> real CARD('n) * L"
        by (rule sconstraint_norm_le[OF L])
    next
      fix s t :: real
      assume "0 \<le> s" "s < t" "t \<le> T"
      then show "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
        using q by blast
    qed
  qed
qed

text \<open>Combined with the difference-quotient-to-density transfer, the class
  member's \<open>Y\<close> is almost surely differentiable off a negligible set of
  times with derivative in the constraint set --- the density statement of
  Eq. (1.7), stated for the class itself rather than for a bare path.\<close>

text \<open>On the capped horizon the second component of a class member is
  uniformly bounded, almost surely, by \<open>n\<sqdot>L\<sqdot>T\<close>: it starts at \<open>0\<close> and is
  \<open>n\<sqdot>L\<close>-Lipschitz, so no probabilistic input is needed. This is what
  makes \<open>X\<close> square-integrable under a class law: the martingale clause
  makes \<open>outerp X - Y\<close> integrable, and \<open>Y\<close> being bounded transfers the
  integrability to \<open>outerp X\<close>.\<close>

theorem exit_class_Y_bounded_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>t\<in>{0..T}. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
proof -
  have B0: "0 \<le> real CARD('n) * L" using L by simp
  have z0: "(0::real) \<in> {0..T}" using T by simp
  have lip: "AE \<omega> in Q. (real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule exit_class_lipschitz_ae[OF T L Q])
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  from lip st show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have lp: "(real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
      and z: "snd (\<omega> 0) = 0" by blast+
    show ?case
    proof (intro ballI)
      fix t :: real assume t: "t \<in> {0..T}"
      have "norm (snd (\<omega> t)) = dist (snd (\<omega> t)) (snd (\<omega> 0))"
        using z by (simp add: dist_norm)
      also have "\<dots> \<le> real CARD('n) * L * dist t 0"
        by (rule lipschitz_onD[OF lp t z0])
      also have "\<dots> = real CARD('n) * L * t"
        using t by (simp add: dist_real_def)
      also have "\<dots> \<le> real CARD('n) * L * T"
        using t B0 by (intro mult_left_mono) auto
      finally show "norm (snd (\<omega> t)) \<le> real CARD('n) * L * T" .
    qed
  qed
qed

text \<open>The diagonal form of the covariation clause, which is what a
  compensator bound asks for: the \<open>(i,i)\<close> entry of \<open>Y\<close> increases, at
  rate at most \<open>L\<close>. Both halves come from the constraint set --- \<open>psd\<close>
  gives the lower bound on a diagonal entry and \<open>eigen_ub\<close> the upper one
  (\<open>psd_eigen_ub_diag\<close>).\<close>

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

theorem exit_class_Y_diag_increment:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes L: "0 \<le> L" and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
      0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
      \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  from dq show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    show "\<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
        0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
        \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
    proof (intro allI impI)
      fix s t :: real
      assume s: "0 \<le> s" and st: "s \<le> t" and tT: "t \<le> T"
      show "0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
          \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
      proof (cases "s = t")
        case True
        then show ?thesis using L by simp
      next
        case False
        then have lt: "s < t" using st by simp
        have d0: "0 < t - s" using lt by simp
        have mem: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
          using h s lt tT by blast
        have ent: "((1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))) $ i $ i
            = (snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s)"
          by simp
        have nn: "0 \<le> (snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s)"
          using sconstraint_diag(1)[OF mem] ent by simp
        have ub: "(snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s) \<le> L"
          using sconstraint_diag(2)[OF mem] ent by simp
        have p1: "0 \<le> ((snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s))
            * (t - s)"
          using nn d0 by (intro mult_nonneg_nonneg) auto
        have p2: "((snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i) / (t - s))
            * (t - s) \<le> L * (t - s)"
          using ub d0 by (intro mult_right_mono) auto
        show ?thesis using p1 p2 d0 by simp
      qed
    qed
  qed
qed

subsection \<open>Square integrability of the class member's process\<close>

text \<open>Under a class law the coordinate process is square integrable on the
  capped horizon, though not from a uniform bound on \<open>X\<close> --- the paper's
  processes are neither stopped nor confined ((1.7)--(1.8)). Instead:
  \<open>outerp X - Y\<close> is integrable by the martingale clause, \<open>Y\<close> is bounded
  (\<open>exit_class_Y_bounded_ae\<close>), and their sum \<open>outerp X\<close> has the
  squared coordinates as diagonal entries.\<close>

lemma exit_class_eval_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> borel_measurable Q"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> (path_borel T :: ('n pairpath) measure) \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF t]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF exit_class_sets[OF Q] refl] by blast
qed

lemma exit_class_Y_entry_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. snd (\<omega> t) $ i $ j) \<in> borel_measurable Q"
proof (rule measurable_compose[OF exit_class_eval_measurable[OF Q t]])
  have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  \<comment> \<open>\<^verbatim>\<open>borel_measurable_nth\<close> is only the REAL-valued instance
      \<open>real^'n \<Rightarrow> real\<close>; the matrix row map needs the linear-continuity
      route.\<close>
  have n1: "(\<lambda>v :: real^'n^'n. v $ i) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have n2: "(\<lambda>v :: real^'n. v $ j) \<in> borel_measurable borel"
    by (rule borel_measurable_nth)
  show "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). snd p $ i $ j)
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
qed

lemma exit_class_Y_entry_bound_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "AE \<omega> in Q. norm (snd (\<omega> t) $ i $ j) \<le> real CARD('n) * L * T"
proof -
  have "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    by (rule exit_class_Y_bounded_ae[OF T L Q])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    then have b: "norm (snd (\<omega> t)) \<le> real CARD('n) * L * T" using t by blast
    have "norm (snd (\<omega> t) $ i $ j) \<le> norm (snd (\<omega> t) $ i)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm (snd (\<omega> t))"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    finally show "norm (snd (\<omega> t) $ i $ j) \<le> real CARD('n) * L * T"
      using b by simp
  qed
qed

lemma exit_class_Y_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ j)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  show ?thesis
    by (rule P.integrable_const_bound
        [OF exit_class_Y_entry_bound_ae[OF T L Q t]
            exit_class_Y_entry_measurable[OF Q t]])
qed

lemma exit_class_compensated_martingale:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  using Q unfolding exit_class_def by blast

lemma exit_class_compensated_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule exit_class_compensated_martingale[OF Q])
  have "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
    using t by (intro MG.integrable) simp
  then show ?thesis using t by simp
qed

lemma exit_class_compensated_entry_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ j)"
  by (rule integrable_bounded_linear[OF bounded_linear_vec_nth,
        OF integrable_bounded_linear[OF bounded_linear_vec_nth
          exit_class_compensated_integrable[OF Q t]]])

text \<open>Squaring the coordinate is the diagonal entry of \<open>outerp\<close>, so the
  split of \<open>(X\<^sub>t $ i)\<^sup>2\<close> into the compensated part plus \<open>Y\<close> is an
  identity of functions, not an inequality.\<close>

lemma sq_coord_split:
  fixes v :: "real^'n::finite" and w :: "real^'n^'n"
  shows "(v $ i)\<^sup>2 = (outerp v - w) $ i $ i + w $ i $ i"
  by (simp add: outerp_def power2_eq_square)

theorem exit_class_sq_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
proof -
  have t0: "0 \<le> t" using t by simp
  have eq: "(\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i + snd (\<omega> t) $ i $ i)"
    by (rule ext) (rule sq_coord_split)
  show ?thesis
    unfolding eq
    by (rule Bochner_Integration.integrable_add
        [OF exit_class_compensated_entry_integrable[OF Q t]
            exit_class_Y_entry_integrable[OF T L Q t]])
qed

subsection \<open>The uniform \<open>L\<^sup>2\<close> bound on the class\<close>

text \<open>The uniform bound the weak-limit machinery needs, from a martingale's
  constant mean: \<open>E[outerp X\<^sub>t - Y\<^sub>t] = outerp x\<close>, whose diagonal entry
  is \<open>(x $ i)\<^sup>2 - E[Y\<^sub>t $ i $ i]\<close>. Since \<open>Y\<close> is bounded by \<open>n\<sqdot>L\<sqdot>T\<close>,
  the second moments are bounded uniformly over the class --- the hypothesis
  of \<open>unif_integrable_of_L2_bound\<close>.\<close>

text \<open>\<open>integral_of_bounded_linear\<close>, \<open>set_integral_of_bounded_linear\<close>,
  \<open>martingale_bounded_linear_image\<close>, \<open>martingale_vec_nth\<close> and
  \<open>martingale_mat_nth\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

theorem exit_class_compensated_mean:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) = outerp x"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule exit_class_compensated_martingale[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by simp_all
  have z: "(0::real) \<in> {0..T}" using t by simp
  have i0: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0))"
    by (rule exit_class_compensated_integrable[OF Q z])
  have it: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  \<comment> \<open>the whole space is in the filtration at time \<open>0\<close>, so the martingale's
      set-integral identity there IS constancy of the mean.\<close>
  have top: "space Q \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0)"
    using sets.top[of "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0"]
    by simp
  have const: "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q)
      = (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
    using MG.set_integral_eq[OF top order.refl t0] t0 tT
    by (simp add: set_integral_space[OF i0] set_integral_space[OF it])
  have start: "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q) = outerp x"
  proof -
    have ae: "AE \<omega> in Q. outerp (fst (\<omega> 0)) - snd (\<omega> 0) = outerp x"
    proof -
      have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
        using Q unfolding exit_class_def by blast
      then show ?thesis by (rule eventually_mono) simp
    qed
    have "(\<integral>\<omega>. outerp (fst (\<omega> 0)) - snd (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. outerp x \<partial>Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0] _ ae])
        measurable
    then show ?thesis by (simp add: P.prob_space)
  qed
  from const start show ?thesis by simp
qed

theorem exit_class_sq_mean_le:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have t0: "0 \<le> t" using t by simp
  have iA: "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i)"
    by (rule exit_class_compensated_entry_integrable[OF Q t])
  have iB: "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ i)"
    by (rule exit_class_Y_entry_integrable[OF T L Q t])
  have eq: "(\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i + snd (\<omega> t) $ i $ i)"
    by (rule ext) (rule sq_coord_split)
  have split: "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
      = (\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
        + (\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q)"
    unfolding eq by (rule Bochner_Integration.integral_add[OF iA iB])
  \<comment> \<open>the compensated part: pull the two \<open>$\<close> projections, both bounded
      linear, out through the integral, then apply the mean identity.\<close>
  have partA: "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
      = (x $ i)\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i \<partial>Q)
        = (\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i \<partial>Q) $ i"
      by (rule integral_of_bounded_linear[OF bounded_linear_vec_nth]
          , rule integrable_bounded_linear[OF bounded_linear_vec_nth])
        (rule exit_class_compensated_integrable[OF Q t])
    also have "(\<integral>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i \<partial>Q)
        = (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) $ i"
      by (rule integral_of_bounded_linear[OF bounded_linear_vec_nth
            exit_class_compensated_integrable[OF Q t]])
    also have "(\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q) = outerp x"
      by (rule exit_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: outerp_def power2_eq_square)
  qed
  have partB: "(\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q) \<le> real CARD('n) * L * T"
  proof -
    have "(\<integral>\<omega>. snd (\<omega> t) $ i $ i \<partial>Q) \<le> (\<integral>\<omega>. real CARD('n) * L * T \<partial>Q)"
    proof (rule integral_mono_AE[OF iB P.integrable_const])
      show "AE \<omega> in Q. snd (\<omega> t) $ i $ i \<le> real CARD('n) * L * T"
        using exit_class_Y_entry_bound_ae[OF T L Q t, of i i]
        by (rule eventually_mono) simp
    qed
    then show ?thesis by (simp add: P.prob_space)
  qed
  from split partA partB show ?thesis by simp
qed

section \<open>Pair tightness from the two component moduli\<close>

text \<open>\<open>lipschitz_imp_holder_bound\<close> lives in @{theory Continuous_Path_Spaces.Holder_Interpolation}.\<close>


lemma pair_holder_of_components:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and X: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
    and Y: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
    and st: "s \<in> {0..T}" "t \<in> {0..T}"
  shows "norm (\<omega> t - \<omega> s) \<le> (c + B * T powr (1 - ga)) * \<bar>t - s\<bar> powr ga"
proof -
  have split: "\<omega> t - \<omega> s = (fst (\<omega> t) - fst (\<omega> s), snd (\<omega> t) - snd (\<omega> s))"
    by (simp add: prod_eq_iff)
  have "norm (\<omega> t - \<omega> s)
      \<le> norm (fst (\<omega> t) - fst (\<omega> s)) + norm (snd (\<omega> t) - snd (\<omega> s))"
    unfolding split by (rule norm_Pair_le)
  also have "\<dots> \<le> c * \<bar>t - s\<bar> powr ga + B * \<bar>t - s\<bar>"
    by (intro add_mono X[OF st] Y[OF st])
  also have "\<dots> \<le> c * \<bar>t - s\<bar> powr ga + B * T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    by (intro add_left_mono lipschitz_imp_holder_bound[OF T ga B st])
  also have "\<dots> = (c + B * T powr (1 - ga)) * \<bar>t - s\<bar> powr ga"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Hence the compact set: pair paths starting at \<open>(x, 0)\<close> whose
  \<open>X\<close>-part obeys a Hoelder-\<open>ga\<close> bound and whose \<open>Y\<close>-part is
  \<open>B\<close>-Lipschitz form a subset of a compact pair-Hoelder ball. This is the
  set the tightness estimate has to charge; the \<open>X\<close>-side probability
  bound is \<open>Path_Tightness.path_law_holder_ball_bound_vec\<close> and the
  \<open>Y\<close>-side holds with probability one by \<open>diffquot_lipschitz\<close>.\<close>

theorem compactin_pair_holder_ball:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c"
  shows "compactin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}. norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}"
  by (rule compactin_path_holder_ball[OF T ga c])

lemma pair_holder_ball_mem:
  fixes \<omega> :: "'n::finite pairpath" and x :: "real^'n"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and mem: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and start: "\<omega> 0 = (x, 0)"
    and X: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
    and Y: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
        \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
  shows "\<omega> \<in> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u) \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  using mem start
  by (auto intro!: pair_holder_of_components[OF T ga c B X Y])

text \<open>The tightness criterion the pair laws are checked against: since
  \<open>compactin_pair_holder_ball\<close> supplies the compact set outright, a
  family of pair laws is tight as soon as, for every \<open>e\<close>, some Hoelder
  ball carries all but \<open>e\<close> of every law's mass.\<close>

theorem tight_on_set_pair_holder_charge:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 \<le> T" and ga: "0 < ga"
    and fm: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> finite_measure N"
    and st: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> sets (path_borel T :: ('n pairpath) measure) = sets N"
    and charge: "\<And>e. 0 < e \<Longrightarrow> \<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}) < e)"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
  unfolding tight_on_set_def
proof (intro conjI)
  show "\<forall>M\<in>\<Gamma>. finite_measure M \<and> sets (path_borel T :: ('n pairpath) measure) = sets M"
    using fm st by blast
next
  show "\<forall>e>0. \<exists>K.
      compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) K
      \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
  proof (intro allI impI)
    fix e :: real assume e: "0 < e"
    obtain c where c: "0 \<le> c"
      and ch: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> measure N (space N -
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
           \<omega> 0 = (x, 0)
           \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}) < e"
      using charge[OF e] by blast
    show "\<exists>K.
        compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) K
        \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
      by (intro exI[of _ "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}"] conjI ballI
          compactin_pair_holder_ball[OF T ga c] ch)
  qed
qed

text \<open>The charge splits along the components: the \<open>X\<close>-side Hoelder event and
  the \<open>Y\<close>-side Lipschitz event intersect inside a pair Hoelder ball
  (\<open>pair_holder_of_components\<close>), so their complements cover the ball's
  complement and subadditivity finishes; here the \<open>Y\<close>-event has
  probability one, so only the \<open>X\<close>-side estimate carries content.\<close>

lemma pair_holder_charge_split:
  fixes N :: "(('n::finite) pairpath) measure" and x :: "real^'n"
    and T ga c B :: real
    and AX :: "real \<Rightarrow> (('n) pairpath) set" and AY :: "(('n) pairpath) set"
  assumes AX_def: "AX = (\<lambda>c. {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga)})"
    and AY_def: "AY = {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      snd (\<omega> 0) = 0
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}. norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>)}"
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and c: "0 \<le> c" and B: "0 \<le> B"
    and fm: "finite_measure N"
    and sp: "space N = mspace (path_metric T :: ('n pairpath) metric)"
    and mX: "AX c \<in> sets N" and mY: "AY \<in> sets N"
  shows "measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
      \<le> measure N (space N - AX c) + measure N (space N - AY)"
proof -
  interpret FM: finite_measure N by fact
  have sub: "AX c \<inter> AY \<subseteq> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  proof
    fix \<omega> assume w: "\<omega> \<in> AX c \<inter> AY"
    then have mem: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and x0: "fst (\<omega> 0) = x" and y0: "snd (\<omega> 0) = 0"
      and Xb: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
          \<Longrightarrow> norm (fst (\<omega> v) - fst (\<omega> u)) \<le> c * \<bar>v - u\<bar> powr ga"
      and Yb: "\<And>u v. u \<in> {0..T} \<Longrightarrow> v \<in> {0..T}
          \<Longrightarrow> norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
      unfolding AX_def AY_def by auto
    have "\<omega> 0 = (x, 0)" using x0 y0 by (simp add: prod_eq_iff)
    then show "\<omega> \<in> {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        \<omega> 0 = (x, 0)
        \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
             norm (\<omega> v - \<omega> u)
               \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
      using mem
      by (auto intro!: pair_holder_of_components[OF T ga c B Xb Yb])
  qed
  have "space N - {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}
      \<subseteq> (space N - AX c) \<union> (space N - AY)"
    using sub by blast
  then have "measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
      \<le> measure N ((space N - AX c) \<union> (space N - AY))"
    using mX mY sp
    by (intro FM.finite_measure_mono sets.Un sets.compl_sets) auto
  also have "\<dots> \<le> measure N (space N - AX c) + measure N (space N - AY)"
    using mX mY
    by (intro measure_subadditive sets.compl_sets)
      (auto simp: FM.emeasure_eq_measure)
  finally show ?thesis .
qed

section \<open>Passing the martingale identities through the weak limit\<close>

text \<open>\<open>unif_integrable_of_L2_bound\<close>, \<open>weak_conv_integral_of_L2_bound\<close> live in @{theory Continuous_Path_Spaces.Path_Tightness}.\<close>


section \<open>The clauses of the class that survive a weak limit\<close>

text \<open>Lemma 2.3 of the paper says the class is closed, passing each defining
  clause of (1.7) to the limit law. The paper uses Prokhorov followed by
  Skorokhod's representation theorem; this instead uses the closed-set
  half of the portmanteau theorem (\<open>weak_conv_closed_full_mass\<close>), needing
  no almost-sure realisation.

  This section discharges the two clauses that are closed conditions on
  a single path: the starting point \<open>(x, 0)\<close> and the covariation
  constraint of (1.7). Portmanteau gives them only for the countably many
  rational pairs \<open>s < t\<close>, and path continuity upgrades that to all real
  pairs (\<open>diffquot_all_of_rational\<close>), as in the paper's own argument. The
  remaining two clauses are the martingale properties, which go through
  the integrated identities instead (\<open>weak_conv_integral_of_L2_bound\<close>).\<close>

subsection \<open>Full mass of the two closed clauses on a class member\<close>

lemma exit_class_diffquot_full_mass:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
    and s: "s \<in> {0..T}" and t: "t \<in> {0..T}" and st: "s < t"
  shows "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L} = 1"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have mm: "{\<omega> \<in> space Q. (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))
      \<in> sconstraint k L} \<in> sets Q"
    unfolding sp setsQ
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF s t]])
  have ae: "AE \<omega> in Q. (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))
      \<in> sconstraint k L"
  proof -
    have "AE \<omega> in Q. \<forall>u v. 0 \<le> u \<longrightarrow> u < v \<longrightarrow> v \<le> T \<longrightarrow>
        (1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
      using Q unfolding exit_class_def by blast
    then show ?thesis
      by (rule eventually_mono) (use s t st in auto)
  qed
  show ?thesis using P.prob_Collect_eq_1[OF mm] ae unfolding sp by blast
qed

text \<open>The starting point is a closed condition too: evaluation at time \<open>0\<close>
  is continuous and \<open>{(x, 0)}\<close> is closed.\<close>

lemma closedin_start_point:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). \<omega> 0 = (x, 0)}"
proof -
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "closedin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> topspace (mtopology_of (path_metric T :: ('n pairpath) metric)).
         \<omega> 0 \<in> {(x, 0)}}"
    by (intro closedin_continuous_map_preimage_gen
          [where Y = euclidean, simplified]
        continuous_map_path_eval[OF z] closed_singleton closedin_topspace)
  then show ?thesis by simp
qed

lemma exit_class_start_full_mass:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> exit_class k L T x"
  shows "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)} = 1"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have mm: "{\<omega> \<in> space Q. \<omega> 0 = (x, 0)} \<in> sets Q"
    unfolding sp setsQ by (rule borel_of_closed[OF closedin_start_point[OF T]])
  have ae: "AE \<omega> in Q. \<omega> 0 = (x, 0)"
  proof -
    have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding exit_class_def by blast
    then show ?thesis
      by (rule eventually_mono) (simp add: prod_eq_iff)
  qed
  show ?thesis using P.prob_Collect_eq_1[OF mm] ae unfolding sp by blast
qed

subsection \<open>Both closed clauses pass to the weak limit\<close>

text \<open>The start clause needs nothing beyond portmanteau. The covariation
  clause is available only pair by pair; the countable conjunction over
  rational pairs is an almost-sure statement (\<open>AE_ball_countable'\<close>), and
  \<open>diffquot_all_of_rational\<close> --- the paper's own last step, "by continuity"
  --- extends it to every real pair.\<close>

theorem exit_class_start_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T"
    and mem: "\<And>i. Qi i \<in> exit_class k L T x"
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
  proof (rule weak_conv_closed_full_mass[OF wc closedin_start_point[OF T]])
    show "\<And>i. prob_space (Qi i)" by (rule exit_class_prob[OF mem])
    show "prob_space Q" by (rule prob)
    show "\<And>i. measure (Qi i)
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). \<omega> 0 = (x, 0)} = 1"
      by (rule exit_class_start_full_mass[OF T mem])
  qed
  then have "AE \<omega> in Q. \<omega> 0 = (x, 0)"
    using P.prob_Collect_eq_1[OF mm] unfolding sp by blast
  then show ?thesis by (rule eventually_mono) (simp add: prod_eq_iff)
qed

theorem exit_class_diffquot_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes mem: "\<And>i. Qi i \<in> exit_class k L T x"
    and wc: "weak_conv_on Qi Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  interpret P: prob_space Q by (rule prob)
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have one: "AE \<omega> in Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p))
      \<in> sconstraint k L"
    if pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
  proof -
    have mm: "{\<omega> \<in> space Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p))
        \<in> sconstraint k L} \<in> sets Q"
      unfolding sp setsQ
      by (rule borel_of_closed
          [OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
    have "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} = 1"
    proof (rule diffquot_constraint_weak_limit[OF pq(1) pq(2) wc])
      show "\<And>i. prob_space (Qi i)" by (rule exit_class_prob[OF mem])
      show "prob_space Q" by (rule prob)
      show "\<And>i. measure (Qi i)
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} = 1"
        by (rule exit_class_diffquot_full_mass[OF mem pq])
    qed
    then show ?thesis
      using P.prob_Collect_eq_1[OF mm] unfolding sp by blast
  qed
  have rat: "AE \<omega> in Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF this] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space Q"
      by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W sp by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition exit_val ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "exit_val k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` exit_class k L T x)"

(*<*)
end
(*>*)
