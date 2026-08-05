(*
  Title:   Paper_Class.thy
  Content: The class P_x of Eq. (1.7) of arXiv:2512.17702, encoded as
           laws of the PAIR (X, <X>) on the path space, following the
           paper's own proof of Lemma 2.3: the covariation is carried
           as a second, uniformly Lipschitz path component whose
           difference quotients lie in the compact convex constraint
           set S = Pi_constraint k \<inter> {eigen_ub L} (Lemma 2.1 =
           lemma_2_1_exact identifies S with the convex hull of the
           unconvexified sufficient-volatility set (1.4)).

           This file provides the DEFINITIONAL layer of plan item NC-1
           (see PLAN_THEOREM_1_1.md \<section>NC); the closedness of the class
           (NC-2/3/4) and the bridge to the stopped_market witnesses
           build on it.

  STATUS:  PIDE-green as of 2026-08-05.
*)

theory Paper_Class
  imports Path_Space Path_Tightness Exit_Semicontinuity Poincare_Separation
    Relative_Arbitrage_Comparison
begin

section \<open>The constraint set of Eq. (1.5) with the technical cap\<close>

definition sconstraint :: "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite^'n) set" where
  "sconstraint k L = Pi_constraint k \<inter> {a. eigen_ub a L}"

text \<open>The first NC-2 obligations: the constraint set is convex, closed
  and bounded, hence COMPACT.  Convexity of the \<open>Pi_constraint\<close> part is
  \<open>Pi_constraint_convex\<close>; the \<open>eigen_ub\<close> cap is an intersection of
  half-spaces in the matrix entries.  Closedness of \<open>Pi_constraint\<close>
  comes from the \<open>Pi_proj\<close>-as-infimum characterisation: \<open>c \<le> Pi_proj a m\<close>
  iff \<open>c \<le> trace (a ** P)\<close> for every rank-\<open>m\<close> projection \<open>P\<close>, an
  intersection of closed half-spaces.  Boundedness is the standard psd
  entry bound \<open>\<bar>a $ i $ j\<bar> \<le> L\<close> off the diagonal cap.\<close>

lemma quadform_convex_comb:
  fixes a b :: "real^'n::finite^'n"
  shows "x \<bullet> ((s *\<^sub>R a + t *\<^sub>R b) *v x)
      = s * (x \<bullet> (a *v x)) + t * (x \<bullet> (b *v x))"
  by (simp add: matrix_vector_mult_add_rdistrib
      scaleR_matrix_vector_assoc[symmetric] inner_add_right)

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
  psd cone the condition \<open>c \<le> Pi_proj a m\<close> is exactly the family of LINEAR
  inequalities \<open>c \<le> trace (a ** P)\<close> — one closed half-space per \<open>P\<close>.\<close>

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

lemma continuous_on_trace_mult_right:
  fixes P :: "real^'n::finite^'n"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. trace (a ** P))"
proof -
  have eq: "(\<lambda>a :: real^'n^'n. trace (a ** P))
      = (\<lambda>a. \<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). a $ i $ j * P $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  show ?thesis
    unfolding eq
    by (intro continuous_on_sum continuous_on_mult continuous_on_const
        continuous_on_matrix_entry)
qed

lemma closed_trace_proj_halfspace:
  fixes P :: "real^'n::finite^'n"
  shows "closed {a :: real^'n^'n. c \<le> trace (a ** P)}"
  by (intro closed_Collect_le continuous_on_const continuous_on_trace_mult_right)

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
  \<open>axis i 1 \<plusminus> axis j 1\<close> (a two-sided form of Cauchy–Schwarz).\<close>

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

theorem compact_sconstraint:
  assumes L: "0 \<le> L"
  shows "compact (sconstraint k L :: (real^'n::finite^'n) set)"
  by (intro compact_eq_bounded_closed[THEN iffD2] conjI
      bounded_sconstraint[OF L] closed_sconstraint)

section \<open>The pair path space and its coordinate processes\<close>

text \<open>Paths take values in \<open>real^'n \<times> real^'n^'n\<close>: the process together
  with its running covariation.  \<open>path_law\<close>, \<open>path_metric\<close> and the
  tightness machinery are polymorphic in the value type, so the whole
  Section-2 toolchain applies verbatim.\<close>

definition outerp :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "outerp x = (\<chi> i j. x $ i * x $ j)"

type_synonym ('n) pairpath = "real \<Rightarrow> (real^'n) \<times> (real^'n^'n)"

abbreviation pairX :: "real \<Rightarrow> ('n::finite) pairpath \<Rightarrow> real^'n"
  where "pairX t \<omega> \<equiv> fst (\<omega> t)"

abbreviation pairY :: "real \<Rightarrow> ('n::finite) pairpath \<Rightarrow> real^'n^'n"
  where "pairY t \<omega> \<equiv> snd (\<omega> t)"

section \<open>The class \<open>P\<^sub>x\<close> of Eq. (1.7), capped at horizon \<open>T\<close>\<close>

text \<open>Operational reading of (1.7), equivalent by compensator
  uniqueness: a law of the pair \<open>(X, Y)\<close> under which \<open>X\<close> is a
  martingale from \<open>x\<close>, \<open>Y\<close> starts at \<open>0\<close> with difference quotients in
  the constraint set (hence \<open>Y\<close> is Lipschitz with a.e. derivative in
  \<open>S\<close> by Lebesgue differentiation, NC-4), and \<open>X X\<^sup>T - Y\<close> is a
  martingale, so \<open>Y\<close> IS the quadratic covariation.  The horizon cap at
  \<open>T\<close> is invisible for \<open>T\<close> beyond the uniform exit-time bound
  (paper's Lemma 1.9 / Eq. (3.10)); the bridge is part of NC-1.\<close>

definition paper_pair_class ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n::finite
     \<Rightarrow> (('n pairpath) measure) set"
  where
  "paper_pair_class k L T x = {Q.
     prob_space Q \<and>
     sets Q = sets (borel_of (mtopology_of (path_metric T
       :: ('n pairpath) metric))) \<and>
     (AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))
          \<in> sconstraint k L) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0 (\<lambda>t \<omega>. fst (\<omega> t)) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))}"

text \<open>Projections out of the definition, used throughout.\<close>

lemma paper_pair_class_prob:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "prob_space Q"
  using Q unfolding paper_pair_class_def by blast

lemma paper_pair_class_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  using Q unfolding paper_pair_class_def by blast

lemma space_of_path_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "space Q = mspace (path_metric T :: ('n pairpath) metric)"
  using sets_eq_imp_space_eq[OF assms] by (simp add: space_borel_of)

section \<open>NC-3: the constraint passes to weak limits (no Skorokhod)\<close>

text \<open>The paper passes the covariation constraint to the limit law using
  Skorokhod's representation theorem, which the AFP does not have.  We
  substitute the CLOSED-SET half of the portmanteau theorem
  (\<open>weak_conv_closed_full_mass\<close>): for FIXED times \<open>s < t\<close> the difference
  quotient is a continuous function of the path, and the constraint set is
  closed (\<open>closed_sconstraint\<close>), so
  \<open>{\<omega>. (Y t \<omega> − Y s \<omega>)/(t − s) \<in> S}\<close> is a closed set of paths.  A closed set
  of full mass under every approximating law has full mass in the limit.
  Ranging over the countably many rational pairs and using path continuity
  then gives the constraint for all real \<open>s < t\<close>.\<close>

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
    by (simp add: continuous_map_iff_continuous2 continuous_on_snd)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s))"
    by (intro continuous_map_diff)
      (auto intro: continuous_map_compose[OF _ sndc, unfolded o_def])
  moreover have scl: "continuous_map euclidean euclidean
      (\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)"
    by (simp add: continuous_map_iff_continuous2
        continuous_on_scaleR continuous_on_const continuous_on_id)
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
    by (simp add: topspace_mtopology_of)
qed

text \<open>The second half of NC-3: the weak limit only delivers the constraint
  for the COUNTABLY many rational pairs (one closed set per pair, all of
  full mass, intersected).  Path continuity and closedness of the
  constraint set upgrade that to all real \<open>s < t\<close>: squeeze rationals
  \<open>p\<^sub>n \<down> s\<close>, \<open>q\<^sub>n \<up> t\<close> strictly inside \<open>(s,t)\<close>, so every approximating
  quotient is constrained, and pass to the limit.\<close>

lemma diffquot_all_of_rational:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes S: "closed S"
    and cont: "continuous_on {0..T} Y"
    and rat: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (Y q - Y p) \<in> S"
    and st: "0 \<le> s" "s < t" "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
proof -
  define d where "d = (t - s) / 3"
  have d0: "0 < d" using st unfolding d_def by simp
  define e where "e = (\<lambda>n :: nat. min d (1 / real (Suc n)))"
  have e0: "0 < e n" for n using d0 unfolding e_def by simp
  have ed: "e n \<le> d" for n unfolding e_def by simp
  have elim: "e \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>n. 0" e sequentially
      "\<lambda>n. 1 / real (Suc n)"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> e n"
      using e0 by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. e n \<le> 1 / real (Suc n)"
      by (simp add: e_def)
    show "(\<lambda>n :: nat. 0 :: real) \<longlonglongrightarrow> 0" by simp
    show "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
  qed
  have exp: "\<exists>r. r \<in> \<rat> \<and> s < r \<and> r < s + e n" for n
  proof -
    have "s < s + e n" using e0 by simp
    from Rats_dense_in_real[OF this] show ?thesis by blast
  qed
  have exq: "\<exists>r. r \<in> \<rat> \<and> t - e n < r \<and> r < t" for n
  proof -
    have "t - e n < t" using e0 by simp
    from Rats_dense_in_real[OF this] show ?thesis by blast
  qed
  obtain p where p: "\<And>n. p n \<in> \<rat>" "\<And>n. s < p n" "\<And>n. p n < s + e n"
    using exp by metis
  obtain q where q: "\<And>n. q n \<in> \<rat>" "\<And>n. t - e n < q n" "\<And>n. q n < t"
    using exq by metis
  have mid: "s + d < t - d"
    unfolding d_def using st by argo
  have pq: "p n < q n" for n
  proof -
    have "p n < s + d" using p(3)[of n] ed[of n] by simp
    also have "\<dots> < t - d" by (rule mid)
    also have "\<dots> \<le> t - e n" using ed[of n] by simp
    also have "\<dots> < q n" by (rule q(2))
    finally show ?thesis .
  qed
  have pmem: "p n \<in> {0..T}" for n
    using p(2)[of n] pq[of n] q(3)[of n] st by auto
  have qmem: "q n \<in> {0..T}" for n
    using q(3)[of n] p(2)[of n] pq[of n] st by auto
  have inS: "(1 / (q n - p n)) *\<^sub>R (Y (q n) - Y (p n)) \<in> S" for n
    using p q pq pmem qmem st by (intro rat) auto
  have pl: "p \<longlonglongrightarrow> s"
  proof (rule tendsto_sandwich[of "\<lambda>n. s" p sequentially "\<lambda>n. s + e n"])
    show "\<forall>\<^sub>F n in sequentially. s \<le> p n"
      using p(2) by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. p n \<le> s + e n"
      using p(3) by (simp add: less_imp_le)
    show "(\<lambda>n. s) \<longlonglongrightarrow> s" by simp
    show "(\<lambda>n. s + e n) \<longlonglongrightarrow> s"
      using tendsto_add[OF tendsto_const elim] by simp
  qed
  have ql: "q \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of "\<lambda>n. t - e n" q sequentially "\<lambda>n. t"])
    show "\<forall>\<^sub>F n in sequentially. t - e n \<le> q n"
      using q(2) by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. q n \<le> t"
      using q(3) by (simp add: less_imp_le)
    show "(\<lambda>n. t - e n) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const elim] by simp
    show "(\<lambda>n. t) \<longlonglongrightarrow> t" by simp
  qed
  have Yp: "(\<lambda>n. Y (p n)) \<longlonglongrightarrow> Y s"
    using st pmem by (intro continuous_on_tendsto_compose[OF cont pl]) auto
  have Yq: "(\<lambda>n. Y (q n)) \<longlonglongrightarrow> Y t"
    using st qmem by (intro continuous_on_tendsto_compose[OF cont ql]) auto
  have "(\<lambda>n. (1 / (q n - p n)) *\<^sub>R (Y (q n) - Y (p n)))
      \<longlonglongrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s)"
    using st by (intro tendsto_intros Yp Yq ql pl) auto
  then show ?thesis
    by (rule closed_sequentially[OF S inS])
qed

section \<open>NC-4: from difference quotients to the density\<close>

text \<open>Once the constraint holds for ALL \<open>s < t\<close>, two things follow with no
  measure theory.  First, \<open>Y\<close> is LIPSCHITZ, because the constraint set is
  bounded — this is the modulus that makes the \<open>Y\<close>-side of the pair
  tightness an Arzelà–Ascoli argument and, by Lebesgue differentiation,
  gives a.e. differentiability.  Second, WHEREVER the derivative exists it
  lies in the constraint set, because it is a limit of constrained
  difference quotients and the set is closed.  Together: \<open>dY/dt \<in> S\<close> a.e.,
  which is the density statement of Eq. (1.7).\<close>

lemma diffquot_lipschitz:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes B0: "0 \<le> B" and B: "\<And>a. a \<in> S \<Longrightarrow> norm a \<le> B"
    and dq: "\<And>s t. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> t \<le> T
        \<Longrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
  shows "B-lipschitz_on {0..T} Y"
proof (rule lipschitz_onI[OF _ B0])
  fix u v :: real
  assume uv: "u \<in> {0..T}" "v \<in> {0..T}"
  have key: "dist (Y a) (Y b) \<le> B * dist a b"
    if ab: "a \<in> {0..T}" "b \<in> {0..T}" "a < b" for a b
  proof -
    have ba: "0 < b - a" using ab by simp
    have "(1 / (b - a)) *\<^sub>R (Y b - Y a) \<in> S"
      using ab by (intro dq) auto
    then have "norm ((1 / (b - a)) *\<^sub>R (Y b - Y a)) \<le> B" by (rule B)
    then have "(1 / (b - a)) * norm (Y b - Y a) \<le> B"
      using ba by simp
    then have "norm (Y b - Y a) \<le> B * (b - a)"
      using ba by (simp add: field_simps)
    then show ?thesis
      using ba by (simp add: dist_norm norm_minus_commute)
  qed
  show "dist (Y u) (Y v) \<le> B * dist u v"
  proof (cases "u = v")
    case True
    then show ?thesis using B0 by simp
  next
    case ne: False
    show ?thesis
    proof (cases "u < v")
      case True
      show ?thesis by (rule key[OF uv True])
    next
      case False
      with ne have vu: "v < u" by simp
      have "dist (Y v) (Y u) \<le> B * dist v u"
        by (rule key[OF uv(2) uv(1) vu])
      then show ?thesis by (simp add: dist_commute)
    qed
  qed
qed

lemma diffquot_deriv_in_constraint:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes S: "closed S"
    and dq: "\<And>s t. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> t \<le> T
        \<Longrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
    and x: "0 \<le> x" "x < T"
    and D: "(Y has_vector_derivative D) (at x within {x..T})"
  shows "D \<in> S"
proof -
  define h where "h = (\<lambda>n :: nat. min (T - x) (1 / real (Suc n)))"
  have h0: "0 < h n" for n using x unfolding h_def by simp
  have hT: "h n \<le> T - x" for n unfolding h_def by simp
  have hlim: "h \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>n. 0" h sequentially
      "\<lambda>n. 1 / real (Suc n)"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> h n" using h0 by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. h n \<le> 1 / real (Suc n)" by (simp add: h_def)
    show "(\<lambda>n :: nat. 0 :: real) \<longlonglongrightarrow> 0" by simp
    show "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
  qed
  define u where "u = (\<lambda>n. x + h n)"
  have umem: "u n \<in> {x..T} - {x}" for n
    using h0[of n] hT[of n] unfolding u_def by auto
  have ulim: "u \<longlonglongrightarrow> x"
    using tendsto_add[OF tendsto_const hlim] unfolding u_def by simp
  have quot: "(1 / (u n - x)) *\<^sub>R (Y (u n) - Y x) \<in> S" for n
    using x h0[of n] hT[of n] unfolding u_def by (intro dq) auto
  have lim0: "((\<lambda>y. (1 / norm (y - x)) *\<^sub>R (Y y - (Y x + (y - x) *\<^sub>R D))) \<longlongrightarrow> 0)
      (at x within {x..T})"
    using D by (simp add: has_vector_derivative_def has_derivative_within)
  have seq0: "(\<lambda>n. (1 / norm (u n - x))
      *\<^sub>R (Y (u n) - (Y x + (u n - x) *\<^sub>R D))) \<longlonglongrightarrow> 0"
    using lim0 umem ulim by (simp add: tendsto_at_iff_sequentially o_def)
  have alg: "(1 / norm (u n - x)) *\<^sub>R (Y (u n) - (Y x + (u n - x) *\<^sub>R D))
      = (1 / (u n - x)) *\<^sub>R (Y (u n) - Y x) - D" for n
  proof -
    have pos: "0 < u n - x" using h0[of n] unfolding u_def by simp
    then have nrm: "norm (u n - x) = u n - x" by simp
    have inv: "(1 / (u n - x)) *\<^sub>R ((u n - x) *\<^sub>R D) = D"
      using pos by simp
    have "(1 / (u n - x)) *\<^sub>R (Y (u n) - (Y x + (u n - x) *\<^sub>R D))
        = (1 / (u n - x)) *\<^sub>R (Y (u n) - Y x)
          - (1 / (u n - x)) *\<^sub>R ((u n - x) *\<^sub>R D)"
      by (simp add: scaleR_diff_right algebra_simps)
    also have "\<dots> = (1 / (u n - x)) *\<^sub>R (Y (u n) - Y x) - D"
      using inv by simp
    finally show ?thesis unfolding nrm .
  qed
  have "(\<lambda>n. (1 / (u n - x)) *\<^sub>R (Y (u n) - Y x) - D) \<longlonglongrightarrow> 0"
    using seq0 unfolding alg .
  then have "(\<lambda>n. (1 / (u n - x)) *\<^sub>R (Y (u n) - Y x)) \<longlonglongrightarrow> D"
    using LIM_zero_cancel by fastforce
  then show ?thesis
    by (rule closed_sequentially[OF S quot])
qed

text \<open>The density statement of Eq. (1.7).  The constraint on the difference
  quotients makes \<open>Y\<close> Lipschitz, hence of bounded variation, hence — by
  Lebesgue's differentiation theorem for BV functions, which HOL-Analysis
  has as \<open>Lebesgue_differentiation_thm\<close> — differentiable off a negligible
  set; and at every point of differentiability the derivative lies in the
  constraint set.  So \<open>dY/dt \<in> S\<close> for all but negligibly many \<open>t\<close>.\<close>

theorem diffquot_density_ae:
  fixes Y :: "real \<Rightarrow> 'b :: {euclidean_space, real_normed_vector}"
    and S :: "'b set"
  assumes T: "0 < T" and S: "closed S"
    and B0: "0 \<le> B" and B: "\<And>a. a \<in> S \<Longrightarrow> norm a \<le> B"
    and dq: "\<And>s t. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> t \<le> T
        \<Longrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
  shows "negligible {x \<in> {0..T}. \<not> Y differentiable (at x)}"
    and "\<And>x D. 0 \<le> x \<Longrightarrow> x < T
        \<Longrightarrow> (Y has_vector_derivative D) (at x within {x..T}) \<Longrightarrow> D \<in> S"
proof -
  have lip: "B-lipschitz_on {0..T} Y"
    by (rule diffquot_lipschitz[OF B0 B dq])
  have norm_le: "norm (Y u - Y v) \<le> B * norm (u - v)"
    if "u \<in> {0..T}" "v \<in> {0..T}" for u v
    using lipschitz_onD[OF lip that] by (simp add: dist_norm)
  have bv: "has_bounded_variation_on Y {0..T}"
    by (rule Lipschitz_imp_has_bounded_variation[where B = B])
      (use norm_le in auto)
  show "negligible {x \<in> {0..T}. \<not> Y differentiable (at x)}"
    by (rule Lebesgue_differentiation_thm[OF is_interval_cc bv])
next
  fix x D
  assume x: "0 \<le> x" "x < T"
    and Dx: "(Y has_vector_derivative D) (at x within {x..T})"
  show "D \<in> S"
    by (rule diffquot_deriv_in_constraint[OF S dq x Dx])
qed

text \<open>The NC-3 transfer itself: a single difference-quotient constraint,
  holding almost surely under every approximating law, holds almost surely
  under the weak limit.  (The a.s. statements are read as full mass of the
  closed set, which is how the class is phrased.)\<close>

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

text \<open>The mathematical heart of the class's covariation condition, and the
  place where the paper uses its Lemma 2.1: if a density takes values in the
  CLOSED CONVEX constraint set, then so does its average over any interval —
  which is exactly the difference quotient of the running covariation
  \<open>Y t = \<integral>₀ᵗ a\<close>.  The proof is separation: were the average outside, a
  hyperplane would separate it from \<open>S\<close>, but the same linear functional
  applied under the integral sign cannot cross that hyperplane.

  This holds for ANY closed convex set, so it is stated that way; the
  application takes \<open>S = sconstraint k L\<close> (\<open>closed_sconstraint\<close>,
  \<open>sconstraint_convex\<close>), whose members arrive as \<open>suff_volatile\<close> densities
  through \<open>lemma_2_1_easy\<close>.\<close>

lemma average_in_closed_convex:
  fixes a :: "real \<Rightarrow> 'b :: {euclidean_space, real_inner, heine_borel}"
    and S :: "'b set"
  assumes S: "convex S" "closed S" and st: "s < t"
    and mem: "\<And>u. u \<in> {s..t} \<Longrightarrow> a u \<in> S"
    and int: "set_integrable lborel {s..t} a"
  shows "(1 / (t - s)) *\<^sub>R (set_lebesgue_integral lborel {s..t} a) \<in> S"
proof (rule ccontr)
  assume out: "(1 / (t - s)) *\<^sub>R (set_lebesgue_integral lborel {s..t} a) \<notin> S"
  obtain b c where bc: "inner b ((1 / (t - s))
      *\<^sub>R (set_lebesgue_integral lborel {s..t} a)) < c"
    and sep: "\<And>y. y \<in> S \<Longrightarrow> c < inner b y"
    using separating_hyperplane_closed_point[OF S out] by blast
  have ts: "0 < t - s" using st by simp
  have iint: "set_integrable lborel {s..t} (\<lambda>u. inner (a u) b)"
  proof -
    have "integrable lborel (\<lambda>u. (indicat_real {s..t} u *\<^sub>R a u) \<bullet> b)"
      using int unfolding set_integrable_def by (rule integrable_inner_left)
    then show ?thesis
      unfolding set_integrable_def by simp
  qed
  have icst: "set_integrable lborel {s..t} (\<lambda>_ :: real. c)"
    unfolding set_integrable_def
  proof -
    have "integrable lborel (indicat_real {s..t})"
      by (rule integrable_real_indicator)
        (use st in \<open>auto simp: emeasure_lborel_Icc\<close>)
    then show "integrable lborel (\<lambda>u. indicat_real {s..t} u *\<^sub>R c)"
      by simp
  qed
  have low: "c * (t - s)
      \<le> set_lebesgue_integral lborel {s..t} (\<lambda>u. inner (a u) b)"
  proof -
    have pt: "c \<le> inner (a u) b" if "u \<in> {s..t}" for u
      using sep[OF mem[OF that]] by (simp add: inner_commute)
    have "set_lebesgue_integral lborel {s..t} (\<lambda>_. c)
        \<le> set_lebesgue_integral lborel {s..t} (\<lambda>u. inner (a u) b)"
      using pt by (intro set_integral_mono[OF icst iint]) auto
    moreover have "set_lebesgue_integral lborel {s..t} (\<lambda>_. c) = c * (t - s)"
      using st by (simp add: set_integral_const)
    ultimately show ?thesis by simp
  qed
  have comm: "set_lebesgue_integral lborel {s..t} (\<lambda>u. inner (a u) b)
      = inner (set_lebesgue_integral lborel {s..t} a) b"
    using int unfolding set_lebesgue_integral_def
    by (simp add: set_integrable_def flip: integral_inner_left)
  have eq: "c * (t - s) \<le> inner (set_lebesgue_integral lborel {s..t} a) b"
    using low unfolding comm .
  have "inner (set_lebesgue_integral lborel {s..t} a) b < c * (t - s)"
  proof -
    have "inner b ((1 / (t - s))
        *\<^sub>R (set_lebesgue_integral lborel {s..t} a))
        = (1 / (t - s)) * inner (set_lebesgue_integral lborel {s..t} a) b"
      by (simp add: inner_commute)
    with bc have lt: "(1 / (t - s))
        * inner (set_lebesgue_integral lborel {s..t} a) b < c"
      by (simp add: inner_commute)
    have "inner (set_lebesgue_integral lborel {s..t} a) b
        = (t - s) * ((1 / (t - s))
            * inner (set_lebesgue_integral lborel {s..t} a) b)"
      using ts by simp
    also have "\<dots> < (t - s) * c"
      using lt ts by (intro mult_strict_left_mono)
    finally show ?thesis by (simp add: mult.commute)
  qed
  with eq show False by simp
qed

text \<open>The specialisation the bridge will consume.  A market witness carries
  its volatility as a \<open>suff_volatile\<close> density with the \<open>eigen_ub\<close> cap;
  \<open>lemma_2_1_easy\<close> puts each value in \<open>sconstraint k L\<close> (this is the EASY
  inclusion of Lemma 2.1 — the hard one, \<open>lemma_2_1_exact\<close>, is what makes
  the two sets the same and is not needed here), and the average lemma then
  puts the difference quotient of \<open>Y t = \<integral>₀ᵗ a\<close> there too.\<close>

lemma suff_volatile_cap_in_sconstraint:
  fixes a :: "real^'n::finite^'n"
  assumes sv: "a \<in> suff_volatile k" and ub: "eigen_ub a L"
  shows "a \<in> sconstraint k L"
  unfolding sconstraint_def
  using sv ub hull_subset[of "suff_volatile k"] lemma_2_1_easy by auto

theorem diffquot_of_density_in_sconstraint:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes st: "s < t"
    and sv: "\<And>u. u \<in> {s..t} \<Longrightarrow> a u \<in> suff_volatile k"
    and ub: "\<And>u. u \<in> {s..t} \<Longrightarrow> eigen_ub (a u) L"
    and int: "set_integrable lborel {s..t} a"
  shows "(1 / (t - s)) *\<^sub>R (set_lebesgue_integral lborel {s..t} a)
      \<in> sconstraint k L"
proof (rule average_in_closed_convex[OF sconstraint_convex closed_sconstraint st _ int])
  fix u assume "u \<in> {s..t}"
  then show "a u \<in> sconstraint k L"
    using sv ub by (intro suff_volatile_cap_in_sconstraint) auto
qed

subsection \<open>The constraint set is inhabited — and why that matters\<close>

text \<open>The paper's standing assumption is \<open>L \<ge> 1\<close> (Theorem 1.1), and that is
  exactly what makes the IDENTITY matrix admissible: \<open>\<Pi>\<^sub>m(I) = m \<ge> m − k\<close> and
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(I) = 1 \<le> L\<close>.  This is not a curiosity.  Per the paper's (1.7) the
  constraint holds for a.e. \<open>t \<ge> 0\<close> — the process is NEVER stopped, and
  \<open>\<tau>\<^sub>K\<close> of (1.8) is merely a functional of the path — so the bridge from a
  stopped market witness must CONTINUE its volatility past the stopping
  time with some admissible value.  \<open>mat 1\<close> is that value.\<close>

lemma psd_mat_1: "psd (mat 1 :: real^'n::finite^'n)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (mat 1 :: real^'n^'n) = mat 1"
    by (simp add: transpose_mat)
  fix x :: "real^'n"
  show "0 \<le> x \<bullet> (mat 1 *v x)"
    by (simp add: matrix_vector_mul_lid)
qed

lemma Pi_proj_mat_1:
  assumes m: "m \<le> CARD('n::finite)"
  shows "real m \<le> Pi_proj (mat 1 :: real^'n^'n) m"
proof (rule Pi_proj_ge[OF m])
  fix P :: "real^'n^'n"
  assume P: "is_proj P" "trace P = real m"
  have "trace ((mat 1 :: real^'n^'n) ** P) = trace P"
    by (simp add: matrix_mul_lid)
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
      by (simp add: matrix_vector_mul_lid)
    also have "\<dots> \<le> L * (x \<bullet> x)"
    proof -
      have "1 * (x \<bullet> x) \<le> L * (x \<bullet> x)"
        using L inner_ge_zero[of x] by (rule mult_right_mono)
      then show ?thesis by simp
    qed
    finally show "x \<bullet> ((mat 1 :: real^'n^'n) *v x) \<le> L * (x \<bullet> x)" .
  qed
qed

corollary sconstraint_nonempty:
  assumes L: "1 \<le> L"
  shows "(sconstraint k L :: (real^'n::finite^'n) set) \<noteq> {}"
  using mat_1_in_sconstraint[OF L] by blast

subsection \<open>Continuing a stopped volatility past its stopping time\<close>

text \<open>The faithful bridge, per (1.7)–(1.8): the paper's processes are NEVER
  stopped, so a market witness — whose volatility vanishes after its
  stopping time — must be CONTINUED to become a class member.  Continue with
  \<open>mat 1\<close>, admissible because \<open>L \<ge> 1\<close> (\<open>mat_1_in_sconstraint\<close>).  The exit
  time is untouched: by (1.8) \<open>\<tau>\<^sub>K\<close> depends only on the path up to the first
  exit from \<open>K\<close>, and the continuation acts only afterwards.\<close>

definition acont :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "acont a tv s = (if s \<le> tv then a s else mat 1)"

lemma acont_before: "s \<le> tv \<Longrightarrow> acont a tv s = a s"
  unfolding acont_def by simp

lemma acont_after: "tv < s \<Longrightarrow> acont a tv s = mat 1"
  unfolding acont_def by simp

text \<open>Time-measurability is inherited by the continuation.  The locale
  assumption \<open>acov_time_measurable\<close> is stated on the NONNEGATIVE axis only
  --- faithfully so, since (1.7) constrains the density for "a.e. \<open>t \<ge> 0\<close>"
  --- and that is also all that is available here: for \<open>u < 0 \<le> tv\<close> the
  continuation still reads off \<open>a u\<close>, about which nothing is known.

  TRAP (cost several round-trips): \<^const>\<open>lborel\<close> is POLYMORPHIC, and
  \<^typ>\<open>real^'n^'n\<close> carries an \<^class>\<open>ord\<close> instance, so an unannotated
  binder in a goal \<open>(\<lambda>u. \<dots>) \<in> borel_measurable lborel\<close> silently elaborates
  at the MATRIX type instead of at \<open>real\<close>.  The symptoms are baffling:
  \<open>show\<close>s that "fail to refine any pending goal" although they print
  identically, and \<open>simp\<close> unable to prove \<open>open {..<0}\<close>.  Pin
  \<open>lborel :: real measure\<close> and annotate every binder.\<close>

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

lemma acont_in_sconstraint:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes L: "1 \<le> L"
    and sv: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> a u \<in> suff_volatile k"
    and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> eigen_ub (a u) L"
    and s: "0 \<le> s"
  shows "acont a tv s \<in> sconstraint k L"
proof (cases "s \<le> tv")
  case True
  then have "acont a tv s = a s" by (rule acont_before)
  then show ?thesis
    using suff_volatile_cap_in_sconstraint[OF sv[OF s True] ub[OF s True]]
    by simp
next
  case False
  then have "acont a tv s = mat 1" by (simp add: acont_after)
  then show ?thesis using mat_1_in_sconstraint[OF L] by simp
qed

text \<open>Hence the continued volatility has ALL its difference quotients in the
  constraint set — which is exactly the covariation condition of
  \<open>paper_pair_class\<close>, now holding for every \<open>0 \<le> s < t\<close> with no stopping
  caveat, as (1.7) demands.\<close>

theorem diffquot_of_continued_density:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes L: "1 \<le> L" and s0: "0 \<le> s" and st: "s < t"
    and sv: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> a u \<in> suff_volatile k"
    and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> eigen_ub (a u) L"
    and int: "set_integrable lborel {s..t} (acont a tv)"
  shows "(1 / (t - s)) *\<^sub>R (set_lebesgue_integral lborel {s..t} (acont a tv))
      \<in> sconstraint k L"
proof (rule average_in_closed_convex
    [OF sconstraint_convex closed_sconstraint st _ int])
  fix u assume u: "u \<in> {s..t}"
  have u0: "0 \<le> u" using u s0 by simp
  show "acont a tv u \<in> sconstraint k L"
    by (rule acont_in_sconstraint[OF L sv ub u0])
qed

subsection \<open>The running covariation built from a continued volatility\<close>

text \<open>Packaging the volatility side of the bridge: \<open>Yint a t = \<integral>₀ᵗ a\<close> starts
  at \<open>0\<close>, has increments given by the interval integrals, and — when \<open>a\<close> is
  the CONTINUED density — difference quotients in the constraint set for
  every \<open>0 \<le> s < t\<close>.  That is precisely the covariation half of
  \<open>paper_pair_class\<close>.\<close>

definition Yint :: "(real \<Rightarrow> real^'n::finite^'n) \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where "Yint a t = set_lebesgue_integral lborel {0..t} a"

lemma Yint_0: "Yint a 0 = 0"
  unfolding Yint_def set_lebesgue_integral_def
proof (rule integral_eq_zero_AE)
  have "AE x in lborel. x \<notin> {0 :: real}"
    using finite_imp_null_set_lborel[of "{0 :: real}"]
    by (simp add: AE_iff_null_sets)
  then show "AE x in lborel. indicat_real {0..0} x *\<^sub>R a x = 0"
    by (rule eventually_mono) auto
qed

lemma Yint_increment:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes st: "0 \<le> s" "s \<le> t"
    and i1: "set_integrable lborel {0..s} a"
    and i2: "set_integrable lborel {s..t} a"
  shows "Yint a t - Yint a s = set_lebesgue_integral lborel {s..t} a"
proof -
  have ae: "AE u in lborel. \<not> (u \<in> {0..s} \<and> u \<in> {s..t})"
  proof -
    have "AE u in lborel. u \<notin> {s :: real}"
      using finite_imp_null_set_lborel[of "{s :: real}"]
      by (simp add: AE_iff_null_sets)
    then show ?thesis
      by (rule eventually_mono) auto
  qed
  have un: "{0..s} \<union> {s..t} = {0..t}" using st by auto
  have "Yint a t = set_lebesgue_integral lborel ({0..s} \<union> {s..t}) a"
    unfolding Yint_def un ..
  also have "\<dots> = set_lebesgue_integral lborel {0..s} a
      + set_lebesgue_integral lborel {s..t} a"
    by (rule set_integral_Un_AE[OF ae _ _ i1 i2]) auto
  finally show ?thesis
    unfolding Yint_def[of a s] by simp
qed

theorem Yint_diffquot_in_sconstraint:
  fixes a :: "real \<Rightarrow> real^'n::finite^'n"
  assumes L: "1 \<le> L" and s0: "0 \<le> s" and st: "s < t"
    and sv: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> a u \<in> suff_volatile k"
    and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> eigen_ub (a u) L"
    and i1: "set_integrable lborel {0..s} (acont a tv)"
    and i2: "set_integrable lborel {s..t} (acont a tv)"
  shows "(1 / (t - s)) *\<^sub>R (Yint (acont a tv) t - Yint (acont a tv) s)
      \<in> sconstraint k L"
proof -
  have "Yint (acont a tv) t - Yint (acont a tv) s
      = set_lebesgue_integral lborel {s..t} (acont a tv)"
    using st by (intro Yint_increment[OF s0 _ i1 i2]) simp
  then show ?thesis
    using diffquot_of_continued_density[OF L s0 st sv ub i2] by simp
qed

subsection \<open>What the class gives the tightness argument for free\<close>

text \<open>The \<open>Y\<close>-side of the pair tightness costs nothing: the class already
  asserts that the difference quotients of \<open>Y\<close> lie in \<open>sconstraint k L\<close>
  almost surely, and every element of that set has norm at most \<open>n\<sqdot>L\<close>
  (\<open>sconstraint_norm_le\<close>), so \<open>diffquot_lipschitz\<close> makes \<open>Y\<close> almost surely
  \<open>n\<sqdot>L\<close>-Lipschitz.  That is the \<open>Y\<close>-event of \<open>pair_holder_charge_split\<close>,
  with probability ONE — leaving the \<open>X\<close>-side Hölder estimate as the only
  part of the tightness with content.\<close>

theorem paper_pair_class_lipschitz_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q. (real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding paper_pair_class_def by blast
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

text \<open>And, combined with NC-4, the class member's \<open>Y\<close> is almost surely
  differentiable off a negligible set of times with derivative in the
  constraint set — the density statement of Eq. (1.7), now stated for the
  class itself rather than for a bare path.\<close>

theorem paper_pair_class_density_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q.
      negligible {u \<in> {0..T}. \<not> (\<lambda>t. snd (\<omega> t)) differentiable (at u)}
      \<and> (\<forall>u D. 0 \<le> u \<longrightarrow> u < T
           \<longrightarrow> ((\<lambda>t. snd (\<omega> t)) has_vector_derivative D) (at u within {u..T})
           \<longrightarrow> D \<in> sconstraint k L)"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding paper_pair_class_def by blast
  have B0: "0 \<le> real CARD('n) * L" using L by simp
  show ?thesis
  proof (rule AE_mp[OF dq], rule AE_I2, intro impI)
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    have dqw: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      if "0 \<le> s" "s < t" "t \<le> T" for s t
      using q that by blast
    have nb: "norm a \<le> real CARD('n) * L" if "a \<in> sconstraint k L"
      for a :: "real^'n^'n"
      using that by (rule sconstraint_norm_le[OF L])
    show "negligible {u \<in> {0..T}. \<not> (\<lambda>t. snd (\<omega> t)) differentiable (at u)}
        \<and> (\<forall>u D. 0 \<le> u \<longrightarrow> u < T
             \<longrightarrow> ((\<lambda>t. snd (\<omega> t)) has_vector_derivative D) (at u within {u..T})
             \<longrightarrow> D \<in> sconstraint k L)"
    proof -
      have part1:
        "negligible {u \<in> {0..T}. \<not> (\<lambda>t. snd (\<omega> t)) differentiable (at u)}"
        by (rule diffquot_density_ae(1)[OF T closed_sconstraint B0 nb dqw])
      have part2: "D \<in> sconstraint k L"
        if u: "0 \<le> u" "u < T"
          and Du: "((\<lambda>t. snd (\<omega> t)) has_vector_derivative D)
            (at u within {u..T})"
        for u D
        by (rule diffquot_deriv_in_constraint
            [OF closed_sconstraint dqw u(1) u(2) Du])
      from part1 part2 show ?thesis by blast
    qed
  qed
qed

text \<open>A consequence used repeatedly downstream: on the capped horizon the
  second component of a class member is UNIFORMLY BOUNDED, almost surely,
  by \<open>n\<sqdot>L\<sqdot>T\<close>.  It starts at \<open>0\<close> and is \<open>n\<sqdot>L\<close>-Lipschitz, so no
  probabilistic input is needed.  This is what makes \<open>X\<close> square-integrable
  under a class law: the martingale clause makes \<open>outerp X - Y\<close> integrable,
  and \<open>Y\<close> being bounded transfers the integrability to \<open>outerp X\<close>.\<close>

theorem paper_pair_class_Y_bounded_ae:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q. \<forall>t\<in>{0..T}. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
proof -
  have B0: "0 \<le> real CARD('n) * L" using L by simp
  have z0: "(0::real) \<in> {0..T}" using T by simp
  have lip: "AE \<omega> in Q. (real CARD('n) * L)-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule paper_pair_class_lipschitz_ae[OF T L Q])
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
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

subsection \<open>Square integrability of the class member's process\<close>

text \<open>The promised consequence.  Under a class law the coordinate process
  is square integrable on the capped horizon --- and, unlike for the repo's
  market witnesses, this cannot be read off a uniform bound on \<open>X\<close>: the
  paper's processes are neither stopped nor confined ((1.7)--(1.8)).  It
  comes instead from the SECOND martingale clause: \<open>outerp X - Y\<close> is
  integrable by definition of a martingale, \<open>Y\<close> is bounded
  (\<open>paper_pair_class_Y_bounded_ae\<close>), and the sum of the two is \<open>outerp X\<close>,
  whose diagonal entries are the squared coordinates.\<close>

lemma paper_pair_class_eval_measurable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> borel_measurable Q"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)) \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF t]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF paper_pair_class_sets[OF Q] refl] by blast
qed

theorem paper_pair_class_sq_integrable:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have t0: "0 \<le> t" using t by simp
  have MG: "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> u)) - snd (\<omega> u))"
    using Q unfolding paper_pair_class_def by blast
  then interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> u)) - snd (\<omega> u)" .
  have iA: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule MG.integrable[OF t0])
  have iA2: "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i)"
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth,
          OF integrable_bounded_linear[OF bounded_linear_vec_nth iA]])
  have em: "(\<lambda>\<omega>. \<omega> t) \<in> borel_measurable Q"
    by (rule paper_pair_class_eval_measurable[OF Q t])
  have Bm: "(\<lambda>\<omega>. snd (\<omega> t) $ i $ i) \<in> borel_measurable Q"
  proof (rule measurable_compose[OF em])
    have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    \<comment> \<open>\<^verbatim>\<open>borel_measurable_nth\<close> is only the REAL-valued instance
        \<open>real^'n \<Rightarrow> real\<close>; the matrix row map needs the linear-continuity
        route.\<close>
    have n1: "(\<lambda>v :: real^'n^'n. v $ i) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
        (rule linear_continuous_on[OF bounded_linear_vec_nth])
    have n2: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
      by (rule borel_measurable_nth)
    show "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). snd p $ i $ i)
        \<in> borel_measurable borel"
      by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
  qed
  have Bb: "AE \<omega> in Q. norm (snd (\<omega> t) $ i $ i) \<le> real CARD('n) * L * T"
  proof -
    have "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
      by (rule paper_pair_class_Y_bounded_ae[OF T L Q])
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath"
      assume "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
      then have b: "norm (snd (\<omega> t)) \<le> real CARD('n) * L * T" using t by blast
      have "norm (snd (\<omega> t) $ i $ i) \<le> norm (snd (\<omega> t) $ i)"
        by (rule Finite_Cartesian_Product.norm_nth_le)
      also have "\<dots> \<le> norm (snd (\<omega> t))"
        by (rule Finite_Cartesian_Product.norm_nth_le)
      finally show "norm (snd (\<omega> t) $ i $ i) \<le> real CARD('n) * L * T"
        using b by simp
    qed
  qed
  have iB: "integrable Q (\<lambda>\<omega>. snd (\<omega> t) $ i $ i)"
    by (rule P.integrable_const_bound[OF Bb Bm])
  have eq: "(\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ i + snd (\<omega> t) $ i $ i)"
    by (rule ext) (simp add: outerp_def power2_eq_square)
  show ?thesis
    unfolding eq by (rule Bochner_Integration.integrable_add[OF iA2 iB])
qed

section \<open>NC-2: pair tightness from the two component moduli\<close>

text \<open>The pair tightness does NOT need a matrix-valued Kolmogorov
  criterion.  The two components carry moduli of different origins — the
  \<open>X\<close>-side a stochastic Hölder estimate (\<open>Path_Tightness\<close>), the \<open>Y\<close>-side the
  DETERMINISTIC Lipschitz modulus of \<open>diffquot_lipschitz\<close> — and on a bounded
  horizon a Lipschitz bound is itself a Hölder-\<open>ga\<close> bound.  Adding the two
  through \<open>norm_Pair_le\<close> puts the whole pair path in a single Hölder ball of
  the PRODUCT type, and \<open>compactin_path_holder_ball\<close> (Path\_Space, the
  Arzelà–Ascoli input) applies there verbatim: products of
  \<open>polish_space\<close>/\<open>real_normed_vector\<close>/\<open>heine_borel\<close> spaces are again such.
  So the compact set the tightness argument needs is a single pair-Hölder
  ball.\<close>

lemma lipschitz_imp_holder_bound:
  fixes s t :: real
  assumes T: "0 \<le> T" and ga: "0 < ga" "ga \<le> 1" and B: "0 \<le> B"
    and st: "s \<in> {0..T}" "t \<in> {0..T}"
  shows "B * \<bar>t - s\<bar> \<le> B * T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
proof (cases "t = s")
  case True
  then show ?thesis using B ga T by simp
next
  case False
  then have d: "0 < \<bar>t - s\<bar>" by simp
  have dT: "\<bar>t - s\<bar> \<le> T" using st by auto
  have "\<bar>t - s\<bar> = \<bar>t - s\<bar> powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    using d by (simp flip: powr_add)
  also have "\<dots> \<le> T powr (1 - ga) * \<bar>t - s\<bar> powr ga"
    using d dT ga by (intro mult_right_mono powr_mono2) auto
  finally have "\<bar>t - s\<bar> \<le> T powr (1 - ga) * \<bar>t - s\<bar> powr ga" .
  then show ?thesis
    using B by (simp add: mult_left_mono mult.assoc)
qed

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

text \<open>Hence the compact set: pair paths starting at \<open>(x, 0)\<close> whose \<open>X\<close>-part
  obeys a Hölder-\<open>ga\<close> bound and whose \<open>Y\<close>-part is \<open>B\<close>-Lipschitz form a
  subset of a compact pair-Hölder ball.  This is the set the tightness
  estimate has to charge; the \<open>X\<close>-side probability bound is
  \<open>Path_Tightness.path_law_holder_ball_bound_vec\<close> and the \<open>Y\<close>-side holds
  with probability one by \<open>diffquot_lipschitz\<close>.\<close>

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

text \<open>The tightness criterion the pair laws are checked against.  Because
  \<open>compactin_pair_holder_ball\<close> supplies the compact set outright, a family
  of pair laws is tight as soon as, for every \<open>e\<close>, SOME Hölder ball carries
  all but \<open>e\<close> of every law's mass.\<close>

theorem tight_on_set_pair_holder_charge:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 \<le> T" and ga: "0 < ga"
    and fm: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> finite_measure N"
    and st: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))) = sets N"
    and charge: "\<And>e. 0 < e \<Longrightarrow> \<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ga)}) < e)"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
  unfolding tight_on_set_def
proof (intro conjI)
  show "\<forall>M\<in>\<Gamma>. finite_measure M \<and> sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))) = sets M"
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

text \<open>And the charge itself splits along the components: the \<open>X\<close>-side
  Hölder event and the \<open>Y\<close>-side Lipschitz event intersect INSIDE a pair
  Hölder ball (\<open>pair_holder_of_components\<close>), so their complements cover the
  ball's complement and subadditivity finishes.  In the application the
  \<open>Y\<close>-event has probability one (\<open>diffquot_lipschitz\<close>), so only the
  \<open>X\<close>-side estimate carries content.\<close>

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

section \<open>NC-3: passing the martingale identities through the weak limit\<close>

text \<open>The integrated identities the class carries — \<open>E[Z\<sqdot>(X\<^sub>t − X\<^sub>s)] = 0\<close> for
  a bounded continuous test \<open>Z\<close> of the past, and its covariation analogue —
  are integrals of CONTINUOUS but UNBOUNDED functions of the path, so plain
  weak convergence does not transfer them.  \<open>Path_Tightness\<close>'s
  \<open>weak_conv_on_integral_unif_integrable\<close> closes exactly that gap, given
  uniform integrability.  What the moment machinery actually produces is a
  uniform \<open>L\<^sup>2\<close> bound, so the usable form is the specialisation below:
  a uniform second moment implies the uniform-integrability hypothesis by
  Chebyshev–Markov, \<open>\<integral>\<bar>f\<bar>\<sqdot>1\<^bsub>{\<bar>f\<bar>>R}\<^esub> \<le> (1/R)\<sqdot>\<integral>f\<^sup>2 \<le> C/R\<close>.\<close>

lemma unif_integrable_of_L2_bound:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes C: "0 \<le> C"
    and iTi: "\<And>i R. integrable (Ni i)
        (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and iTN: "\<And>R. integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and sqi: "\<And>i. (\<integral>w. (f w)\<^sup>2 \<partial>(Ni i)) \<le> C"
    and sqN: "(\<integral>w. (f w)\<^sup>2 \<partial>N) \<le> C"
    and sqiI: "\<And>i. integrable (Ni i) (\<lambda>w. (f w)\<^sup>2)"
    and sqNI: "integrable N (\<lambda>w. (f w)\<^sup>2)"
    and e: "0 < e"
  shows "\<exists>R. 0 \<le> R
      \<and> (\<forall>i. (\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>(Ni i)) \<le> e)
      \<and> (\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>N) \<le> e"
proof -
  define R where "R = (C + 1) / e"
  have R0: "0 < R" using C e unfolding R_def by (simp add: divide_pos_pos)
  have key: "(\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>M) \<le> e"
    if int: "integrable M (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
      and sq: "(\<integral>w. (f w)\<^sup>2 \<partial>M) \<le> C"
      and sqI: "integrable M (\<lambda>w. (f w)\<^sup>2)"
    for M :: "'b measure"
  proof -
    have pt: "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<le> (1 / R) * (f w)\<^sup>2"
      for w
    proof (cases "R < \<bar>f w\<bar>")
      case True
      have "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) = \<bar>f w\<bar>"
        using True by (simp add: indicator_def)
      also have "\<dots> = (1 / R) * (R * \<bar>f w\<bar>)" using R0 by simp
      also have "\<dots> \<le> (1 / R) * (\<bar>f w\<bar> * \<bar>f w\<bar>)"
        using True R0 by (intro mult_left_mono mult_right_mono) auto
      also have "\<dots> = (1 / R) * (f w)\<^sup>2"
        by (simp add: power2_eq_square flip: power2_abs)
      finally show ?thesis .
    next
      case False
      have "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) = 0"
        using False by (simp add: indicator_def)
      also have "\<dots> \<le> (1 / R) * (f w)\<^sup>2"
        using R0 by simp
      finally show ?thesis .
    qed
    have "(\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>M)
        \<le> (\<integral>w. (1 / R) * (f w)\<^sup>2 \<partial>M)"
      using pt int sqI by (intro Bochner_Integration.integral_mono) auto
    also have "\<dots> = (1 / R) * (\<integral>w. (f w)\<^sup>2 \<partial>M)" by simp
    also have "\<dots> \<le> (1 / R) * C"
      using sq R0 by (intro mult_left_mono) auto
    also have "\<dots> \<le> e"
      using C e R0 unfolding R_def by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using R0 key[OF iTi sqi sqiI] key[OF iTN sqN sqNI]
    by (intro exI[of _ R]) auto
qed

text \<open>Hence the transfer in the form the canonical-market construction uses:
  a continuous path functional with a UNIFORM second-moment bound has its
  integral pass to the weak limit.  Applied with
  \<open>f \<omega> = Z \<omega> \<sqdot> ((X\<^sub>t − X\<^sub>s) \<bullet> e\<^sub>j)\<close> this carries the martingale identity of
  the approximating laws to the limit law, and with the squared increment it
  carries the covariation identity.\<close>

theorem weak_conv_integral_of_L2_bound:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and f: "continuous_map X euclideanreal f"
    and fmi: "\<And>i. finite_measure (Ni i)" and fmN: "finite_measure N"
    and iNi: "\<And>i. integrable (Ni i) f" and iN: "integrable N f"
    and iCi: "\<And>i R. integrable (Ni i) (\<lambda>w. max (- R) (min R (f w)))"
    and iCN: "\<And>R. integrable N (\<lambda>w. max (- R) (min R (f w)))"
    and iTi: "\<And>i R. integrable (Ni i)
        (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and iTN: "\<And>R. integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and C: "0 \<le> C"
    and sqi: "\<And>i. (\<integral>w. (f w)\<^sup>2 \<partial>(Ni i)) \<le> C" and sqN: "(\<integral>w. (f w)\<^sup>2 \<partial>N) \<le> C"
    and sqiI: "\<And>i. integrable (Ni i) (\<lambda>w. (f w)\<^sup>2)"
    and sqNI: "integrable N (\<lambda>w. (f w)\<^sup>2)"
  shows "(\<lambda>i. \<integral>w. f w \<partial>(Ni i)) \<longlonglongrightarrow> (\<integral>w. f w \<partial>N)"
  by (rule weak_conv_on_integral_unif_integrable
      [OF wc f fmi fmN iNi iN iCi iCN iTi iTN])
    (rule unif_integrable_of_L2_bound
      [OF C iTi iTN sqi sqN sqiI sqNI])

section \<open>NC-3: the clauses of the class that survive a weak limit\<close>

text \<open>Lemma 2.3 of the paper says the class is CLOSED, and its proof passes
  each defining clause of (1.7) to the limit law.  The paper does that
  through Prokhorov followed by Skorokhod's representation theorem; we
  substitute the closed-set half of the portmanteau theorem
  (\<open>weak_conv_closed_full_mass\<close>), which needs no almost-sure realisation and
  is already available here.

  This section discharges the two clauses that are CLOSED CONDITIONS ON A
  SINGLE PATH: the starting point \<open>(x, 0)\<close> and the covariation constraint of
  (1.7).  Portmanteau gives them only for the countably many RATIONAL pairs
  \<open>s < t\<close> --- one closed set per pair --- and path continuity upgrades that
  to all real pairs (\<open>diffquot_all_of_rational\<close>), exactly as in the last
  step of the paper's own argument.  The remaining two clauses of the class
  are the martingale properties; those are not closed conditions on single
  paths and go through the integrated identities instead
  (\<open>weak_conv_integral_of_L2_bound\<close>).\<close>

subsection \<open>Full mass of the two closed clauses on a class member\<close>

lemma paper_pair_class_diffquot_full_mass:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
    and s: "s \<in> {0..T}" and t: "t \<in> {0..T}" and st: "s < t"
  shows "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L} = 1"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
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
      using Q unfolding paper_pair_class_def by blast
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
  then show ?thesis by (simp add: topspace_mtopology_of)
qed

lemma paper_pair_class_start_full_mass:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> paper_pair_class k L T x"
  shows "measure Q {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)} = 1"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have sp: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have mm: "{\<omega> \<in> space Q. \<omega> 0 = (x, 0)} \<in> sets Q"
    unfolding sp setsQ by (rule borel_of_closed[OF closedin_start_point[OF T]])
  have ae: "AE \<omega> in Q. \<omega> 0 = (x, 0)"
  proof -
    have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding paper_pair_class_def by blast
    then show ?thesis
      by (rule eventually_mono) (simp add: prod_eq_iff)
  qed
  show ?thesis using P.prob_Collect_eq_1[OF mm] ae unfolding sp by blast
qed

subsection \<open>Both closed clauses pass to the weak limit\<close>

text \<open>The start clause needs nothing beyond portmanteau.  The covariation
  clause is available from portmanteau only pair by pair; the countable
  conjunction over rational pairs is an almost-sure statement
  (\<open>AE_ball_countable'\<close>), and \<open>diffquot_all_of_rational\<close> --- the paper's own
  last step, "by continuity" --- extends it to every real pair.\<close>

theorem paper_pair_class_start_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T"
    and mem: "\<And>i. Qi i \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qi Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
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
    show "\<And>i. prob_space (Qi i)" by (rule paper_pair_class_prob[OF mem])
    show "prob_space Q" by (rule prob)
    show "\<And>i. measure (Qi i)
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). \<omega> 0 = (x, 0)} = 1"
      by (rule paper_pair_class_start_full_mass[OF T mem])
  qed
  then have "AE \<omega> in Q. \<omega> 0 = (x, 0)"
    using P.prob_Collect_eq_1[OF mm] unfolding sp by blast
  then show ?thesis by (rule eventually_mono) (simp add: prod_eq_iff)
qed

theorem paper_pair_class_diffquot_limit:
  fixes Qi :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes mem: "\<And>i. Qi i \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qi Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
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
      show "\<And>i. prob_space (Qi i)" by (rule paper_pair_class_prob[OF mem])
      show "prob_space Q" by (rule prob)
      show "\<And>i. measure (Qi i)
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} = 1"
        by (rule paper_pair_class_diffquot_full_mass[OF mem pq])
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

definition paper_v ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "paper_v k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` paper_pair_class k L T x)"

end
