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
  imports Path_Space Exit_Semicontinuity Poincare_Separation
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

theorem bounded_sconstraint:
  assumes L: "0 \<le> L"
  shows "bounded (sconstraint k L :: (real^'n::finite^'n) set)"
proof (rule boundedI)
  fix a :: "real^'n^'n"
  assume as: "a \<in> sconstraint k L"
  then have a: "psd a" and ub: "eigen_ub a L"
    by (auto simp: sconstraint_def Pi_constraint_def)
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

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition paper_v ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "paper_v k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` paper_pair_class k L T x)"

end
