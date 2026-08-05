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

  STATUS:  PIDE-green (413 commands) as of 2026-08-05.
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

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition paper_v ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "paper_v k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` paper_pair_class k L T x)"

end
