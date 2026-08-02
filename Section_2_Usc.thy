section \<open>Upper semicontinuity of the essential-infimum exit time (plan item 2.3)\<close>

text \<open>
  Larsson--Ruf (EJP 29 (2024), Proposition 2.2(ii)) --- which arXiv:2512.17702
  Proposition 2.4 defers to verbatim --- proves upper semicontinuity of the value
  function by combining two facts: \<open>g(P) = P\<hyphen>essinf \<tau>\<^sub>K\<close> is usc on the set of
  candidate laws, and Berge's maximum theorem turns a usc integrand into a usc
  supremum. Berge is already available (\<open>Section_2_Compactness.usc_sup_over_compact\<close>);
  this theory supplies the first fact.

  It has to be a separate leaf. The argument needs \<open>Value_Function\<close> (for the
  \<open>measure = 1\<close> characterisation of \<open>essinf\<close>) and \<open>Path_Tightness_Market\<close> (for the
  usc of \<open>\<tau>\<^sub>K\<close> itself and the Portmanteau bridge), and no existing theory imports
  both: \<open>Value_Function\<close> sits under the market/Ito branch while the path-topology
  content sits under the AFP Prokhorov branch.
\<close>

theory Section_2_Usc
  imports Path_Tightness_Market Value_Function
begin

subsection \<open>Superlevel sets of the exit time are closed\<close>

text \<open>
  The \<open>ennreal\<close> threshold is what \<open>ess_inf_time\<close> works with, so the case split on
  \<open>c\<close> is unavoidable. The \<open>top\<close> branch is not degenerate bookkeeping: there
  \<open>{\<tau> \<ge> \<top>}\<close> is EMPTY, because the exit time is a genuine real capped at \<open>T\<close>, and
  the whole space is its complement.
\<close>

lemma etime_superlevel_closed:
  fixes T :: real and c :: ennreal and A :: "'b::polish_space set"
  assumes T: "0 \<le> T" and A: "open A"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}"
proof -
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         ennreal (etime T A (\<lambda>s w. w s) f) < c}"
  proof (cases c rule: ennreal_cases)
    case top
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}
        = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      unfolding top by simp
    then show ?thesis
      using openin_topspace[of
          "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)"]
      by simp
  next
    case (real r)
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}
        = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           etime T A (\<lambda>s w. w s) f < r}"
      unfolding real
      using etime_nonneg[OF T, of A "\<lambda>s w. w s"]
      by (auto simp: ennreal_less_iff)
    then show ?thesis by (simp add: etime_usc_on_paths[OF T A])
  qed
  have compl: "topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}"
    by (auto simp: not_le)
  show ?thesis
    unfolding closedin_def using op unfolding compl by auto
qed

subsection \<open>The essential infimum of the exit time is usc in the law\<close>

text \<open>
  This is the Portmanteau step. It is stated in the ``superlevel sets are closed''
  form rather than as a \<open>limsup\<close> inequality because that is precisely the shape
  Berge's \<open>box\<close> hypothesis consumes downstream, and because it is what upper
  semicontinuity MEANS: \<open>{P. c \<le> g(P)}\<close> is closed under weak limits for every
  threshold \<open>c\<close>.
\<close>

lemma essinf_etime_usc:
  fixes T :: real and c :: ennreal and A :: "'b::polish_space set"
    and Ni :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and A: "open A"
    and wc: "weak_conv_on Ni N sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and pi: "\<And>i. prob_space (Ni i)" and pN: "prob_space N"
    and ge: "\<And>i. c \<le> ess_inf_time (Ni i) (etime T A (\<lambda>s w. w s))"
  shows "c \<le> ess_inf_time N (etime T A (\<lambda>s w. w s))"
proof -
  define S where "S = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}"
  have clS: "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) S"
    unfolding S_def by (rule etime_superlevel_closed[OF T A])
  have sN: "sets N = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and ev: "\<forall>\<^sub>F i in sequentially.
        sets (Ni i) = sets (borel_of
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> finite_measure (Ni i)"
    using wc[unfolded weak_conv_on_def] by blast+

  text \<open>Weak convergence only guarantees the \<open>sets\<close> equation EVENTUALLY, so the
    measurability facts below are stated under that hypothesis and discharged
    per index where needed.\<close>
  have Smeas: "S \<in> sets M" if "sets M = sets (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for M
    using borel_of_closed[OF clS] that by simp
  have Sspace: "{\<omega> \<in> space M. c \<le> ennreal (etime T A (\<lambda>s w. w s) \<omega>)} = S"
    if "sets M = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for M
  proof -
    have "space M = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using sets_eq_imp_space_eq[OF that] by (simp add: space_borel_of)
    thus ?thesis unfolding S_def by simp
  qed

  have oneN: "measure (Ni i) S = 1"
    if s: "sets (Ni i) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for i
  proof -
    have "measure (Ni i)
        {\<omega> \<in> space (Ni i). c \<le> ennreal (etime T A (\<lambda>s w. w s) \<omega>)} = 1"
      using ess_inf_time_ge_iff_measure[OF pi[of i]]
        Smeas[OF s] Sspace[OF s] ge[of i] by simp
    thus ?thesis unfolding Sspace[OF s] .
  qed

  text \<open>To feed \<open>weak_conv_closed_full_measure\<close>, which asks for full measure at
    EVERY index, replace the eventually-good tail by a shifted sequence. Weak
    convergence is invariant under dropping a finite prefix.\<close>
  obtain n0 where n0: "\<And>i. n0 \<le> i \<Longrightarrow>
      sets (Ni i) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
      \<and> finite_measure (Ni i)"
    using ev unfolding eventually_sequentially by blast
  have wc': "weak_conv_on (\<lambda>i. Ni (i + n0)) N sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F i in sequentially. sets (Ni (i + n0)) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> finite_measure (Ni (i + n0))"
      by (intro always_eventually allI n0) simp
    show "sets N = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      by (rule sN)
    show "finite_measure N" by (rule prob_space.finite_measure[OF pN])
    fix f :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
    assume f: "continuous_map
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) euclideanreal f"
      and b: "\<exists>B. \<forall>x \<in> topspace
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)). \<bar>f x\<bar> \<le> B"
    have "((\<lambda>i. \<integral>x. f x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. f x \<partial>N)) sequentially"
      using wc[unfolded weak_conv_on_def] f b by blast
    thus "((\<lambda>i. \<integral>x. f x \<partial>(Ni (i + n0)))
        \<longlongrightarrow> (\<integral>x. f x \<partial>N)) sequentially"
      by (rule LIMSEQ_ignore_initial_segment)
  qed
  have one': "measure (Ni (i + n0)) S = 1" for i
    by (rule oneN) (use n0[of "i + n0"] in simp)
  have "measure N S = 1"
    by (rule weak_conv_closed_full_measure[OF wc' clS one' pN])
  thus ?thesis
    using ess_inf_time_ge_iff_measure[OF pN] Smeas[OF sN] Sspace[OF sN] by simp
qed

subsection \<open>Item 2.4: a shift margin uniform over the sample space\<close>

text \<open>
  Larsson--Ruf get joint upper semicontinuity of \<open>f(x,P) = ((x + \<cdot>)\<^sub>*P)\<hyphen>essinf \<tau>\<^sub>K\<close>
  by asserting that \<open>(x,P) \<mapsto> (x + \<cdot>)\<^sub>*P\<close> is continuous. Berge's \<open>box\<close> hypothesis
  asks for much less --- only that \<open>f(x,P) < d\<close> PERSISTS on a product
  neighbourhood --- and unfolding that is far cheaper than proving continuity of
  the pushforward map.

  The obstruction is uniformity. \<open>f(x,P) < d\<close> says the event
  \<open>{\<omega> : \<tau>\<^sub>K(x + \<omega>) < d}\<close> has positive mass, and by \<open>etime_less_iff\<close> each such \<open>\<omega>\<close>
  is witnessed by a time \<open>r < d\<close> with \<open>x + \<omega>(r) \<in> A\<close>. Each \<omega> then has its OWN
  room to move \<open>x\<close>, and a pointwise \<open>\<epsilon>(\<omega>)\<close> is worthless against a measure.

  The erosion operator fixes exactly this: \<open>eroded \<delta> A\<close> is open, exhausts \<open>A\<close>, and
  its margin \<open>\<delta>\<close> is the same at every point. Passing to an erosion costs only mass,
  and \<open>positive_mass_at_some_erosion\<close> says some level retains it.
\<close>

lemma open_shifted_eval_preimage:
  fixes T r :: real
    and U :: "'b::{polish_space,real_normed_vector} set" and x :: 'b
  assumes rT: "r \<in> {0..T}" and U: "open U"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). x + f r \<in> U}"
proof -
  have eq: "{z. x + z \<in> U} = (\<lambda>w. (- x) + w) ` U"
  proof
    show "{z. x + z \<in> U} \<subseteq> (\<lambda>w. (- x) + w) ` U"
    proof
      fix z assume "z \<in> {z. x + z \<in> U}"
      hence mem: "x + z \<in> U" by simp
      have "z = (- x) + (x + z)" by simp
      with mem show "z \<in> (\<lambda>w. (- x) + w) ` U" by blast
    qed
  next
    show "(\<lambda>w. (- x) + w) ` U \<subseteq> {z. x + z \<in> U}" by auto
  qed
  have op: "open {z. x + z \<in> U}"
    unfolding eq by (rule open_translation[OF U])
  have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). x + f r \<in> U}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). f r \<in> {z. x + z \<in> U}}"
    by simp
  thus ?thesis using open_eval_preimage[OF rT op] by simp
qed

text \<open>The margin itself. Note what does NOT appear: no property of \<open>\<omega>\<close> beyond the
  single evaluation \<open>\<omega>(r)\<close>, and no dependence of \<open>\<delta>\<close> on \<open>\<omega>\<close>.\<close>

lemma etime_shift_le_of_eroded:
  fixes A :: "'b::{polish_space,real_normed_vector} set"
  assumes T: "0 \<le> T" and rr: "0 \<le> r" "r \<le> T"
    and mem: "x + \<omega> r \<in> eroded \<delta> A"
    and near: "dist x y < \<delta>"
  shows "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
proof -
  have "dist (x + \<omega> r) (y + \<omega> r) < \<delta>" using near by simp
  from eroded_shift[OF mem this] have inA: "y + \<omega> r \<in> A" .
  text \<open>The conclusion has to drive the unification here. Chaining \<open>inA\<close> into the
    rule instead leaves \<open>?X r \<omega> \<in> A\<close> to be solved higher-order, which has several
    solutions and makes the step fail.\<close>
  show ?thesis
  proof (rule etime_le_of_mem)
    show "0 \<le> T" by (rule T)
    show "0 \<le> r" by (rule rr(1))
    show "r \<le> T" by (rule rr(2))
    show "y + \<omega> r \<in> A" by (rule inA)
  qed
qed

text \<open>The assembly. From a witness time \<open>r\<close> carrying positive mass we extract an
  OPEN set of paths, still of positive mass, on which the exit time stays below
  \<open>d\<close> for EVERY nearby starting point. Openness is what lets the second half of
  Berge's \<open>box\<close> --- moving the measure --- go through by Portmanteau.\<close>

lemma etime_shift_uniform_margin:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and sP: "sets P = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and r: "0 \<le> r" "r \<le> T" "r < d"
    and pos: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  have rT: "r \<in> {0..T}" using r by simp
  have opn: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         x + f r \<in> eroded (1 / Suc n) A}" for n :: nat
    by (rule open_shifted_eval_preimage[OF rT open_eroded])
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<in> sets P" for n :: nat
    using borel_of_open[OF opn[of n]] unfolding sP spP by simp
  obtain n :: nat where
    posn: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<noteq> 0"
    by (rule positive_mass_at_some_erosion[OF A meas pos, THEN exE])
  define G where "G = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      x + f r \<in> eroded (1 / Suc n) A}"
  have Gspace: "G = {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A}"
    unfolding G_def spP by simp
  have "(0::real) < 1 / Suc n" by simp
  moreover have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    unfolding G_def by (rule opn)
  moreover have "emeasure P G \<noteq> 0" unfolding Gspace by (rule posn)
  moreover have "etime T A (\<lambda>s w. y + w s) \<omega> < d"
    if near: "dist x y < 1 / Suc n" and \<omega>: "\<omega> \<in> G" for y \<omega>
  proof -
    have le: "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
    proof (rule etime_shift_le_of_eroded)
      show "0 \<le> T" by (rule T)
      show "0 \<le> r" by (rule r(1))
      show "r \<le> T" by (rule r(2))
      show "x + \<omega> r \<in> eroded (1 / Suc n) A" using \<omega> unfolding G_def by simp
      show "dist x y < 1 / Suc n" by (rule near)
    qed
    from le r(3) show ?thesis by linarith
  qed
  ultimately show ?thesis by blast
qed

text \<open>The countable reduction, at the level of measures. \<open>etime_less_iff_qtimes_open\<close>
  turns the event into a union over \<open>qtimes T\<close>, which is countable, so
  \<open>positive_of_countable_UN\<close> extracts a SINGLE witness time still carrying positive
  mass. Doing this before the erosion is not a matter of taste: the erosion step
  needs a fixed time \<open>r\<close> to erode around, and over the uncountable family of
  witness times no such extraction exists.\<close>

lemma positive_mass_at_some_qtime:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>r \<in> qtimes T. r < d
      \<and> emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  define R where "R = {r \<in> qtimes T. r < d}"
  have cR: "countable R" unfolding R_def using countable_qtimes by simp

  text \<open>The pointwise reduction, applied path by path. Continuity of the shifted
    path is what \<open>mspace_path_metricD\<close> supplies.\<close>
  have ptw: "etime T A (\<lambda>s w. x + w s) \<omega> < d
      \<longleftrightarrow> (\<exists>r \<in> R. x + \<omega> r \<in> A)"
    if w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for \<omega>
  proof -
    have cont: "continuous_on {0..T} (\<lambda>s. x + \<omega> s)"
      by (intro continuous_intros mspace_path_metricD[OF w])
    text \<open>\<open>etime\<close> only ever applies its process to the ONE path \<open>\<omega>\<close>, so freezing
      the path inside the process changes nothing --- but it does change the
      term, and the reduction lemma is stated for a frozen process.\<close>
    have eq: "etime T A (\<lambda>s w. x + w s) \<omega> = etime T A (\<lambda>s w'. x + \<omega> s) \<omega>"
      unfolding etime_def by simp
    show ?thesis
      unfolding eq R_def
      using etime_less_iff_qtimes_open[OF T A dT cont, of \<omega>] by auto
  qed
  have split: "{\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d}
      = (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A})"
    using ptw unfolding spP by blast

  text \<open>Measurability of each slice comes from openness of the shifted evaluation
    preimage, exactly as in \<open>etime_shift_uniform_margin\<close>.\<close>
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> A} \<in> sets P" if r: "r \<in> R" for r
  proof -
    have "r \<in> qtimes T" using r unfolding R_def by simp
    hence rT: "r \<in> {0..T}" using qtimes_subset[OF T] by blast
    have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). x + f r \<in> A}"
      by (rule open_shifted_eval_preimage[OF rT A])
    from borel_of_open[OF this] show ?thesis unfolding sP spP by simp
  qed
  have "emeasure P (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A}) \<noteq> 0"
    using pos unfolding split .
  from positive_of_countable_UN[OF cR meas this] show ?thesis
    unfolding R_def by blast
qed

text \<open>Both halves of item 2.4's \<open>x\<close>-perturbation, in one statement: from
  \<open>f(x,P) < d\<close> alone --- no continuity of the pushforward map, no joint
  continuity --- we get an OPEN set of paths of positive \<open>P\<close>-mass on which the
  exit time stays below \<open>d\<close> for every starting point within \<open>\<delta>\<close> of \<open>x\<close>.\<close>

theorem etime_shift_box_half:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  obtain r where r: "r \<in> qtimes T" "r < d"
    and posr: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
    using positive_mass_at_some_qtime[OF T A dT sP pos] by blast
  have rT: "r \<in> {0..T}" using qtimes_subset[OF T] r(1) by blast
  show ?thesis
  proof (rule etime_shift_uniform_margin[OF T A sP])
    show "0 \<le> r" using rT by simp
    show "r \<le> T" using rT by simp
    show "r < d" by (rule r(2))
    show "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0" by (rule posr)
  qed
qed

text \<open>The same decomposition, used for measurability rather than for extraction:
  the event \<open>{\<tau>\<^sub>K(y + \<cdot>) < d}\<close> is a COUNTABLE union of open sets, hence open, hence
  Borel. Without this the final monotonicity step below has no set to be
  monotone into.\<close>

lemma open_etime_shift_less:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         etime T A (\<lambda>s w. y + w s) f < d}"
proof -
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        etime T A (\<lambda>s w. y + w s) f < d}
      = (\<Union>r \<in> {r \<in> qtimes T. r < d}.
           {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). y + f r \<in> A})"
  proof -
    have "etime T A (\<lambda>s w. y + w s) f < d
        \<longleftrightarrow> (\<exists>r \<in> {r \<in> qtimes T. r < d}. y + f r \<in> A)"
      if w: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for f
    proof -
      have cont: "continuous_on {0..T} (\<lambda>s. y + f s)"
        by (intro continuous_intros mspace_path_metricD[OF w])
      have e: "etime T A (\<lambda>s w. y + w s) f = etime T A (\<lambda>s w'. y + f s) f"
        unfolding etime_def by simp
      show ?thesis unfolding e
        using etime_less_iff_qtimes_open[OF T A dT cont, of f] by auto
    qed
    thus ?thesis by blast
  qed
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). y + f r \<in> A}"
    if r: "r \<in> {r \<in> qtimes T. r < d}" for r
  proof -
    have "r \<in> qtimes T" using r by simp
    hence rT: "r \<in> {0..T}" using qtimes_subset[OF T] by blast
    show ?thesis by (rule open_shifted_eval_preimage[OF rT A])
  qed
  show ?thesis unfolding eq by (rule openin_Union) (use op in blast)
qed

subsection \<open>Item 2.4 complete: Berge's box hypothesis for the shifted exit time\<close>

text \<open>
  Both perturbations at once, in the sequential form the Lévy--Prokhorov
  metrisation makes equivalent to the topological one. The strict inequality
  \<open>f(x,P) < d\<close> --- read as ``the event \<open>\<tau>\<^sub>K(x + \<cdot>) < d\<close> has positive mass'' ---
  persists when the starting point moves to any \<open>y\<^sub>i \<rightarrow> x\<close> AND the law moves to any
  \<open>Q\<^sub>i \<rightarrow> P\<close> weakly.

  Larsson--Ruf get this from continuity of \<open>(x,P) \<mapsto> (x + \<cdot>)\<^sub>*P\<close>; no such theorem
  is used here. The single set \<open>G\<close> does all the work: the erosion makes it survive
  moving \<open>x\<close>, and its openness makes it survive moving \<open>P\<close>. That is why the
  erosion had to be OPEN and not merely closed --- a closed eroded set would give
  the wrong Portmanteau direction.
\<close>

theorem etime_shift_box:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
    and x :: 'b and yi :: "nat \<Rightarrow> 'b"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and wc: "weak_conv_on Qi P sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and sQ: "\<And>i. sets (Qi i) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pQ: "\<And>i. prob_space (Qi i)" and pP: "prob_space P"
    and yconv: "yi \<longlonglongrightarrow> x"
    and pos: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "eventually (\<lambda>i. emeasure (Qi i)
      {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
proof -
  interpret PP: prob_space P by (rule pP)
  have sP: "sets P = sets (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    using wc[unfolded weak_conv_on_def] by blast
  obtain \<delta> G where d0: "0 < \<delta>"
    and Gopen: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    and Gpos: "emeasure P G \<noteq> 0"
    and marg: "\<And>y \<omega>. dist x y < \<delta> \<Longrightarrow> \<omega> \<in> G
        \<Longrightarrow> etime T A (\<lambda>s w. y + w s) \<omega> < d"
    using etime_shift_box_half[OF T A dT sP pos] by blast
  have GP: "0 < measure P G"
  proof (rule ccontr)
    assume "\<not> 0 < measure P G"
    hence "measure P G = 0" using measure_nonneg[of P G] by linarith
    hence "ennreal (measure P G) = 0" by simp
    thus False using Gpos PP.emeasure_eq_measure by simp
  qed
  have ev1: "eventually (\<lambda>i. 0 < measure (Qi i) G) sequentially"
    by (rule weak_conv_open_positive_eventually[OF wc Gopen GP sQ pQ pP])
  have ev2: "eventually (\<lambda>i. dist x (yi i) < \<delta>) sequentially"
    using tendstoD[OF yconv d0] by (simp add: dist_commute)
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF ev1 ev2]])
    fix i
    assume h: "0 < measure (Qi i) G \<and> dist x (yi i) < \<delta>"
    interpret QQ: prob_space "Qi i" by (rule pQ)
    have spQ: "space (Qi i) = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using sets_eq_imp_space_eq[OF sQ[of i]] by (simp add: space_borel_of)
    have Gsub: "G \<subseteq> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using openin_subset[OF Gopen] by simp
    have sub: "G \<subseteq> {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
    proof
      fix \<omega> assume w: "\<omega> \<in> G"
      have "etime T A (\<lambda>s w. yi i + w s) \<omega> < d"
        using marg[OF _ w] h by simp
      thus "\<omega> \<in> {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
        using w Gsub spQ by auto
    qed
    have meas: "{\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}
        \<in> sets (Qi i)"
      using borel_of_open[OF open_etime_shift_less[OF T A dT]]
      unfolding sQ spQ by simp
    have "emeasure (Qi i) G \<noteq> 0"
      using h QQ.emeasure_eq_measure by simp
    moreover have "emeasure (Qi i) G
        \<le> emeasure (Qi i) {\<omega> \<in> space (Qi i).
             etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
      by (rule emeasure_mono[OF sub meas])
    ultimately show "emeasure (Qi i) {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0" by auto
  qed
qed

end
