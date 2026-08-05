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

subsection \<open>Item 2.6: upper semicontinuity of the supremum over a compact family\<close>

text \<open>
  The value functional, real-valued. \<open>ess_inf_time\<close> is \<open>ennreal\<close>-valued and Berge's
  supremum has to be a real number; the conversion is faithful because the exit
  time is capped at \<open>T\<close>, so the essential infimum is never \<open>\<top>\<close>.
\<close>

definition vshift :: "real \<Rightarrow> 'b::{polish_space,real_normed_vector} set
    \<Rightarrow> 'b \<Rightarrow> (real \<Rightarrow> 'b) measure \<Rightarrow> real" where
  "vshift T A y Q = enn2real (ess_inf_time Q (etime T A (\<lambda>s w. y + w s)))"

lemma vshift_le:
  fixes A :: "'b::{polish_space,real_normed_vector} set"
  assumes T: "0 \<le> T" and Q: "prob_space Q"
  shows "vshift T A y Q \<le> T"
proof -
  have "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF Q]) (rule etime_le_T[OF T])
  from enn2real_mono[OF this] show ?thesis
    unfolding vshift_def using T by simp
qed

text \<open>The bridge from the real-valued functional back to the positive-mass
  statement the two halves of item 2.4 speak. Both directions of the \<open>ennreal\<close>
  conversion need the ceiling: without it \<open>enn2real\<close> could collapse \<open>\<top>\<close> to \<open>0\<close> and
  the strict inequality would be an artefact.\<close>

lemma vshift_less_iff_positive_mass:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and Q :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d" and d0: "0 \<le> d"
    and sQ: "sets Q = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pQ: "prob_space Q"
  shows "vshift T A y Q < d
      \<longleftrightarrow> emeasure Q {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d} \<noteq> 0"
proof -
  have spQ: "space Q = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sQ] by (simp add: space_borel_of)
  have setseq: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      = {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d}"
    using etime_nonneg[OF T, of A "\<lambda>s w. y + w s"]
    by (auto simp: ennreal_less_iff)
  have meas: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      \<in> sets Q"
    unfolding setseq
    using borel_of_open[OF open_etime_shift_less[OF T A dT]]
    unfolding sQ spQ by simp
  have le: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF pQ]) (rule etime_le_T[OF T])
  have fin: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < \<top>"
    using le ennreal_less_top by (rule order_le_less_trans)
  have "vshift T A y Q < d
      \<longleftrightarrow> ennreal (vshift T A y Q) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_less_iff)
  also have "\<dots> \<longleftrightarrow> ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_enn2real[OF fin])
  also have "\<dots> \<longleftrightarrow> emeasure Q
      {\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d} \<noteq> 0"
    by (rule ess_inf_time_less_iff[OF meas])
  finally show ?thesis unfolding setseq .
qed

text \<open>
  Item 2.6 --- and, granted Lemma 2.3, clause (1) of Theorem 1.1. The supremum
  of \<open>P \<mapsto> P\<hyphen>essinf \<tau>\<^sub>K(x + \<cdot>)\<close> over a weakly compact family of laws is upper
  semicontinuous in the starting point \<open>x\<close>.

  Every hypothesis of Berge is discharged here EXCEPT compactness of the family,
  which is Lemma 2.3 and is assumed. That is the honest statement of where the
  development stands: the semicontinuity argument is complete, and the only
  outstanding input is that \<open>\<P>\<^sub>0\<close> is weakly compact.
\<close>

theorem vshift_sup_usc:
  fixes T c :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and cC: "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof (rule usc_sup_over_compactin)
  show "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule cC)
  show "C \<noteq> {}" by (rule neC)
  show "bdd_above (vshift T A y ` C)" for y
    by (rule bdd_aboveI2[of _ _ T]) (use vshift_le[OF T] pC in blast)
  show "Sup (vshift T A x ` C) < c" by (rule lt)
next
  fix P :: "(real \<Rightarrow> 'b) measure" and d :: real
  assume P: "P \<in> C" and small: "vshift T A x P < d"
  have d0: "0 \<le> d"
  proof -
    have "0 \<le> vshift T A x P" unfolding vshift_def by simp
    with small show ?thesis by linarith
  qed
  show "\<exists>U V. open U \<and> openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) V
      \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. vshift T A y Q < d)"
  proof (cases "T < d")
    text \<open>Berge quantifies \<open>box\<close> over EVERY threshold above \<open>vshift T A x P\<close>, and a
      threshold beyond \<open>T\<close> is not excluded by anything --- \<open>vshift\<close> could be \<open>0\<close>
      while \<open>d\<close> is huge. That branch is trivial rather than impossible: the exit
      time never exceeds \<open>T\<close>, so the whole space works. It has to be split off
      because the witness machinery of item 2.4 assumes \<open>\<not> T < d\<close> throughout.\<close>
    case True
    have allQ: "vshift T A y Q < d" if "Q \<in> C" for y Q
    proof -
      have "vshift T A y Q \<le> T" by (rule vshift_le[OF T pC[OF that]])
      with True show ?thesis by linarith
    qed
    have oT: "openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        (topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))"
      by (rule openin_topspace)
    have Ptop: "P \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    text \<open>The witnesses have to be handed over explicitly. Left to invent
      \<open>U = UNIV\<close> and \<open>V = topspace\<close> for itself, \<open>blast\<close> does not terminate.\<close>
    have inst: "open (UNIV :: 'b set)
        \<and> openin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
           (topspace (weak_conv_topology
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))
        \<and> x \<in> (UNIV :: 'b set)
        \<and> P \<in> topspace (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> (\<forall>y \<in> (UNIV :: 'b set).
             \<forall>Q \<in> topspace (weak_conv_topology
                 (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) \<inter> C.
               vshift T A y Q < d)"
      using oT Ptop allQ by simp
    thus ?thesis by blast
  next
    case False
    hence dT: "\<not> T < d" by simp
    have posP: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
      using small
      unfolding vshift_less_iff_positive_mass[OF T A dT d0 sC[OF P] pC[OF P]] .
    show ?thesis
    proof (rule box_of_sequential_euclidean)
      show "metrizable_space (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        by (rule metrizable_weak_conv_path_topology)
      show "P \<in> topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    next
      fix yi :: "nat \<Rightarrow> 'b" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
      assume yconv: "yi \<longlonglongrightarrow> x"
        and lQ: "limitin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) Qi P sequentially"
        and inC: "\<And>i. Qi i \<in> C"
      text \<open>\<open>weak_conv_on\<close> IS \<open>limitin (weak_conv_topology \<dots>)\<close> by definition. The
        membership \<open>Qi i \<in> C\<close> is what cannot be dropped: \<open>etime_shift_box\<close> needs each
        \<open>Qi i\<close> to be a PROBABILITY measure, and an arbitrary measure near \<open>P\<close> in the
        weak topology is only a finite one.\<close>
      have wc: "weak_conv_on Qi P sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
        using lQ .
      have sQi: "sets (Qi i) = sets (borel_of
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for i
        by (rule sC[OF inC])
      have pQi: "prob_space (Qi i)" for i by (rule pC[OF inC])
      have ev: "eventually (\<lambda>i. emeasure (Qi i)
          {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
        by (rule etime_shift_box[OF T A dT wc sQi pQi pC[OF P] yconv posP])
      show "eventually (\<lambda>i. vshift T A (yi i) (Qi i) < d) sequentially"
      proof (rule eventually_mono[OF ev])
        fix i
        assume "emeasure (Qi i)
            {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0"
        thus "vshift T A (yi i) (Qi i) < d"
          unfolding vshift_less_iff_positive_mass[OF T A dT d0
              sC[OF inC] pC[OF inC]] .
      qed
    qed
  qed
qed

text \<open>
  The interface to Lemma 2.3, stated so that its eventual proof has exactly one
  obligation. Lemmas 2.2 and 2.3 of arXiv:2512.17702 together say precisely that
  \<open>\<P>\<^sub>0\<close> is SEQUENTIALLY compact for weak convergence: 2.2 extracts a convergent
  subsequence from any sequence of laws, 2.3 puts the limit back into the set.
  That is the \<open>seq\<close> hypothesis below verbatim, and nothing else about \<open>\<P>\<^sub>0\<close> is
  used.

  Note what does NOT have to be assumed: the family being a subset of the weak
  topology's carrier is derivable, since a probability measure on the path
  \<open>\<sigma>\<close>-algebra is in particular a finite measure with the right \<open>sets\<close>.
\<close>

corollary vshift_sup_usc_of_seq_compact:
  fixes T c :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and seq: "\<And>\<sigma> :: nat \<Rightarrow> (real \<Rightarrow> 'b) measure. range \<sigma> \<subseteq> C \<Longrightarrow>
        \<exists>L r. L \<in> C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) L sequentially
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof -
  have sub: "C \<subseteq> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
  proof
    fix Q assume Q: "Q \<in> C"
    show "Q \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF Q] prob_space.finite_measure[OF pC[OF Q]] by simp
  qed
  have cC: "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule compactin_of_seq_compact[OF metrizable_weak_conv_path_topology sub])
       (use seq in blast)
  show ?thesis by (rule vshift_sup_usc[OF T A cC neC sC pC lt])
qed

subsection \<open>From a market to its law: transferring the exit time\<close>

text \<open>
  \<open>vshift\<close> and everything above it speak about LAWS on the path space, while the
  repository's value function \<open>Value_Function.val_fn\<close> is a supremum over MARKETS
  --- a measure, a filtration, a process and a covariation. \<open>Path_Space.path_law\<close>
  is the bridge between the two, and these lemmas carry the essential infimum of
  the exit time across it.

  Nothing here is deep, but it cannot be skipped: without it the semicontinuity
  results proved above are statements about a set of measures that has not been
  connected to \<open>\<P>\<^sub>x\<close>.
\<close>

lemma etime_shift_superlevel_closed:
  fixes T :: real and c :: ennreal
    and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}"
proof -
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         ennreal (etime T A (\<lambda>s w. y + w s) f) < c}"
  proof (cases "ennreal T < c")
    text \<open>One split, on whether the threshold is beyond the cap, rather than the
      two that \<open>ennreal_cases\<close> would give: above the cap EVERY path qualifies,
      and below it the threshold is automatically a real \<open>r\<close> with \<open>\<not> T < r\<close>,
      which is exactly the hypothesis \<open>open_etime_shift_less\<close> wants.\<close>
    case True
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          ennreal (etime T A (\<lambda>s w. y + w s) f) < c}
        = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    proof -
      have "ennreal (etime T A (\<lambda>s w. y + w s) f) < c" for f
      proof -
        have "etime T A (\<lambda>s w. y + w s) f \<le> T" by (rule etime_le_T[OF T])
        hence "ennreal (etime T A (\<lambda>s w. y + w s) f) \<le> ennreal T"
          by (rule ennreal_leI)
        thus ?thesis using True by (rule order_le_less_trans)
      qed
      thus ?thesis by blast
    qed
    then show ?thesis
      using openin_topspace[of
          "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)"]
      by simp
  next
    case False
    hence cT: "c \<le> ennreal T" by simp
    then obtain r where r: "0 \<le> r" "c = ennreal r"
      by (cases c rule: ennreal_cases) (auto simp: top_unique)
    have rT: "\<not> T < r"
    proof
      assume "T < r"
      hence "ennreal T < ennreal r" using T by (simp add: ennreal_less_iff)
      thus False using False r(2) by simp
    qed
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          ennreal (etime T A (\<lambda>s w. y + w s) f) < c}
        = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          etime T A (\<lambda>s w. y + w s) f < r}"
      unfolding r(2)
      using etime_nonneg[OF T, of A "\<lambda>s w. y + w s"]
      by (auto simp: ennreal_less_iff)
    then show ?thesis by (simp add: open_etime_shift_less[OF T A rT])
  qed
  have compl: "topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. y + w s) f) < c}"
    by (auto simp: not_le)
  show ?thesis
    unfolding closedin_def using op unfolding compl by auto
qed

lemma ess_inf_time_distr:
  assumes fm: "f \<in> M \<rightarrow>\<^sub>M N"
    and meas: "\<And>c :: ennreal. {\<omega> \<in> space N. c \<le> ennreal (tau \<omega>)} \<in> sets N"
  shows "ess_inf_time (distr M N f) tau = ess_inf_time M (\<lambda>\<omega>. tau (f \<omega>))"
  unfolding ess_inf_time_def
proof (rule arg_cong[where f = Sup])
  show "{c. AE \<omega> in distr M N f. c \<le> ennreal (tau \<omega>)}
      = {c. AE \<omega> in M. c \<le> ennreal (tau (f \<omega>))}"
    using AE_distr_iff[OF fm meas] by blast
qed

text \<open>The exit time does not notice the restriction to \<open>{0..T}\<close> that \<open>path_law\<close>
  performs, because it only ever inspects times in \<open>[0,T]\<close>.\<close>

lemma etime_shift_of_restrict:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{polish_space,real_normed_vector}" and y :: 'b
  shows "etime T A (\<lambda>s w. y + w s) (restrict (\<lambda>t. X t \<omega>) {0..T})
       = etime T A (\<lambda>s \<omega>'. y + X s \<omega>') \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> y + restrict (\<lambda>t. X t \<omega>) {0..T} r \<in> A}
      = {r. 0 \<le> r \<and> r \<le> T \<and> y + X r \<omega> \<in> A}"
    by (auto simp: restrict_def)
  thus ?thesis unfolding etime_def by simp
qed

theorem vshift_path_law:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{polish_space,real_normed_vector}" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and Xm: "\<And>t. t \<in> {0..T} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
  shows "vshift T A y (path_law M X T)
       = enn2real (ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>')))"
proof -
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})
      \<in> M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    by (rule pathify_measurable[OF T Xm cont])
  have meas: "{\<omega> \<in> space (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))).
        c \<le> ennreal (etime T A (\<lambda>s w. y + w s) \<omega>)}
      \<in> sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    for c :: ennreal
    using borel_of_closed[OF etime_shift_superlevel_closed[OF T A, of c y]]
    by (simp add: space_borel_of)
  have "ess_inf_time (path_law M X T) (etime T A (\<lambda>s w. y + w s))
      = ess_inf_time M
          (\<lambda>\<omega>. etime T A (\<lambda>s w. y + w s) (restrict (\<lambda>t. X t \<omega>) {0..T}))"
    unfolding path_law_def by (rule ess_inf_time_distr[OF pm meas])
  also have "\<dots> = ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>'))"
    by (simp add: etime_shift_of_restrict)
  finally show ?thesis unfolding vshift_def by simp
qed

section \<open>Lemma 2.3: the compact family of laws for clause (1)\<close>

text \<open>The single obligation of \<open>vshift_sup_usc_of_seq_compact\<close> asks for a
  family of laws in which every sequence has a weakly convergent subsequence
  WITH LIMIT IN THE FAMILY.  Lemma 2.2 (the market form,
  \<open>market_path_laws_convergent_subsequence\<close>) provides the subsequence for
  sequences of market path laws; Lemma 2.3 must put the limit back.  The
  family below makes that step definitional: take the WEAK CLOSURE of the
  market path laws.  Sequential compactness of the closure needs nothing
  beyond the extraction property of the base set and metrizability of the
  weak topology (\<open>seq_compact_closure_of\<close>), and every closure point is a
  probability measure with the right \<open>sets\<close> because total mass survives weak
  limits.

  What this does NOT settle is that the closure adds no VALUE: identifying
  \<open>Sup (vshift T A x ` mkt_law_closure \<dots>)\<close> with the market-form value
  function \<open>val_fn\<close> is the pushforward analysis of Larsson--Ruf
  Proposition 2.2 and remains open.  The theorem at the end of this section
  is clause (1) of Theorem 1.1 for the LAW-LEVEL value function of the
  closure, with no compactness hypothesis left.\<close>

definition mkt_law_witness ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> real
     \<Rightarrow> (real \<Rightarrow> real^'m) measure \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) measure
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) measure)
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'m)
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'m^'m)
     \<Rightarrow> (('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> bool"
  where
  "mkt_law_witness k L K x0 T Q M F X acov tau \<longleftrightarrow>
     Q = path_law M X T
     \<and> sufficiently_volatile_market M F X acov k L K x0 tau
     \<and> (\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>)
     \<and> (\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> tau \<omega> < s \<longrightarrow> acov s \<omega> = 0)
     \<and> (AE \<omega> in M. \<forall>l t. 0 \<le> t \<longrightarrow>
           set_integrable lborel {0..t} (\<lambda>s. acov s \<omega> $ l $ l))"

definition mkt_path_laws ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> real
     \<Rightarrow> (real \<Rightarrow> real^'m) measure set"
  where
  "mkt_path_laws k L K x0 T =
     {Q. \<exists>M F X acov tau. mkt_law_witness k L K x0 T Q M F X acov tau}"

text \<open>The four side conditions beyond the locale are part of the paper's
  class (1.7): the process is stopped at its horizon, the covariance
  vanishes after it, and its diagonal entries are pathwise integrable.\<close>

lemma mkt_path_laws_prob:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> mkt_path_laws k L K x0 T"
  shows "prob_space Q"
proof -
  from Q obtain M F X acov tau
    where W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  have QM: "Q = path_law M X T"
    and svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have Xm: "X t \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that by (intro sv.random_variable) simp
  have cont: "continuous_on {0..T} (\<lambda>t. X t \<omega>)" if "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
  show ?thesis
    unfolding QM by (rule prob_space_path_law[OF sv.prob_space_M T Xm cont])
qed

lemma mkt_path_laws_sets:
  assumes "Q \<in> mkt_path_laws k L K x0 T"
  shows "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m::finite) metric)))"
  using assms unfolding mkt_path_laws_def mkt_law_witness_def by auto

lemma mkt_path_laws_topspace:
  assumes T: "0 \<le> T"
  shows "mkt_path_laws k L K x0 T \<subseteq> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m::finite) metric)))"
proof
  fix Q assume Q: "Q \<in> mkt_path_laws k L K x0 T"
  have fin: "finite_measure Q"
    by (rule prob_space.finite_measure[OF mkt_path_laws_prob[OF T Q]])
  show "Q \<in> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using fin mkt_path_laws_sets[OF Q] by simp
qed

text \<open>Lemma 2.2, restated for members of the family: unpack the defining
  markets by choice and hand them to the tightness package.\<close>

lemma mkt_path_laws_seq_extraction:
  fixes \<sigma> :: "nat \<Rightarrow> (real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r"
    and rng: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
  shows "\<exists>N \<rho>. N \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
      \<and> strict_mono \<rho>
      \<and> weak_conv_on (\<sigma> \<circ> \<rho>) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof -
  have H: "\<exists>M F X acov tau. mkt_law_witness k L K x0 T (\<sigma> i) M F X acov tau"
    for i
    using rng unfolding mkt_path_laws_def mem_Collect_eq by blast
  define MM where "MM = (\<lambda>i. SOME M. \<exists>F X acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) M F X acov tau)"
  have exM: "\<exists>F X acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) F X acov tau" for i
    unfolding MM_def by (rule someI_ex[OF H])
  define FF where "FF = (\<lambda>i. SOME F. \<exists>X acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) F X acov tau)"
  have exF: "\<exists>X acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) X acov tau" for i
    unfolding FF_def by (rule someI_ex[OF exM])
  define XX where "XX = (\<lambda>i. SOME X. \<exists>acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) X acov tau)"
  have exX: "\<exists>acov tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) (XX i) acov tau" for i
    unfolding XX_def by (rule someI_ex[OF exF])
  define aa where "aa = (\<lambda>i. SOME acov. \<exists>tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) (XX i) acov tau)"
  have exA: "\<exists>tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) (XX i) (aa i) tau" for i
    unfolding aa_def by (rule someI_ex[OF exX])
  define tt where "tt = (\<lambda>i. SOME tau.
      mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) (XX i) (aa i) tau)"
  have Wi: "mkt_law_witness k L K x0 T (\<sigma> i) (MM i) (FF i) (XX i) (aa i) (tt i)"
    for i
    unfolding tt_def by (rule someI_ex[OF exA])
  have c1: "\<And>i. \<sigma> i = path_law (MM i) (XX i) T"
    using Wi unfolding mkt_law_witness_def by blast
  have c2: "\<And>i. sufficiently_volatile_market (MM i) (FF i) (XX i) (aa i)
      k L K x0 (tt i)"
    using Wi unfolding mkt_law_witness_def by blast
  have c3: "\<And>i s \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow>
      XX i s \<omega> = XX i (min s (tt i \<omega>)) \<omega>"
    using Wi unfolding mkt_law_witness_def by blast
  have c4: "\<And>i s \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> tt i \<omega> < s \<Longrightarrow>
      aa i s \<omega> = 0"
    using Wi unfolding mkt_law_witness_def by blast
  have c5: "\<And>i. AE \<omega> in MM i. \<forall>l t. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. aa i s \<omega> $ l $ l)"
    using Wi unfolding mkt_law_witness_def by blast
  obtain a N where aN1: "strict_mono a" and aN2: "finite_measure N"
    and aN3: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    and aN5: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N
        sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    using market_path_laws_convergent_subsequence[where MM = MM and FF = FF
        and XX = XX and aa = aa and tt = tt, OF c2 c3 c4 Kball c5 T]
    by blast
  have "\<sigma> \<circ> a = (\<lambda>i. path_law (MM i) (XX i) T) \<circ> a"
    by (intro ext) (simp add: c1)
  then have "weak_conv_on (\<sigma> \<circ> a) N sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    using aN5 by simp
  moreover have "N \<in> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using aN2 aN3 by simp
  ultimately show ?thesis using aN1 by blast
qed

subsection \<open>The closure and its properties\<close>

definition mkt_law_closure ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> real
     \<Rightarrow> (real \<Rightarrow> real^'m) measure set"
  where
  "mkt_law_closure k L K x0 T =
     (weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric)))
       closure_of (mkt_path_laws k L K x0 T)"

lemma mkt_path_laws_subset_closure:
  assumes T: "0 \<le> T"
  shows "mkt_path_laws k L K x0 T \<subseteq> mkt_law_closure k L K x0 T"
  unfolding mkt_law_closure_def
  by (rule closure_of_subset[OF mkt_path_laws_topspace[OF T]])

lemma mkt_law_closure_sets:
  assumes "Q \<in> mkt_law_closure k L K x0 T"
  shows "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m::finite) metric)))"
  using closure_of_subset_topspace assms
  unfolding mkt_law_closure_def by fastforce

lemma mkt_law_closure_finite:
  assumes "Q \<in> mkt_law_closure k L K x0 T"
  shows "finite_measure Q"
  using closure_of_subset_topspace assms
  unfolding mkt_law_closure_def by fastforce

text \<open>Total mass survives a weak limit: test against the constant \<open>1\<close>.\<close>

lemma weak_conv_on_prob_limit:
  fixes X :: "'b topology"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and P: "\<And>i. prob_space (Ni i)"
  shows "prob_space N"
proof -
  have fin: "finite_measure N"
    using wc unfolding weak_conv_on_def by blast
  have cm: "continuous_map X euclideanreal (\<lambda>_. 1 :: real)"
    by simp
  have bd: "\<exists>B. \<forall>x\<in>topspace X. \<bar>(\<lambda>_. 1 :: real) x\<bar> \<le> B"
    by (intro exI[of _ 1]) simp
  have lim: "(\<lambda>i. \<integral>x. (1 :: real) \<partial>(Ni i)) \<longlonglongrightarrow> (\<integral>x. (1 :: real) \<partial>N)"
    using wc cm bd unfolding weak_conv_on_def by blast
  have one: "(\<integral>x. (1 :: real) \<partial>(Ni i)) = 1" for i
    using prob_space.prob_space[OF P] by simp
  have "(\<integral>x. (1 :: real) \<partial>N) = 1"
    using LIMSEQ_unique[OF lim] one tendsto_const[of "1 :: real"] by simp
  then have m1: "measure N (space N) = 1"
    by simp
  show ?thesis
    by (intro prob_spaceI)
      (simp add: finite_measure.emeasure_eq_measure[OF fin] m1)
qed

lemma mkt_law_closure_prob:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and Q: "Q \<in> mkt_law_closure k L K x0 T"
  shows "prob_space Q"
proof -
  obtain \<sigma> where r\<sigma>: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
    and lim: "limitin (weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric))) \<sigma> Q sequentially"
    using closure_of_sequential_limit[OF metrizable_weak_conv_path_topology
        Q[unfolded mkt_law_closure_def]] by blast
  have Pi: "prob_space (\<sigma> i)" for i
    using r\<sigma> by (intro mkt_path_laws_prob[OF T]) blast
  show ?thesis
    by (rule weak_conv_on_prob_limit[OF lim Pi])
qed

text \<open>Sequential compactness of the closure: approximate, extract on the
  base family by Lemma 2.2, carry the limit across.\<close>

theorem mkt_law_closure_seq_compact:
  fixes \<tau> :: "nat \<Rightarrow> (real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r"
    and rng: "range \<tau> \<subseteq> mkt_law_closure k L K x0 T"
  shows "\<exists>N \<rho>. N \<in> mkt_law_closure k L K x0 T \<and> strict_mono \<rho>
      \<and> weak_conv_on (\<tau> \<circ> \<rho>) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
  unfolding mkt_law_closure_def
  by (rule seq_compact_closure_of[where Y = "weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric))"
      and A = "mkt_path_laws k L K x0 T" and \<tau> = \<tau>,
      OF metrizable_weak_conv_path_topology
      mkt_path_laws_topspace[OF T]
      mkt_path_laws_seq_extraction[OF T Kball]
      rng[unfolded mkt_law_closure_def]])

subsection \<open>Clause (1) for the law-level value function, unconditional\<close>

theorem vshift_sup_usc_mkt:
  fixes T c :: real and A :: "(real^'m::finite) set" and x :: "real^'m"
  assumes T: "0 \<le> T" and A: "open A"
    and ne: "mkt_path_laws k L K x0 T \<noteq> {}"
    and Kball: "K \<subseteq> cball 0 r"
    and lt: "Sup (vshift T A x ` mkt_law_closure k L K x0 T) < c"
  shows "eventually
      (\<lambda>y. Sup (vshift T A y ` mkt_law_closure k L K x0 T) < c) (nhds x)"
proof (rule vshift_sup_usc_of_seq_compact[OF T A])
  show "mkt_law_closure k L K x0 T \<noteq> {}"
    using mkt_path_laws_subset_closure[OF T] ne by blast
  show "\<And>Q. Q \<in> mkt_law_closure k L K x0 T \<Longrightarrow>
      sets Q = sets (borel_of (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    by (rule mkt_law_closure_sets)
  show "\<And>Q. Q \<in> mkt_law_closure k L K x0 T \<Longrightarrow> prob_space Q"
    by (rule mkt_law_closure_prob[OF T])
  show "\<And>\<sigma> :: nat \<Rightarrow> (real \<Rightarrow> real^'m) measure.
      range \<sigma> \<subseteq> mkt_law_closure k L K x0 T \<Longrightarrow>
      \<exists>N \<rho>. N \<in> mkt_law_closure k L K x0 T \<and> strict_mono \<rho>
          \<and> weak_conv_on (\<sigma> \<circ> \<rho>) N sequentially
              (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule mkt_law_closure_seq_compact[OF T Kball])
  show "Sup (vshift T A x ` mkt_law_closure k L K x0 T) < c"
    by (rule lt)
qed

subsection \<open>N1: the family is nonempty --- the immediate-stop market\<close>

text \<open>The market that stops at time \<open>0\<close>: the state is the constant \<open>x0\<close>, the
  horizon is \<open>0\<close>, and the covariance is \<open>mat 1\<close> at the single instant \<open>s = 0\<close>
  and \<open>0\<close> afterwards.  The eigenvalue constraints are only imposed on
  \<open>[0, tau]\<close> = \<open>{0}\<close>, where \<open>mat 1\<close> satisfies them; the compensator integrals
  all vanish because the covariance is supported on a Lebesgue-null set.  The
  filtration is the constant one.\<close>

lemma set_integral_at_origin:
  fixes c t :: real
  shows "set_integrable lborel {0..t} (\<lambda>s. if s = 0 then c else 0)"
    and "set_lebesgue_integral lborel {0..t} (\<lambda>s. if s = 0 then c else 0) = 0"
proof -
  have m: "(\<lambda>s :: real. indicator {0..t} s *\<^sub>R (if s = 0 then c else 0))
      \<in> borel_measurable lborel"
    by measurable
  have ae: "AE s in lborel.
      indicator {0..t} s *\<^sub>R (if s = 0 then c else 0) = (0 :: real)"
    using AE_lborel_singleton[of 0] by eventually_elim auto
  have "integrable lborel
      (\<lambda>s :: real. indicator {0..t} s *\<^sub>R (if s = 0 then c else 0))"
    using integrable_cong_AE[OF m borel_measurable_const ae] by simp
  then show "set_integrable lborel {0..t} (\<lambda>s. if s = 0 then c else 0)"
    unfolding set_integrable_def .
  show "set_lebesgue_integral lborel {0..t}
      (\<lambda>s. if s = 0 then c else 0) = 0"
    unfolding set_lebesgue_integral_def
    using integral_cong_AE[OF m borel_measurable_const ae] by simp
qed

theorem mkt_path_laws_nonempty:
  fixes x0 :: "real^'m::finite" and K :: "(real^'m) set"
  assumes k: "1 \<le> k" "k < CARD('m)" and L: "1 \<le> L" and x0K: "x0 \<in> K"
  shows "mkt_path_laws k L K x0 T \<noteq> {}"
proof -
  let ?M = "bm_paths :: ('m \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "\<lambda>_ :: real. bm_paths :: ('m \<Rightarrow> real \<Rightarrow> real) measure"
  let ?X = "\<lambda>(s :: real) (\<omega> :: 'm \<Rightarrow> real \<Rightarrow> real). x0"
  let ?acov = "\<lambda>(s :: real) (\<omega> :: 'm \<Rightarrow> real \<Rightarrow> real).
      if s = 0 then mat 1 :: real^'m^'m else 0"
  let ?tau = "\<lambda>\<omega> :: 'm \<Rightarrow> real \<Rightarrow> real. 0 :: real"
  have fin: "finite_measure ?M"
    by (rule prob_space.finite_measure) simp
  have sub: "subalgebra ?M ?M"
    by (simp add: subalgebra_def)
  have fm: "filtered_measure ?M ?F 0"
    by unfold_locales (simp_all add: subalgebra_def)
  have sff: "sigma_finite_filtered_measure ?M ?F 0"
    by (intro sigma_finite_filtered_measure.intro fm
        sigma_finite_filtered_measure_axioms.intro
        finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fin sub)
  interpret SFF: sigma_finite_filtered_measure ?M ?F 0
    by (rule sff)
  have mgX: "martingale ?M ?F 0 ?X"
    by (intro SFF.martingale_const_fun BMP.integrable_const
        borel_measurable_const)
  have entry: "(?acov s \<omega>) $ l $ l = (if s = 0 then 1 else 0)"
    for s :: real and l :: 'm and \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real"
    by (simp add: mat_def)
  have tr: "trace (?acov s \<omega>) = (if s = 0 then real CARD('m) else 0)"
    for s :: real and \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real"
  proof (cases "s = 0")
    case True
    then show ?thesis by (simp add: trace_mat1)
  next
    case False
    then show ?thesis by (simp add: trace_def)
  qed
  have comp0: "set_lebesgue_integral lborel {0..t}
      (\<lambda>s. trace (?acov s \<omega>)) = 0"
    for t :: real and \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real"
  proof -
    have "(\<lambda>s. trace (?acov s \<omega>))
        = (\<lambda>s. if s = 0 then real CARD('m) else 0)"
      using tr by (intro ext) simp
    then show ?thesis
      using set_integral_at_origin(2)[of t "real CARD('m)"] by simp
  qed
  have psd1: "psd (mat 1 :: real^'m^'m)"
    by (simp add: psd_def)
  have elb: "eigen_lb (mat 1 :: real^'m^'m) (CARD('m) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'m) set)" by simp
    show "CARD('m) - k \<le> dim (UNIV :: (real^'m) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'m) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  have eub: "eigen_ub (mat 1 :: real^'m^'m) L"
  proof -
    have "x \<bullet> x \<le> L * (x \<bullet> x)" for x :: "real^'m"
      using mult_right_mono[OF L inner_ge_zero] by simp
    then show ?thesis
      by (simp add: eigen_ub_def)
  qed
  have svm: "sufficiently_volatile_market ?M ?F ?X ?acov k L K x0 ?tau"
  proof (intro sufficiently_volatile_market.intro
      sufficiently_volatile_market_axioms.intro)
    show "martingale ?M ?F 0 ?X" by (rule mgX)
    show "prob_space ?M" by simp
    show "1 \<le> k" "k < CARD('m)" "1 \<le> L" by fact+
    show "AE \<omega> in ?M. ?X 0 \<omega> = x0" by simp
    show "AE \<omega> in ?M. 0 \<le> ?tau \<omega>" by simp
    show "?tau \<in> borel_measurable ?M" by simp
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow> ?X s \<omega> \<in> K"
      using x0K by (intro AE_I2) auto
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow> psd (?acov s \<omega>)"
      using psd1 by (intro AE_I2) auto
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
        eigen_lb (?acov s \<omega>) (CARD('m) - k)"
      using elb by (intro AE_I2) auto
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
        eigen_ub (?acov s \<omega>) L"
      using eub by (intro AE_I2) auto
    show "AE \<omega> in ?M. (\<lambda>s. ?acov s \<omega>) \<in> borel_measurable lborel"
      by (intro AE_I2 measurable_If) auto
    show "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (?acov s \<omega>))"
    proof (intro AE_I2 allI impI)
      fix \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real" and t :: real
      have "(\<lambda>s. trace (?acov s \<omega>))
          = (\<lambda>s. if s = 0 then real CARD('m) else 0)"
        using tr by (intro ext) simp
      then show "set_integrable lborel {0..t} (\<lambda>s. trace (?acov s \<omega>))"
        using set_integral_at_origin(1)[of t "real CARD('m)"] by simp
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
        (\<lambda>\<omega>. ?X (min t (?tau \<omega>)) \<omega> \<bullet> ?X (min t (?tau \<omega>)) \<omega>)"
      by (intro BMP.integrable_const)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (?tau \<omega>)}
          (\<lambda>s. trace (?acov s \<omega>)))"
      by (intro BMP.integrable_const)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. ?X (min t (?tau \<omega>)) \<omega> \<bullet> ?X (min t (?tau \<omega>)) \<omega> \<partial>?M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (?tau \<omega>)}
                   (\<lambda>s. trace (?acov s \<omega>)) \<partial>?M)
        = x0 \<bullet> x0"
    proof -
      fix t :: real assume "0 \<le> t"
      show "(\<integral>\<omega>. ?X (min t (?tau \<omega>)) \<omega>
            \<bullet> ?X (min t (?tau \<omega>)) \<omega> \<partial>?M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (?tau \<omega>)}
                   (\<lambda>s. trace (?acov s \<omega>)) \<partial>?M)
          = x0 \<bullet> x0"
        by (simp add: comp0 BMP.prob_space)
    qed
    show "martingale ?M ?F 0 (coord_Z ?X ?acov i)" for i
    proof -
      have cz: "coord_Z ?X ?acov i = (\<lambda>t \<omega>. (x0 $ i)\<^sup>2)"
      proof (intro ext)
        fix t :: real and \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real"
        have "(\<lambda>s. ?acov s \<omega> $ i $ i)
            = (\<lambda>s. if s = 0 then 1 else 0)"
          using entry by (intro ext) simp
        then have "set_lebesgue_integral lborel {0..t}
            (\<lambda>s. ?acov s \<omega> $ i $ i) = 0"
          using set_integral_at_origin(2)[of t 1] by simp
        then show "coord_Z ?X ?acov i t \<omega> = (x0 $ i)\<^sup>2"
          unfolding coord_Z_def by simp
      qed
      show ?thesis
        unfolding cz
        by (intro SFF.martingale_const_fun BMP.integrable_const
            borel_measurable_const)
    qed
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space ?M. ?tau \<omega> \<le> s} \<in> sets (?F s)"
    proof -
      fix s :: real assume s: "0 \<le> s"
      have "{\<omega> \<in> space ?M. ?tau \<omega> \<le> s} = space ?M"
        using s by blast
      then show "{\<omega> \<in> space ?M. ?tau \<omega> \<le> s} \<in> sets (?F s)"
        using sets.top[of ?M] by metis
    qed
    show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. ?X s \<omega>)"
      by (intro continuous_on_const)
  qed
  have W: "mkt_law_witness k L K x0 T (path_law ?M ?X T) ?M ?F ?X ?acov ?tau"
    unfolding mkt_law_witness_def
  proof (intro conjI)
    show "path_law ?M ?X T = path_law ?M ?X T" by (rule refl)
    show "sufficiently_volatile_market ?M ?F ?X ?acov k L K x0 ?tau"
      by (rule svm)
    show "\<forall>s \<omega>. \<omega> \<in> space ?M \<longrightarrow> ?X s \<omega> = ?X (min s (?tau \<omega>)) \<omega>"
      by simp
    show "\<forall>s \<omega>. \<omega> \<in> space ?M \<longrightarrow> ?tau \<omega> < s \<longrightarrow> ?acov s \<omega> = 0"
      by auto
    show "AE \<omega> in ?M. \<forall>l t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. ?acov s \<omega> $ l $ l)"
    proof (intro AE_I2 allI impI)
      fix \<omega> :: "'m \<Rightarrow> real \<Rightarrow> real" and l :: 'm and t :: real
      have "(\<lambda>s. ?acov s \<omega> $ l $ l) = (\<lambda>s. if s = 0 then 1 else 0)"
        using entry by (intro ext) simp
      then show "set_integrable lborel {0..t} (\<lambda>s. ?acov s \<omega> $ l $ l)"
        using set_integral_at_origin(1)[of t 1] by simp
    qed
  qed
  then show ?thesis
    unfolding mkt_path_laws_def by blast
qed

subsection \<open>N2: witness values are dominated by the law supremum\<close>

text \<open>The pushforward half of Larsson--Ruf Prop.\ 2.2, in market form: a
  witness market for \<open>(K, x0)\<close> shifted by \<open>-x0\<close> is a witness market for
  \<open>(K - x0, 0)\<close>; enlarging the domain moves it into the FIXED family over
  \<open>cball 0 (2r)\<close>; and its value \<open>ess_inf_time M tau\<close> is dominated by the
  \<open>vshift\<close> of its shifted path law at \<open>x0\<close>, because the path avoids the
  open target \<open>A\<close> (disjoint from \<open>K\<close>) up to \<open>tau\<close>.  Together: every
  witness value for \<open>(K, x0)\<close> is at most the law-level supremum over
  \<open>mkt_law_closure k L (cball 0 (2r)) 0 T\<close>.\<close>

lemma mkt_law_witness_mono_K:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and KK: "K \<subseteq> K'"
  shows "mkt_law_witness k L K' x0 T Q M F X acov tau"
  using W sufficiently_volatile_market_mono_K[OF _ KK]
  unfolding mkt_law_witness_def by blast

lemma inner_diff_self_expand:
  fixes a c :: "real^'m::finite"
  shows "(a - c) \<bullet> (a - c) = a \<bullet> a - 2 * (c \<bullet> a) + c \<bullet> c"
  by (simp add: inner_diff_left inner_diff_right inner_commute)

lemma mkt_law_witness_shift:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and c :: "real^'m" and r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r"
  shows "mkt_law_witness k L ((\<lambda>y. y - c) ` K) (x0 - c) T
      (path_law M (\<lambda>s \<omega>. X s \<omega> - c) T) M F (\<lambda>s \<omega>. X s \<omega> - c) acov tau"
proof -
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    and stp: "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>"
    and astop: "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> tau \<omega> < s \<longrightarrow> acov s \<omega> = 0"
    and aint: "AE \<omega> in M. \<forall>l t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. acov s \<omega> $ l $ l)"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have stp': "X (min t (tau \<omega>)) \<omega> = X t \<omega>"
    if "\<omega> \<in> space M" for t \<omega>
    using stp that by metis
  have fin: "finite_measure M"
    by (rule prob_space.finite_measure[OF sv.prob_space_M])
  have prj: "(\<lambda>x :: real^'m. x $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have bndX: "AE \<omega> in M. norm (X t \<omega>) \<le> r" if t: "0 \<le> t" for t
    using sv.X_in_K sv.tau_nonneg AE_space
  proof eventually_elim
    case (elim \<omega>)
    have m0: "0 \<le> min t (tau \<omega>)" using t elim by simp
    have "X t \<omega> = X (min t (tau \<omega>)) \<omega>"
      using stp elim by blast
    also have "\<dots> \<in> K"
      using elim m0 by auto
    finally have "X t \<omega> \<in> K" .
    then show ?case using Kball by (auto simp: dist_norm)
  qed
  have measX: "X t \<in> borel_measurable M" if "0 \<le> t" for t
    by (rule sv.random_variable[OF that])
  have mgc: "martingale M F 0 (\<lambda>_ \<omega>. c)"
    by (intro sv.martingale_const_fun finite_measure.integrable_const fin
        borel_measurable_const)
  have mgX': "martingale M F 0 (\<lambda>s \<omega>. X s \<omega> - c)"
    using martingale.diff[OF sv.martingale_axioms mgc] by simp
  have intXi: "integrable M (\<lambda>\<omega>. X t \<omega> $ i)" if t: "0 \<le> t" for t i
  proof (rule finite_measure.integrable_const_bound[OF fin, of _ r])
    show "(\<lambda>\<omega>. X t \<omega> $ i) \<in> borel_measurable M"
      by (intro measurable_compose[OF measX[OF t] prj])
    show "AE \<omega> in M. norm (X t \<omega> $ i) \<le> r"
      using bndX[OF t]
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>X t \<omega> $ i\<bar> \<le> norm (X t \<omega>)"
        by (rule component_le_norm_cart)
      then show ?case using elim by simp
    qed
  qed
  have EXi: "(\<integral>\<omega>. X t \<omega> $ i \<partial>M) = x0 $ i" if t: "0 \<le> t" for t i
  proof -
    have mXi: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ i)"
      by (rule martingale_vec_component[OF sv.martingale_axioms])
    have e0t: "(\<integral>\<omega>. X 0 \<omega> $ i \<partial>M) = (\<integral>\<omega>. X t \<omega> $ i \<partial>M)"
      by (rule martingale_expectation_eq[OF mXi]) (simp_all add: t)
    have aeX0: "AE \<omega> in M. X 0 \<omega> $ i = x0 $ i"
      using sv.X_start by eventually_elim simp
    have m0: "(\<lambda>\<omega>. X 0 \<omega> $ i) \<in> borel_measurable M"
      by (intro measurable_compose[OF measX prj]) simp
    have "(\<integral>\<omega>. X 0 \<omega> $ i \<partial>M) = (\<integral>\<omega>. x0 $ i \<partial>M)"
      using aeX0 by (intro integral_cong_AE m0 borel_measurable_const)
    also have "\<dots> = x0 $ i"
      using prob_space.prob_space[OF sv.prob_space_M] by simp
    finally show ?thesis using e0t by simp
  qed
  have EcX: "(\<integral>\<omega>. c \<bullet> X t \<omega> \<partial>M) = c \<bullet> x0" if t: "0 \<le> t" for t
  proof -
    have pw: "c \<bullet> X t \<omega> = (\<Sum>i\<in>UNIV. c $ i * (X t \<omega> $ i))" for \<omega>
      by (simp add: inner_vec_def)
    have "(\<integral>\<omega>. c \<bullet> X t \<omega> \<partial>M)
        = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. c $ i * (X t \<omega> $ i) \<partial>M))"
      unfolding pw
      by (intro Bochner_Integration.integral_sum integrable_mult_right
          intXi[OF t])
    also have "\<dots> = (\<Sum>i\<in>UNIV. c $ i * x0 $ i)"
      using EXi[OF t] by simp
    also have "\<dots> = c \<bullet> x0"
      by (simp add: inner_vec_def)
    finally show ?thesis .
  qed
  have measXX: "(\<lambda>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c)) \<in> borel_measurable M"
    if "0 \<le> t" for t
    by (intro borel_measurable_inner borel_measurable_diff
        borel_measurable_const measX that)
  have intXX: "integrable M (\<lambda>\<omega>. X t \<omega> \<bullet> X t \<omega>)" if t: "0 \<le> t" for t
  proof (rule finite_measure.integrable_const_bound[OF fin, of _ "r\<^sup>2"])
    show "(\<lambda>\<omega>. X t \<omega> \<bullet> X t \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_inner measX t)
    show "AE \<omega> in M. norm (X t \<omega> \<bullet> X t \<omega>) \<le> r\<^sup>2"
      using bndX[OF t]
    proof eventually_elim
      case (elim \<omega>)
      have "X t \<omega> \<bullet> X t \<omega> = (norm (X t \<omega>))\<^sup>2"
        by (simp add: power2_norm_eq_inner)
      also have "\<dots> \<le> r\<^sup>2"
        using elim by (intro power_mono) auto
      finally show ?case
        by (simp add: power2_norm_eq_inner)
    qed
  qed
  have intcX: "integrable M (\<lambda>\<omega>. c \<bullet> X t \<omega>)" if t: "0 \<le> t" for t
  proof (rule finite_measure.integrable_const_bound[OF fin,
        of _ "norm c * r"])
    show "(\<lambda>\<omega>. c \<bullet> X t \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_inner borel_measurable_const measX t)
    show "AE \<omega> in M. norm (c \<bullet> X t \<omega>) \<le> norm c * r"
      using bndX[OF t]
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>c \<bullet> X t \<omega>\<bar> \<le> norm c * norm (X t \<omega>)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm c * r"
        using elim by (intro mult_left_mono) auto
      finally show ?case by simp
    qed
  qed
  have EXXc: "(\<integral>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c) \<partial>M)
      = (\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> \<partial>M) - 2 * (c \<bullet> x0) + c \<bullet> c"
    if t: "0 \<le> t" for t
  proof -
    have pw: "(X t \<omega> - c) \<bullet> (X t \<omega> - c)
        = X t \<omega> \<bullet> X t \<omega> - 2 * (c \<bullet> X t \<omega>) + c \<bullet> c" for \<omega>
      by (rule inner_diff_self_expand)
    have int2: "integrable M (\<lambda>\<omega>. 2 * (c \<bullet> X t \<omega>))"
      by (intro integrable_mult_right intcX t)
    have "(\<integral>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c) \<partial>M)
        = (\<integral>\<omega>. (X t \<omega> \<bullet> X t \<omega> - 2 * (c \<bullet> X t \<omega>)) + c \<bullet> c \<partial>M)"
      unfolding pw by simp
    also have "\<dots> = (\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> - 2 * (c \<bullet> X t \<omega>) \<partial>M)
        + (\<integral>\<omega>. c \<bullet> c \<partial>M)"
      by (intro Bochner_Integration.integral_add
          Bochner_Integration.integrable_diff intXX[OF t] int2
          finite_measure.integrable_const fin)
    also have "(\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> - 2 * (c \<bullet> X t \<omega>) \<partial>M)
        = (\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> \<partial>M) - (\<integral>\<omega>. 2 * (c \<bullet> X t \<omega>) \<partial>M)"
      by (intro Bochner_Integration.integral_diff intXX[OF t] int2)
    also have "(\<integral>\<omega>. 2 * (c \<bullet> X t \<omega>) \<partial>M)
        = 2 * (\<integral>\<omega>. c \<bullet> X t \<omega> \<partial>M)"
      by (rule Bochner_Integration.integral_mult_right)
        (use intcX[OF t] in simp)
    also have "(\<integral>\<omega>. c \<bullet> X t \<omega> \<partial>M) = c \<bullet> x0"
      by (rule EcX[OF t])
    also have "(\<integral>\<omega>. c \<bullet> c \<partial>M) = c \<bullet> c"
      using prob_space.prob_space[OF sv.prob_space_M] by simp
    finally show ?thesis by simp
  qed
  have dyn0: "(\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> \<partial>M)
      - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
          (\<lambda>s. trace (acov s \<omega>)) \<partial>M) = x0 \<bullet> x0"
    if t: "0 \<le> t" for t
  proof -
    have e: "(\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
        = (\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl) (simp add: stp')
    show ?thesis
      using sv.dynkin_quadratic[OF t] e by simp
  qed
  have svm': "sufficiently_volatile_market M F (\<lambda>s \<omega>. X s \<omega> - c) acov
      k L ((\<lambda>y. y - c) ` K) (x0 - c) tau"
  proof (intro sufficiently_volatile_market.intro
      sufficiently_volatile_market_axioms.intro)
    show "martingale M F 0 (\<lambda>s \<omega>. X s \<omega> - c)" by (rule mgX')
    show "prob_space M" by (rule sv.prob_space_M)
    show "1 \<le> k" by (rule sv.k_lb)
    show "k < CARD('m)" by (rule sv.k_ub)
    show "1 \<le> L" by (rule sv.L_ge)
    show "AE \<omega> in M. X 0 \<omega> - c = x0 - c"
      using sv.X_start by eventually_elim simp
    show "AE \<omega> in M. 0 \<le> tau \<omega>" by (rule sv.tau_nonneg)
    show "tau \<in> borel_measurable M" by (rule sv.tau_meas)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        X s \<omega> - c \<in> (\<lambda>y. y - c) ` K"
      using sv.X_in_K by eventually_elim blast
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
      by (rule sv.acov_psd)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        eigen_lb (acov s \<omega>) (CARD('m) - k)"
      by (rule sv.acov_eigen_lb)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        eigen_ub (acov s \<omega>) L"
      by (rule sv.acov_eigen_ub)
    show "AE \<omega> in M. (\<lambda>s. acov s \<omega>) \<in> borel_measurable lborel"
      by (rule sv.acov_time_measurable)
    show "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule sv.acov_trace_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. (X (min t (tau \<omega>)) \<omega> - c) \<bullet> (X (min t (tau \<omega>)) \<omega> - c))"
    proof -
      fix t :: real assume t: "0 \<le> t"
      have "integrable M (\<lambda>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c))"
      proof (rule finite_measure.integrable_const_bound[OF fin,
            of _ "(r + norm c)\<^sup>2"])
        show "(\<lambda>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c)) \<in> borel_measurable M"
          by (rule measXX[OF t])
        show "AE \<omega> in M. norm ((X t \<omega> - c) \<bullet> (X t \<omega> - c)) \<le> (r + norm c)\<^sup>2"
          using bndX[OF t]
        proof eventually_elim
          case (elim \<omega>)
          have n1: "norm (X t \<omega> - c) \<le> r + norm c"
            using norm_triangle_ineq4[of "X t \<omega>" c] elim by simp
          have "(X t \<omega> - c) \<bullet> (X t \<omega> - c) = (norm (X t \<omega> - c))\<^sup>2"
            by (simp add: power2_norm_eq_inner)
          also have "\<dots> \<le> (r + norm c)\<^sup>2"
            using n1 by (intro power_mono) auto
          finally show ?case
            by (simp add: power2_norm_eq_inner)
        qed
      qed
      then show "integrable M
          (\<lambda>\<omega>. (X (min t (tau \<omega>)) \<omega> - c) \<bullet> (X (min t (tau \<omega>)) \<omega> - c))"
        by (rule Bochner_Integration.integrable_cong[OF refl, THEN iffD1,
            rotated]) (simp add: stp')
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
          (\<lambda>s. trace (acov s \<omega>)))"
      by (rule sv.compensator_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. (X (min t (tau \<omega>)) \<omega> - c) \<bullet> (X (min t (tau \<omega>)) \<omega> - c) \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
        = (x0 - c) \<bullet> (x0 - c)"
    proof -
      fix t :: real assume t: "0 \<le> t"
      have e1: "(\<integral>\<omega>. (X (min t (tau \<omega>)) \<omega> - c)
            \<bullet> (X (min t (tau \<omega>)) \<omega> - c) \<partial>M)
          = (\<integral>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c) \<partial>M)"
        by (intro Bochner_Integration.integral_cong refl) (simp add: stp')
      have "(\<integral>\<omega>. (X t \<omega> - c) \<bullet> (X t \<omega> - c) \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
          = ((\<integral>\<omega>. X t \<omega> \<bullet> X t \<omega> \<partial>M) - 2 * (c \<bullet> x0) + c \<bullet> c)
            - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                     (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
        using EXXc[OF t] by simp
      also have "\<dots> = x0 \<bullet> x0 - 2 * (c \<bullet> x0) + c \<bullet> c"
        using dyn0[OF t] by simp
      also have "\<dots> = (x0 - c) \<bullet> (x0 - c)"
        by (simp add: inner_diff_self_expand)
      finally show "(\<integral>\<omega>. (X (min t (tau \<omega>)) \<omega> - c)
            \<bullet> (X (min t (tau \<omega>)) \<omega> - c) \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
          = (x0 - c) \<bullet> (x0 - c)"
        using e1 by simp
    qed
    show "martingale M F 0 (coord_Z (\<lambda>s \<omega>. X s \<omega> - c) acov i)" for i
    proof -
      have mXi: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ i)"
        by (rule martingale_vec_component[OF sv.martingale_axioms])
      have mB: "martingale M F 0 (\<lambda>t \<omega>. (2 * c $ i) *\<^sub>R (X t \<omega> $ i))"
        by (rule martingale.scaleR_const[OF mXi])
      have mAB: "martingale M F 0 (\<lambda>t \<omega>. coord_Z X acov i t \<omega>
          - (2 * c $ i) *\<^sub>R (X t \<omega> $ i))"
        by (rule martingale.diff[OF sv.coord_Z_martingale mB])
      have mCst: "martingale M F 0 (\<lambda>_ \<omega>. (c $ i)\<^sup>2)"
        by (intro sv.martingale_const_fun finite_measure.integrable_const
            fin borel_measurable_const)
      have mFinal: "martingale M F 0 (\<lambda>t \<omega>. (coord_Z X acov i t \<omega>
          - (2 * c $ i) *\<^sub>R (X t \<omega> $ i)) + (c $ i)\<^sup>2)"
        by (rule martingale.add[OF mAB mCst])
      have cz_eq: "coord_Z (\<lambda>s \<omega>. X s \<omega> - c) acov i
          = (\<lambda>t \<omega>. (coord_Z X acov i t \<omega>
              - (2 * c $ i) *\<^sub>R (X t \<omega> $ i)) + (c $ i)\<^sup>2)"
      proof (intro ext)
        fix t :: real and \<omega>
        have comp: "(X t \<omega> - c) $ i = X t \<omega> $ i - c $ i"
          by (simp add: vector_minus_component)
        show "coord_Z (\<lambda>s \<omega>. X s \<omega> - c) acov i t \<omega>
            = (coord_Z X acov i t \<omega>
                - (2 * c $ i) *\<^sub>R (X t \<omega> $ i)) + (c $ i)\<^sup>2"
          unfolding coord_Z_def comp
          by (simp add: power2_diff algebra_simps)
      qed
      show ?thesis
        unfolding cz_eq by (rule mFinal)
    qed
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
      by (rule sv.tau_stopping)
    show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega> - c)"
      by (intro continuous_on_diff continuous_on_const sv.X_paths_cont)
  qed
  show ?thesis
    unfolding mkt_law_witness_def
  proof (intro conjI)
    show "path_law M (\<lambda>s \<omega>. X s \<omega> - c) T
        = path_law M (\<lambda>s \<omega>. X s \<omega> - c) T" by (rule refl)
    show "sufficiently_volatile_market M F (\<lambda>s \<omega>. X s \<omega> - c) acov
        k L ((\<lambda>y. y - c) ` K) (x0 - c) tau" by (rule svm')
    show "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow>
        X s \<omega> - c = X (min s (tau \<omega>)) \<omega> - c"
    proof (intro allI impI)
      fix s :: real and \<omega> assume w: "\<omega> \<in> space M"
      have "X s \<omega> = X (min s (tau \<omega>)) \<omega>"
        using stp w by blast
      then show "X s \<omega> - c = X (min s (tau \<omega>)) \<omega> - c" by simp
    qed
    show "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> tau \<omega> < s \<longrightarrow> acov s \<omega> = 0"
      using astop by blast
    show "AE \<omega> in M. \<forall>l t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. acov s \<omega> $ l $ l)"
      by (rule aint)
  qed
qed

lemma witness_value_le_vshift:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and A :: "(real^'m) set" and T :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and A: "open A" and AK: "A \<inter> K = {}" and T0: "0 \<le> T"
    and vT: "ess_inf_time M tau \<le> ennreal T"
  shows "ess_inf_time M tau
      \<le> ennreal (vshift T A x0 (path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T))"
proof -
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have Xm: "(\<lambda>\<omega>. X t \<omega> - x0) \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that
    by (intro borel_measurable_diff borel_measurable_const
        sv.random_variable) simp
  have cont: "continuous_on {0..T} (\<lambda>t. X t \<omega> - x0)"
    if "\<omega> \<in> space M" for \<omega>
    by (intro continuous_on_diff continuous_on_const
        continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
  have vpl: "vshift T A x0 (path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T)
      = enn2real (ess_inf_time M
          (etime T A (\<lambda>s \<omega>'. x0 + (X s \<omega>' - x0))))"
    by (rule vshift_path_law[OF T0 A Xm cont])
  have peq: "(\<lambda>s \<omega>'. x0 + (X s \<omega>' - x0)) = X"
    by (intro ext) simp
  have core: "ess_inf_time M tau \<le> ess_inf_time M (etime T A X)"
  proof (subst ess_inf_time_ge_iff)
    show "AE \<omega> in M. ess_inf_time M tau \<le> ennreal (etime T A X \<omega>)"
      using sv.X_in_K sv.tau_nonneg
        ess_inf_time_ge_iff[of "ess_inf_time M tau" M tau, THEN iffD1,
          OF order.refl]
    proof eventually_elim
      case (elim \<omega>)
      have et_ge: "min T (tau \<omega>) \<le> etime T A X \<omega>"
      proof (rule ccontr)
        assume "\<not> min T (tau \<omega>) \<le> etime T A X \<omega>"
        then have "etime T A X \<omega> < min T (tau \<omega>)" by linarith
        then have "(\<exists>u. 0 \<le> u \<and> u \<le> T \<and> X u \<omega> \<in> A
            \<and> u < min T (tau \<omega>)) \<or> T < min T (tau \<omega>)"
          using etime_less_iff[OF T0, of A X \<omega> "min T (tau \<omega>)"] by blast
        moreover have "\<not> T < min T (tau \<omega>)" by simp
        ultimately obtain u where u: "0 \<le> u" "u \<le> T" "X u \<omega> \<in> A"
          "u < min T (tau \<omega>)" by blast
        have "X u \<omega> \<in> K"
          using elim u by auto
        then show False using u AK by blast
      qed
      have "ess_inf_time M tau \<le> ennreal (min T (tau \<omega>))"
      proof (cases "T \<le> tau \<omega>")
        case True
        then show ?thesis using vT by (simp add: min_absorb1)
      next
        case False
        then show ?thesis using elim by (simp add: min_absorb2)
      qed
      also have "\<dots> \<le> ennreal (etime T A X \<omega>)"
        using et_ge by (intro ennreal_leI)
      finally show ?case .
    qed
  qed
  have fin_et: "ess_inf_time M (etime T A X) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF sv.prob_space_M etime_le_T[OF T0]])
  have "ennreal (enn2real (ess_inf_time M (etime T A X)))
      = ess_inf_time M (etime T A X)"
    using fin_et by (intro ennreal_enn2real) (simp add: le_less_trans)
  then show ?thesis
    unfolding vpl peq using core by simp
qed

theorem witness_value_le_law_sup:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and A :: "(real^'m) set" and T r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r" and x0K: "x0 \<in> K"
    and A: "open A" and AK: "A \<inter> K = {}" and T0: "0 \<le> T"
    and vT: "ess_inf_time M tau \<le> ennreal T"
  shows "ess_inf_time M tau
      \<le> ennreal (Sup (vshift T A x0
          ` mkt_law_closure k L (cball 0 (2 * r)) 0 T))"
proof -
  have W1: "mkt_law_witness k L ((\<lambda>y. y - x0) ` K) (x0 - x0) T
      (path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T) M F (\<lambda>s \<omega>. X s \<omega> - x0) acov tau"
    by (rule mkt_law_witness_shift[OF W Kball])
  have sub2r: "(\<lambda>y. y - x0) ` K \<subseteq> cball 0 (2 * r)"
  proof
    fix z assume "z \<in> (\<lambda>y. y - x0) ` K"
    then obtain y where y: "y \<in> K" and z: "z = y - x0" by blast
    have ny: "norm y \<le> r"
      using y Kball by (auto simp: dist_norm)
    have nx: "norm x0 \<le> r"
      using x0K Kball by (auto simp: dist_norm)
    have "norm (y - x0) \<le> norm y + norm x0"
      by (rule norm_triangle_ineq4)
    also have "\<dots> \<le> 2 * r"
      using ny nx by linarith
    finally show "z \<in> cball 0 (2 * r)"
      using z by (simp add: dist_norm norm_minus_commute)
  qed
  have W2: "mkt_law_witness k L (cball 0 (2 * r)) 0 T
      (path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T) M F (\<lambda>s \<omega>. X s \<omega> - x0) acov tau"
    using mkt_law_witness_mono_K[OF W1 sub2r] by simp
  have Qmem: "path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T
      \<in> mkt_path_laws k L (cball 0 (2 * r)) 0 T"
    using W2 unfolding mkt_path_laws_def by blast
  then have Qcl: "path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T
      \<in> mkt_law_closure k L (cball 0 (2 * r)) 0 T"
    using mkt_path_laws_subset_closure[OF T0] by blast
  have bdd: "bdd_above (vshift T A x0
      ` mkt_law_closure k L (cball 0 (2 * r)) 0 T)"
  proof (rule bdd_aboveI[of _ T])
    fix v assume "v \<in> vshift T A x0
        ` mkt_law_closure k L (cball 0 (2 * r)) 0 T"
    then obtain N where N: "N \<in> mkt_law_closure k L (cball 0 (2 * r)) 0 T"
      and v: "v = vshift T A x0 N" by blast
    show "v \<le> T"
      unfolding v
      by (rule vshift_le[OF T0 mkt_law_closure_prob[OF T0 N]])
  qed
  have "vshift T A x0 (path_law M (\<lambda>s \<omega>. X s \<omega> - x0) T)
      \<le> Sup (vshift T A x0 ` mkt_law_closure k L (cball 0 (2 * r)) 0 T)"
    by (intro cSup_upper imageI Qcl bdd)
  then show ?thesis
    using witness_value_le_vshift[OF W A AK T0 vT] ennreal_leI
    by (meson order.trans)
qed

subsection \<open>N3 opening: closure laws inherit start and confinement\<close>

text \<open>The first piece of "the closure adds no value": whatever a closure
  point turns out to be, it is supported on paths that start at \<open>x0\<close> and
  stay in \<open>K\<close>.  The set of such paths is CLOSED in the path topology (an
  arbitrary intersection of closed evaluation preimages, no rational
  reduction needed), members of \<open>mkt_path_laws\<close> carry full mass on it
  because their markets are stopped and confined, and the closed-set
  Portmanteau (\<open>weak_conv_closed_full_measure\<close>) pushes full mass to every
  weak limit.  Both the canonical-market route and a law-level restatement
  of clause (1) will consume these facts.\<close>

definition confined_paths ::
  "real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> (real \<Rightarrow> real^'m) set"
  where
  "confined_paths T K x0 =
     {f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
        f 0 = x0 \<and> (\<forall>t\<in>{0..T}. f t \<in> K)}"

lemma closedin_confined_paths:
  fixes K :: "(real^'m::finite) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      (confined_paths T K x0)"
proof -
  let ?X = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  interpret PM: Metric_space
      "mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
      "mdist (path_metric T :: (real \<Rightarrow> real^'m) metric)"
    by (rule Metric_space_mspace_mdist)
  have ts: "topspace ?X
      = mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
    unfolding mtopology_of_def by (rule PM.topspace_mtopology)
  have c0: "closedin ?X {f \<in> topspace ?X. f 0 \<in> {x0}}"
    by (rule closedin_continuous_map_preimage[OF continuous_map_path_eval])
      (use T in \<open>auto simp: closed_closedin[symmetric]\<close>)
  have ct: "closedin ?X {f \<in> topspace ?X. f t \<in> K}"
    if t: "t \<in> {0..T}" for t
    by (rule closedin_continuous_map_preimage[OF
          continuous_map_path_eval[OF t]])
      (simp add: closed_closedin[symmetric] K)
  have eq: "confined_paths T K x0
      = {f \<in> topspace ?X. f 0 \<in> {x0}}
        \<inter> (\<Inter>t\<in>{0..T}. {f \<in> topspace ?X. f t \<in> K})"
    using T unfolding confined_paths_def ts by auto
  show ?thesis
    unfolding eq
    by (intro closedin_Int c0 closedin_INT ct) (use T in auto)
qed

lemma mkt_path_laws_confined:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and Q: "Q \<in> mkt_path_laws k L K x0 T"
  shows "measure Q (confined_paths T K x0) = 1"
proof -
  from Q obtain M F X acov tau
    where W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  have QM: "Q = path_law M X T"
    and svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    and stp: "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have Xm: "X t \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that by (intro sv.random_variable) simp
  have cont: "continuous_on {0..T} (\<lambda>t. X t \<omega>)" if "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T}) \<in> M \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF T Xm cont])
  interpret PQ: prob_space Q
    by (rule mkt_path_laws_prob[OF T Q])
  have setB: "confined_paths T K x0 \<in> sets (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    by (rule borel_of_closed[OF closedin_confined_paths[OF T K]])
  then have setQ: "confined_paths T K x0 \<in> sets Q"
    using mkt_path_laws_sets[OF Q] by simp
  have ae: "AE \<omega> in M. restrict (\<lambda>t. X t \<omega>) {0..T}
      \<in> confined_paths T K x0"
    using sv.X_start sv.X_in_K sv.tau_nonneg AE_space
  proof eventually_elim
    case (elim \<omega>)
    have msp: "restrict (\<lambda>t. X t \<omega>) {0..T}
        \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
      using measurable_space[OF pm] elim
      by (simp add: space_borel_of mtopology_of_def
          Metric_space.topspace_mtopology[OF Metric_space_mspace_mdist])
    have v0: "restrict (\<lambda>t. X t \<omega>) {0..T} 0 = x0"
      using T elim by simp
    have vt: "restrict (\<lambda>t. X t \<omega>) {0..T} t \<in> K"
      if t: "t \<in> {0..T}" for t
    proof -
      have t0: "0 \<le> t" using t by simp
      have m0: "0 \<le> min t (tau \<omega>)" using t0 elim by simp
      have "X t \<omega> = X (min t (tau \<omega>)) \<omega>"
        using stp elim by blast
      also have "\<dots> \<in> K"
        using elim m0 by auto
      finally show ?thesis using t by simp
    qed
    show ?case
      unfolding confined_paths_def using msp v0 vt by blast
  qed
  have ceq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
      f \<in> confined_paths T K x0} = confined_paths T K x0"
    unfolding confined_paths_def by auto
  have "AE f in Q. f \<in> confined_paths T K x0"
    unfolding QM path_law_def
    by (subst AE_distr_iff[OF pm])
      (use setB ae ceq in \<open>auto simp: space_borel_of\<close>)
  then show ?thesis
    using PQ.AE_in_set_eq_1[OF setQ] by simp
qed

theorem mkt_law_closure_confined:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
  shows "measure \<Lambda> (confined_paths T K x0) = 1"
proof -
  obtain \<sigma> where r\<sigma>: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
    and lim: "limitin (weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric))) \<sigma> \<Lambda> sequentially"
    using closure_of_sequential_limit[OF metrizable_weak_conv_path_topology
        L[unfolded mkt_law_closure_def]] by blast
  show ?thesis
  proof (rule weak_conv_closed_full_measure[OF lim
      closedin_confined_paths[OF T K]])
    show "\<And>i. measure (\<sigma> i) (confined_paths T K x0) = 1"
      using r\<sigma> by (intro mkt_path_laws_confined[OF T K]) blast
    show "prob_space \<Lambda>"
      by (rule mkt_law_closure_prob[OF T L])
  qed
qed

corollary mkt_law_closure_confined_AE:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
  shows "AE f in \<Lambda>. f 0 = x0 \<and> (\<forall>t\<in>{0..T}. f t \<in> K)"
proof -
  interpret PL: prob_space \<Lambda>
    by (rule mkt_law_closure_prob[OF T L])
  have setL: "confined_paths T K x0 \<in> sets \<Lambda>"
    using borel_of_closed[OF closedin_confined_paths[OF T K]]
      mkt_law_closure_sets[OF L] by simp
  have "AE f in \<Lambda>. f \<in> confined_paths T K x0"
    using PL.AE_in_set_eq_1[OF setL]
      mkt_law_closure_confined[OF T K L] by simp
  then show ?thesis
    by eventually_elim (simp add: confined_paths_def)
qed

subsection \<open>The domination theorem, hypothesis-free\<close>

text \<open>The value-below-horizon hypothesis of \<open>witness_value_le_law_sup\<close> is
  discharged uniformly: every witness value is at most \<open>ball_v r k x0\<close>, by
  monotonicity into the ball and the exit-time bound of Lemma 2.1.\<close>

lemma witness_value_le_ball_v:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r"
  shows "ess_inf_time M tau \<le> ennreal (ball_v r k x0)"
proof -
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have svm': "sufficiently_volatile_market M F X acov k L (cball 0 r) x0 tau"
    by (rule sufficiently_volatile_market_mono_K[OF svm Kball])
  have "ess_inf_time M tau \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
    by (rule ess_inf_time_le_nn_integral[OF sv.prob_space_M])
  also have "\<dots> \<le> ennreal (ball_v r k x0)"
    by (rule sufficiently_volatile_market.expected_exit_time_bound[OF svm' refl])
  finally show ?thesis .
qed

theorem witness_value_le_law_sup_ball:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and A :: "(real^'m) set" and T r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r" and x0K: "x0 \<in> K"
    and A: "open A" and AK: "A \<inter> K = {}" and T0: "0 \<le> T"
    and bT: "ball_v r k x0 \<le> T"
  shows "ess_inf_time M tau
      \<le> ennreal (Sup (vshift T A x0
          ` mkt_law_closure k L (cball 0 (2 * r)) 0 T))"
proof (rule witness_value_le_law_sup[OF W Kball x0K A AK T0])
  show "ess_inf_time M tau \<le> ennreal T"
    using witness_value_le_ball_v[OF W Kball] ennreal_leI[OF bT]
    by (rule order_trans)
qed

subsection \<open>N3, integrated identities: the martingale property survives the limit\<close>

text \<open>Members of \<open>mkt_path_laws\<close> satisfy the INTEGRATED martingale identity
  \<open>E[(f t $ i - f s $ i) * g f] = 0\<close> against every bounded continuous test
  function of the path up to time \<open>s\<close> --- and so does every closure point.
  The increment factor is CLAMPED at \<open>2r\<close> so that the functional is bounded
  and continuous on the whole path space; on the members the clamp is
  invisible because their markets are stopped and confined.  The identity
  passes to the closure by the integral clause of weak convergence.  This
  is the first structural fact a canonical market carries out of a limit
  law.\<close>

definition rclamp :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rclamp c y = max (- c) (min c y)"

lemma rclamp_bound: "0 \<le> c \<Longrightarrow> \<bar>rclamp c y\<bar> \<le> c"
  by (simp add: rclamp_def abs_le_iff min_def max_def)

lemma rclamp_id:
  assumes "\<bar>y\<bar> \<le> c"
  shows "rclamp c y = y"
proof -
  have "min c y = y"
    using assms by (intro min_absorb2) (simp add: abs_le_iff)
  moreover have "max (- c) y = y"
    using assms by (intro max_absorb2) (simp add: abs_le_iff)
  ultimately show ?thesis by (simp add: rclamp_def)
qed

lemma rclamp_cont: "continuous_map euclideanreal euclideanreal (rclamp c)"
  unfolding continuous_map_iff_continuous2 rclamp_def
  by (intro continuous_intros)

lemma mkt_law_witness_bound:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r" and t: "0 \<le> t"
  shows "AE \<omega> in M. norm (X t \<omega>) \<le> r"
proof -
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    and stp: "\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  show ?thesis
    using sv.X_in_K sv.tau_nonneg AE_space
  proof eventually_elim
    case (elim \<omega>)
    have m0: "0 \<le> min t (tau \<omega>)" using t elim by simp
    have "X t \<omega> = X (min t (tau \<omega>)) \<omega>"
      using stp elim by blast
    also have "\<dots> \<in> K"
      using elim m0 by auto
    finally have "X t \<omega> \<in> K" .
    then show ?case using Kball by (auto simp: dist_norm)
  qed
qed

lemma martingale_bounded_test:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and Z :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F (0::real) Y"
    and st: "0 \<le> s" and ts: "s \<le> t"
    and Zm: "Z \<in> borel_measurable (F s)"
    and int_t: "integrable M (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)"
    and int_s: "integrable M (\<lambda>\<omega>. Z \<omega> * Y s \<omega>)"
  shows "(\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M) = (\<integral>\<omega>. Z \<omega> * Y s \<omega> \<partial>M)"
proof -
  interpret MY: martingale M F 0 Y by (rule mg)
  have t0: "0 \<le> t" using st ts by linarith
  interpret sfs: sigma_finite_subalgebra M "F s"
    by (rule MY.sigma_finite_subalgebra_F[OF st])
  have sp: "space M \<in> sets (F s)"
    using sets.top[of "F s"] MY.space_F[OF st] by simp
  have mp: "AE \<omega> in M. Y s \<omega> = cond_exp M (F s) (Y t) \<omega>"
    by (rule MY.martingale_property[OF st ts])
  have ZM: "Z \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st] Zm])
  have cM: "cond_exp M (F s) (Y t) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st]
        borel_measurable_cond_exp])
  have cPM: "cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st]
        borel_measurable_cond_exp])
  have m1: "(\<lambda>\<omega>. Z \<omega> * Y s \<omega>) \<in> borel_measurable M"
    by (rule borel_measurable_integrable[OF int_s])
  have m2: "(\<lambda>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_times ZM cM)
  have e1: "(\<integral>\<omega>. Z \<omega> * Y s \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega> \<partial>M)"
    using mp by (intro integral_cong_AE m1 m2) auto
  have mult: "AE \<omega> in M. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega>
      = Z \<omega> * cond_exp M (F s) (Y t) \<omega>"
    by (rule sfs.cond_exp_measurable_mult(2)[OF int_t MY.integrable[OF t0] Zm])
  have e2: "(\<integral>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega> \<partial>M)
      = (\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)"
    using mult by (intro integral_cong_AE m2 cPM) auto
  have e3: "(\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M)"
  proof -
    have s1: "set_lebesgue_integral M (space M)
        (cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>))
        = set_lebesgue_integral M (space M) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)"
      using sfs.cond_exp_set_integral[OF int_t sp] by simp
    have s2: "set_lebesgue_integral M (space M)
        (cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>))
        = (\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)"
      by (rule set_integral_space[OF integrable_cond_exp])
    have s3: "set_lebesgue_integral M (space M) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)
        = (\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M)"
      by (rule set_integral_space[OF int_t])
    show ?thesis using s1 s2 s3 by simp
  qed
  from e1 e2 e3 show ?thesis by simp
qed

lemma martingale_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real" and c :: real
  assumes st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i) * h (restrict f {0..s}))"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have part1': "continuous_map ?PT euclideanreal
      ((rclamp c \<circ> (\<lambda>v. v $ i)) \<circ> (\<lambda>f. f t - f s))"
    by (intro continuous_map_compose[OF evdiff]
        continuous_map_compose[OF cmp_i] rclamp_cont)
  have part1: "continuous_map ?PT euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i))"
    using part1' by (simp add: o_def vector_minus_component)
  have rc: "continuous_map ?PT
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))
      (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have part2': "continuous_map ?PT euclideanreal
      (h \<circ> (\<lambda>f. restrict f {0..s}))"
    by (rule continuous_map_compose[OF rc hc])
  have part2: "continuous_map ?PT euclideanreal
      (\<lambda>f. h (restrict f {0..s}))"
    using part2' by (simp add: o_def)
  show ?thesis
    by (rule continuous_map_real_mult[OF part1 part2])
qed

lemma mkt_path_laws_martingale_test:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real" and B r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and Q: "Q \<in> mkt_path_laws k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
    and hb: "\<And>f. \<bar>h f\<bar> \<le> B"
  shows "(\<integral>f. rclamp (2 * r) (f t $ i - f s $ i)
      * h (restrict f {0..s}) \<partial>Q) = 0"
proof -
  let ?G = "\<lambda>f :: real \<Rightarrow> real^'m.
      rclamp (2 * r) (f t $ i - f s $ i) * h (restrict f {0..s})"
  have B0: "0 \<le> B" using hb[of "\<lambda>_. 0"] by auto
  have t0: "0 \<le> t" and sT: "s \<le> T" using st ts tT by linarith+
  have sI: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using st ts tT by auto
  from Q obtain M F X acov tau
    where W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  have QM: "Q = path_law M X T"
    and svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have fin: "finite_measure M"
    by (rule prob_space.finite_measure[OF sv.prob_space_M])
  have prj: "(\<lambda>x :: real^'m. x $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have Xm: "X u \<in> borel_measurable M" if "u \<in> {0..T}" for u
    using that by (intro sv.random_variable) simp
  have cont: "continuous_on {0..T} (\<lambda>u. X u \<omega>)" if "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>u. X u \<omega>) {0..T}) \<in> M \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF T0 Xm cont])
  have Gcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?G"
    by (rule martingale_test_functional_cont[OF st sT tI hc])
  have Gmeas: "?G \<in> borel_measurable (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF Gcont]
    by (simp add: borel_of_euclidean)
  have rr: "restrict (restrict g {0..T}) {0..s} = restrict g {0..s}"
    for g :: "real \<Rightarrow> real^'m"
    using sT by (auto simp: restrict_def fun_eq_iff)
  define Z where "Z = (\<lambda>\<omega>. h (restrict (\<lambda>u. X u \<omega>) {0..s}))"
  have Xm_Fs: "X u \<in> borel_measurable (F s)" if "u \<in> {0..s}" for u
    using that by (intro sv.adaptedD) auto
  have cont_Fs: "continuous_on {0..s} (\<lambda>u. X u \<omega>)"
    if "\<omega> \<in> space (F s)" for \<omega>
  proof -
    have "\<omega> \<in> space M" using that sv.space_F[OF st] by simp
    then show ?thesis
      by (intro continuous_on_subset[OF sv.X_paths_cont]) auto
  qed
  have pms: "(\<lambda>\<omega>. restrict (\<lambda>u. X u \<omega>) {0..s}) \<in> (F s) \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF st Xm_Fs cont_Fs])
  have hmeas: "h \<in> borel_measurable (borel_of
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF hc]
    by (simp add: borel_of_euclidean)
  have ZFs: "Z \<in> borel_measurable (F s)"
    unfolding Z_def
    using measurable_comp[OF pms hmeas] by (simp add: o_def)
  have ZM: "Z \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF sv.subalgebras[OF st] ZFs])
  have XiM: "(\<lambda>\<omega>. X u \<omega> $ i) \<in> borel_measurable M" if "u \<in> {0..T}" for u
    by (intro measurable_compose[OF Xm[OF that] prj])
  have step1: "(\<integral>f. ?G f \<partial>Q)
      = (\<integral>\<omega>. ?G (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)"
    unfolding QM path_law_def
    by (rule Bochner_Integration.integral_distr[OF pm Gmeas])
  have step2: "(\<integral>\<omega>. ?G (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)
      = (\<integral>\<omega>. rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i) * Z \<omega> \<partial>M)"
    unfolding Z_def
    by (intro Bochner_Integration.integral_cong refl)
      (use st ts tT sT in \<open>simp add: rr\<close>)
  have bnd_t: "AE \<omega> in M. norm (X t \<omega>) \<le> r"
    by (rule mkt_law_witness_bound[OF W Kball t0])
  have bnd_s: "AE \<omega> in M. norm (X s \<omega>) \<le> r"
    by (rule mkt_law_witness_bound[OF W Kball st])
  have ae_inc: "AE \<omega> in M. \<bar>X t \<omega> $ i - X s \<omega> $ i\<bar> \<le> 2 * r"
    using bnd_t bnd_s
  proof eventually_elim
    case (elim \<omega>)
    have "\<bar>X t \<omega> $ i - X s \<omega> $ i\<bar>
        \<le> \<bar>X t \<omega> $ i\<bar> + \<bar>X s \<omega> $ i\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> norm (X t \<omega>) + norm (X s \<omega>)"
      by (intro add_mono component_le_norm_cart)
    also have "\<dots> \<le> 2 * r" using elim by linarith
    finally show ?case .
  qed
  have mcl: "(\<lambda>\<omega>. rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i) * Z \<omega>)
      \<in> borel_measurable M"
  proof (intro borel_measurable_times ZM)
    have "continuous_on UNIV (rclamp (2 * r))"
      using rclamp_cont[of "2 * r"]
      by (simp add: continuous_map_iff_continuous2)
    then have "rclamp (2 * r) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
    then show "(\<lambda>\<omega>. rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i))
        \<in> borel_measurable M"
      by (intro measurable_compose[OF _ \<open>rclamp (2 * r)
          \<in> borel_measurable borel\<close>] borel_measurable_diff
          XiM[OF tI] XiM[OF sI])
  qed
  have mun: "(\<lambda>\<omega>. Z \<omega> * X t \<omega> $ i - Z \<omega> * X s \<omega> $ i)
      \<in> borel_measurable M"
    by (intro borel_measurable_diff borel_measurable_times ZM
        XiM[OF tI] XiM[OF sI])
  have step3: "(\<integral>\<omega>. rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i) * Z \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * X t \<omega> $ i - Z \<omega> * X s \<omega> $ i \<partial>M)"
  proof (rule integral_cong_AE[OF mcl mun])
    show "AE \<omega> in M. rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i) * Z \<omega>
        = Z \<omega> * X t \<omega> $ i - Z \<omega> * X s \<omega> $ i"
      using ae_inc
    proof eventually_elim
      case (elim \<omega>)
      show ?case
        unfolding rclamp_id[OF elim]
        by (simp add: algebra_simps)
    qed
  qed
  have intZ: "integrable M (\<lambda>\<omega>. Z \<omega> * X u \<omega> $ i)" if u: "u \<in> {0..T}" for u
  proof (rule finite_measure.integrable_const_bound[OF fin, of _ "B * r"])
    show "(\<lambda>\<omega>. Z \<omega> * X u \<omega> $ i) \<in> borel_measurable M"
      by (intro borel_measurable_times ZM XiM[OF u])
    have u0: "0 \<le> u" using u by simp
    show "AE \<omega> in M. norm (Z \<omega> * X u \<omega> $ i) \<le> B * r"
      using mkt_law_witness_bound[OF W Kball u0]
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>Z \<omega> * X u \<omega> $ i\<bar> = \<bar>Z \<omega>\<bar> * \<bar>X u \<omega> $ i\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> B * r"
      proof (intro mult_mono)
        show "\<bar>Z \<omega>\<bar> \<le> B" unfolding Z_def by (rule hb)
        show "\<bar>X u \<omega> $ i\<bar> \<le> r"
          using component_le_norm_cart[of "X u \<omega>" i] elim by linarith
      qed (use B0 in auto)
      finally show ?case by simp
    qed
  qed
  have step4: "(\<integral>\<omega>. Z \<omega> * X t \<omega> $ i - Z \<omega> * X s \<omega> $ i \<partial>M) = 0"
  proof -
    have "(\<integral>\<omega>. Z \<omega> * X t \<omega> $ i - Z \<omega> * X s \<omega> $ i \<partial>M)
        = (\<integral>\<omega>. Z \<omega> * X t \<omega> $ i \<partial>M) - (\<integral>\<omega>. Z \<omega> * X s \<omega> $ i \<partial>M)"
      by (rule Bochner_Integration.integral_diff[OF intZ[OF tI] intZ[OF sI]])
    also have "\<dots> = 0"
      using martingale_bounded_test[OF martingale_vec_component[OF
          sv.martingale_axioms] st ts ZFs intZ[OF tI] intZ[OF sI]]
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    using step1 step2 step3 step4 by simp
qed

theorem mkt_law_closure_martingale_test:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure"
    and h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real" and B r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
    and hb: "\<And>f. \<bar>h f\<bar> \<le> B"
  shows "(\<integral>f. rclamp (2 * r) (f t $ i - f s $ i)
      * h (restrict f {0..s}) \<partial>\<Lambda>) = 0"
proof -
  let ?G = "\<lambda>f :: real \<Rightarrow> real^'m.
      rclamp (2 * r) (f t $ i - f s $ i) * h (restrict f {0..s})"
  have B0: "0 \<le> B" using hb[of "\<lambda>_. 0"] by auto
  have sT: "s \<le> T" using ts tT by linarith
  have tI: "t \<in> {0..T}" using st ts tT by auto
  obtain \<sigma> where r\<sigma>: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
    and lim: "limitin (weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric))) \<sigma> \<Lambda> sequentially"
    using closure_of_sequential_limit[OF metrizable_weak_conv_path_topology
        L[unfolded mkt_law_closure_def]] by blast
  have z: "(\<integral>f. ?G f \<partial>(\<sigma> j)) = 0" for j
    using r\<sigma>
    by (intro mkt_path_laws_martingale_test[OF T0 Kball r0 _ st ts tT hc hb])
      blast
  have Gcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?G"
    by (rule martingale_test_functional_cont[OF st sT tI hc])
  have Gbd: "\<exists>B'. \<forall>f\<in>topspace (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m) metric)). \<bar>?G f\<bar> \<le> B'"
  proof (intro exI[of _ "2 * r * B"] ballI)
    fix f :: "real \<Rightarrow> real^'m"
    have "\<bar>?G f\<bar> = \<bar>rclamp (2 * r) (f t $ i - f s $ i)\<bar>
        * \<bar>h (restrict f {0..s})\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> 2 * r * B"
      by (intro mult_mono rclamp_bound hb) (use r0 B0 in auto)
    finally show "\<bar>?G f\<bar> \<le> 2 * r * B" .
  qed
  have blim: "(\<lambda>j. \<integral>f. ?G f \<partial>(\<sigma> j)) \<longlonglongrightarrow> (\<integral>f. ?G f \<partial>\<Lambda>)"
    using lim Gcont Gbd unfolding weak_conv_on_def by blast
  have c0: "(\<lambda>j. \<integral>f. ?G f \<partial>(\<sigma> j)) = (\<lambda>_. 0 :: real)"
    using z by (intro ext) simp
  have blim': "(\<lambda>_. 0 :: real) \<longlonglongrightarrow> (\<integral>f. ?G f \<partial>\<Lambda>)"
    using blim unfolding c0 .
  show ?thesis
    using LIMSEQ_unique[OF blim' tendsto_const] by simp
qed

subsection \<open>N3, integrated identities: the covariation upper bound\<close>

text \<open>The covariation analogue: against a NONNEGATIVE bounded continuous
  past-measurable test functional, the expected squared coordinate increment
  is at most \<open>L * (t - s)\<close> times the expected test value.  On a witness
  market this is the compensator identity for \<open>coord_Z\<close> together with the
  pointwise bounds \<open>0 \<le> acov $ i $ i \<le> L\<close> (psd and the eigenvalue upper
  bound before the horizon, \<open>acov = 0\<close> after); the clamped form passes to
  closure points by weak convergence exactly as the martingale identity
  did.\<close>

lemma witness_compensator_increment_bounds:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and st: "0 \<le> s" and ts: "s \<le> t"
  shows "AE \<omega> in M.
      0 \<le> set_lebesgue_integral lborel {0..t} (\<lambda>u. acov u \<omega> $ i $ i)
           - set_lebesgue_integral lborel {0..s} (\<lambda>u. acov u \<omega> $ i $ i)
      \<and> set_lebesgue_integral lborel {0..t} (\<lambda>u. acov u \<omega> $ i $ i)
           - set_lebesgue_integral lborel {0..s} (\<lambda>u. acov u \<omega> $ i $ i)
        \<le> L * (t - s)"
proof -
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    and astop: "\<forall>u \<omega>. \<omega> \<in> space M \<longrightarrow> tau \<omega> < u \<longrightarrow> acov u \<omega> = 0"
    and aint: "AE \<omega> in M. \<forall>l u. 0 \<le> u \<longrightarrow>
        set_integrable lborel {0..u} (\<lambda>v. acov v \<omega> $ l $ l)"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L0: "0 \<le> L" using sv.L_ge by simp
  show ?thesis
    using sv.acov_psd sv.acov_eigen_ub aint AE_space
  proof eventually_elim
    case (elim \<omega>)
    have psdg: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and ubg: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      and ent: "\<And>u. 0 \<le> u \<Longrightarrow>
          set_integrable lborel {0..u} (\<lambda>v. acov v \<omega> $ i $ i)"
      and wsp: "\<omega> \<in> space M"
      using elim by blast+
    have pt: "0 \<le> acov \<sigma> \<omega> $ i $ i \<and> acov \<sigma> \<omega> $ i $ i \<le> L"
      if \<sigma>: "\<sigma> \<in> {s<..t}" for \<sigma>
    proof (cases "\<sigma> \<le> tau \<omega>")
      case True
      have s0: "0 \<le> \<sigma>" using \<sigma> st by auto
      with True psdg ubg have "psd (acov \<sigma> \<omega>)" "eigen_ub (acov \<sigma> \<omega>) L"
        by blast+
      then show ?thesis by (auto intro: psd_diag_nonneg eigen_ub_diag)
    next
      case False
      then have "acov \<sigma> \<omega> = 0"
        using astop[rule_format, OF wsp] by simp
      then show ?thesis using L0 by simp
    qed
    have splitset: "{0..t} = {0..s} \<union> {s<..t}" using st ts by auto
    have int_t: "set_integrable lborel {0..t} (\<lambda>v. acov v \<omega> $ i $ i)"
      using ent st ts by simp
    have int_s: "set_integrable lborel {0..s} (\<lambda>v. acov v \<omega> $ i $ i)"
      using ent st by simp
    have int_st: "set_integrable lborel {s<..t} (\<lambda>v. acov v \<omega> $ i $ i)"
      by (rule set_integrable_subset[OF int_t]) (use st in auto)
    have add: "set_lebesgue_integral lborel {0..t} (\<lambda>v. acov v \<omega> $ i $ i)
        = set_lebesgue_integral lborel {0..s} (\<lambda>v. acov v \<omega> $ i $ i)
          + set_lebesgue_integral lborel {s<..t} (\<lambda>v. acov v \<omega> $ i $ i)"
      unfolding splitset
      by (rule set_integral_Un) (auto intro: int_s int_st)
    have zero_int: "set_integrable lborel {s<..t} (\<lambda>_. 0 :: real)"
      by (simp add: set_integrable_def)
    have lower: "0 \<le> set_lebesgue_integral lborel {s<..t}
        (\<lambda>v. acov v \<omega> $ i $ i)"
    proof -
      have "set_lebesgue_integral lborel {s<..t} (\<lambda>_. 0 :: real)
          \<le> set_lebesgue_integral lborel {s<..t} (\<lambda>v. acov v \<omega> $ i $ i)"
        by (rule set_integral_mono[OF zero_int int_st]) (use pt in blast)
      then show ?thesis by simp
    qed
    have Lint: "set_integrable lborel {s<..t} (\<lambda>_. L)"
      unfolding set_integrable_def
      by (intro integrable_scaleR_left integrable_real_indicator)
        (use ts in \<open>auto simp: emeasure_lborel_Ioc\<close>)
    have upper: "set_lebesgue_integral lborel {s<..t}
        (\<lambda>v. acov v \<omega> $ i $ i) \<le> L * (t - s)"
    proof -
      have "set_lebesgue_integral lborel {s<..t} (\<lambda>v. acov v \<omega> $ i $ i)
          \<le> set_lebesgue_integral lborel {s<..t} (\<lambda>_. L)"
        by (rule set_integral_mono[OF int_st Lint]) (use pt in blast)
      also have "set_lebesgue_integral lborel {s<..t} (\<lambda>_. L)
          = measure lborel {s<..t} *\<^sub>R L"
        by (intro set_integral_const)
          (use ts in \<open>auto simp: emeasure_lborel_Ioc\<close>)
      also have "measure lborel {s<..t} = t - s"
        using ts by simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    show ?case using add lower upper by simp
  qed
qed

lemma coord_sq_bounded_test:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and Z :: "('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real" and B r :: real
  assumes W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and st: "0 \<le> s" and ts: "s \<le> t"
    and ZFs: "Z \<in> borel_measurable (F s)"
    and Zpos: "\<And>\<omega>. 0 \<le> Z \<omega>" and Zb: "\<And>\<omega>. Z \<omega> \<le> B"
  shows "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)
      \<le> L * (t - s) * (\<integral>\<omega>. Z \<omega> \<partial>M)"
proof -
  let ?A = "\<lambda>u \<omega>. set_lebesgue_integral lborel {0..u}
      (\<lambda>v. acov v \<omega> $ i $ i)"
  have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  interpret cz: martingale M F 0 "coord_Z X acov i"
    by (rule sv.coord_Z_martingale)
  have fin: "finite_measure M"
    by (rule prob_space.finite_measure[OF sv.prob_space_M])
  have t0: "0 \<le> t" using st ts by linarith
  have B0: "0 \<le> B" using Zpos[of undefined] Zb[of undefined] by linarith
  have Zabs: "\<And>\<omega>. \<bar>Z \<omega>\<bar> \<le> B"
    using Zpos Zb by (auto simp: abs_of_nonneg)
  have prj: "(\<lambda>x :: real^'m. x $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have Xm: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    using that by (intro sv.random_variable) simp
  have XiM: "(\<lambda>\<omega>. X u \<omega> $ i) \<in> borel_measurable M" if "0 \<le> u" for u
    by (intro measurable_compose[OF Xm[OF that] prj])
  have ZM: "Z \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF sv.subalgebras[OF st] ZFs])
  have bnd: "AE \<omega> in M. norm (X u \<omega>) \<le> r" if "0 \<le> u" for u
    by (rule mkt_law_witness_bound[OF W Kball that])
  have A0: "set_lebesgue_integral lborel {0..(0::real)} g = 0"
    for g :: "real \<Rightarrow> real"
  proof -
    have s0: "{(0::real)..0} = {0}" by auto
    have "AE x in lborel. indicat_real {(0::real)..0} x *\<^sub>R g x = 0"
      using AE_lborel_singleton[of "0::real"]
      by eventually_elim (auto simp: s0 indicator_def)
    then show ?thesis
      unfolding set_lebesgue_integral_def by (rule integral_eq_zero_AE)
  qed
  have cbnd: "AE \<omega> in M. 0 \<le> ?A u \<omega> \<and> ?A u \<omega> \<le> L * u"
    if u: "0 \<le> u" for u
    using witness_compensator_increment_bounds[OF W order_refl u]
    by eventually_elim (simp add: A0)
  have int_ZX2: "integrable M (\<lambda>\<omega>. Z \<omega> * (X u \<omega> $ i)\<^sup>2)"
    if u: "0 \<le> u" for u
  proof (rule finite_measure.integrable_const_bound[OF fin,
      of _ "B * r\<^sup>2"])
    show "(\<lambda>\<omega>. Z \<omega> * (X u \<omega> $ i)\<^sup>2) \<in> borel_measurable M"
      by (intro borel_measurable_times ZM borel_measurable_power XiM[OF u])
    show "AE \<omega> in M. norm (Z \<omega> * (X u \<omega> $ i)\<^sup>2) \<le> B * r\<^sup>2"
      using bnd[OF u]
    proof eventually_elim
      case (elim \<omega>)
      have absi: "\<bar>X u \<omega> $ i\<bar> \<le> r"
        using component_le_norm_cart[of "X u \<omega>" i] elim by linarith
      have "(X u \<omega> $ i)\<^sup>2 = \<bar>X u \<omega> $ i\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> r\<^sup>2" by (intro power_mono absi) simp
      finally have sq: "(X u \<omega> $ i)\<^sup>2 \<le> r\<^sup>2" .
      have "\<bar>Z \<omega> * (X u \<omega> $ i)\<^sup>2\<bar> = Z \<omega> * (X u \<omega> $ i)\<^sup>2"
        using Zpos by (simp add: abs_mult abs_of_nonneg)
      also have "\<dots> \<le> B * r\<^sup>2"
        by (intro mult_mono Zb sq) (use B0 in \<open>auto simp: Zpos\<close>)
      finally show ?case by simp
    qed
  qed
  have int_cross: "integrable M
      (\<lambda>\<omega>. (Z \<omega> * X s \<omega> $ i) * X u \<omega> $ i)"
    if u: "0 \<le> u" for u
  proof (rule finite_measure.integrable_const_bound[OF fin,
      of _ "B * r * r"])
    show "(\<lambda>\<omega>. (Z \<omega> * X s \<omega> $ i) * X u \<omega> $ i) \<in> borel_measurable M"
      by (intro borel_measurable_times ZM XiM[OF st] XiM[OF u])
    show "AE \<omega> in M. norm ((Z \<omega> * X s \<omega> $ i) * X u \<omega> $ i) \<le> B * r * r"
      using bnd[OF u] bnd[OF st]
    proof eventually_elim
      case (elim \<omega>)
      have au: "\<bar>X u \<omega> $ i\<bar> \<le> r" and as: "\<bar>X s \<omega> $ i\<bar> \<le> r"
        using component_le_norm_cart[of "X u \<omega>" i]
          component_le_norm_cart[of "X s \<omega>" i] elim by linarith+
      have "\<bar>(Z \<omega> * X s \<omega> $ i) * X u \<omega> $ i\<bar>
          = \<bar>Z \<omega>\<bar> * \<bar>X s \<omega> $ i\<bar> * \<bar>X u \<omega> $ i\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> B * r * r"
        by (intro mult_mono Zabs as au) (use B0 r0 in auto)
      finally show ?case by simp
    qed
  qed
  have Am: "(\<lambda>\<omega>. ?A u \<omega>) \<in> borel_measurable M" if u: "0 \<le> u" for u
  proof -
    have eq: "(\<lambda>\<omega>. ?A u \<omega>)
        = (\<lambda>\<omega>. (X u \<omega> $ i)\<^sup>2 - coord_Z X acov i u \<omega>)"
      by (simp add: coord_Z_def)
    show ?thesis
      unfolding eq
      by (intro borel_measurable_diff borel_measurable_power XiM[OF u]
          borel_measurable_integrable[OF cz.integrable[OF u]])
  qed
  have int_ZA: "integrable M (\<lambda>\<omega>. Z \<omega> * ?A u \<omega>)" if u: "0 \<le> u" for u
  proof (rule finite_measure.integrable_const_bound[OF fin,
      of _ "B * (L * u)"])
    show "(\<lambda>\<omega>. Z \<omega> * ?A u \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_times ZM Am[OF u])
    show "AE \<omega> in M. norm (Z \<omega> * ?A u \<omega>) \<le> B * (L * u)"
      using cbnd[OF u]
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>Z \<omega> * ?A u \<omega>\<bar> = Z \<omega> * ?A u \<omega>"
        using Zpos elim by (simp add: abs_mult abs_of_nonneg)
      also have "\<dots> \<le> B * (L * u)"
        by (intro mult_mono Zb) (use elim B0 in \<open>auto simp: Zpos\<close>)
      finally show ?case by simp
    qed
  qed
  have int_ZcZ: "integrable M (\<lambda>\<omega>. Z \<omega> * coord_Z X acov i u \<omega>)"
    if u: "0 \<le> u" for u
  proof -
    have eq: "(\<lambda>\<omega>. Z \<omega> * coord_Z X acov i u \<omega>)
        = (\<lambda>\<omega>. Z \<omega> * (X u \<omega> $ i)\<^sup>2 - Z \<omega> * ?A u \<omega>)"
      by (simp add: coord_Z_def right_diff_distrib)
    show ?thesis
      unfolding eq
      by (intro Bochner_Integration.integrable_diff int_ZX2[OF u]
          int_ZA[OF u])
  qed
  have splitE: "(\<integral>\<omega>. Z \<omega> * coord_Z X acov i u \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * (X u \<omega> $ i)\<^sup>2 \<partial>M) - (\<integral>\<omega>. Z \<omega> * ?A u \<omega> \<partial>M)"
    if u: "0 \<le> u" for u
  proof -
    have eq: "(\<lambda>\<omega>. Z \<omega> * coord_Z X acov i u \<omega>)
        = (\<lambda>\<omega>. Z \<omega> * (X u \<omega> $ i)\<^sup>2 - Z \<omega> * ?A u \<omega>)"
      by (simp add: coord_Z_def right_diff_distrib)
    show ?thesis
      unfolding eq
      by (rule Bochner_Integration.integral_diff[OF int_ZX2[OF u]
          int_ZA[OF u]])
  qed
  have XsFs: "(\<lambda>\<omega>. X s \<omega> $ i) \<in> borel_measurable (F s)"
    by (intro measurable_compose[OF _ prj] sv.adaptedD) (use st in auto)
  have ZXsFs: "(\<lambda>\<omega>. Z \<omega> * X s \<omega> $ i) \<in> borel_measurable (F s)"
    by (intro borel_measurable_times ZFs XsFs)
  have cross: "(\<integral>\<omega>. (Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i \<partial>M)
      = (\<integral>\<omega>. (Z \<omega> * X s \<omega> $ i) * X s \<omega> $ i \<partial>M)"
    by (rule martingale_bounded_test[OF martingale_vec_component[OF
        sv.martingale_axioms] st ts ZXsFs int_cross[OF t0]
        int_cross[OF st]])
  have czid: "(\<integral>\<omega>. Z \<omega> * coord_Z X acov i t \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * coord_Z X acov i s \<omega> \<partial>M)"
    by (rule martingale_bounded_test[OF sv.coord_Z_martingale st ts ZFs
        int_ZcZ[OF t0] int_ZcZ[OF st]])
  have int2: "integrable M (\<lambda>\<omega>. 2 * ((Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i))"
    using int_cross[OF t0] by simp
  have int12: "integrable M (\<lambda>\<omega>. Z \<omega> * (X t \<omega> $ i)\<^sup>2
      - 2 * ((Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i))"
    by (intro Bochner_Integration.integrable_diff int_ZX2[OF t0] int2)
  have LHS_eq: "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i)\<^sup>2 \<partial>M)
        - (\<integral>\<omega>. Z \<omega> * (X s \<omega> $ i)\<^sup>2 \<partial>M)"
  proof -
    have e1: "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)
        = (\<integral>\<omega>. (Z \<omega> * (X t \<omega> $ i)\<^sup>2
            - 2 * ((Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i))
            + Z \<omega> * (X s \<omega> $ i)\<^sup>2 \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: power2_diff algebra_simps)
    have e2: "\<dots> = (\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i)\<^sup>2
            - 2 * ((Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i) \<partial>M)
            + (\<integral>\<omega>. Z \<omega> * (X s \<omega> $ i)\<^sup>2 \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF int12 int_ZX2[OF st]])
    have e3: "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i)\<^sup>2
        - 2 * ((Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i) \<partial>M)
        = (\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i)\<^sup>2 \<partial>M)
          - 2 * (\<integral>\<omega>. (Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i \<partial>M)"
      using Bochner_Integration.integral_diff[OF int_ZX2[OF t0] int2]
      by simp
    have e4: "(\<integral>\<omega>. (Z \<omega> * X s \<omega> $ i) * X t \<omega> $ i \<partial>M)
        = (\<integral>\<omega>. Z \<omega> * (X s \<omega> $ i)\<^sup>2 \<partial>M)"
      using cross by (simp add: power2_eq_square mult.assoc)
    show ?thesis using e1 e2 e3 e4 by linarith
  qed
  have intZ: "integrable M Z"
    by (rule finite_measure.integrable_const_bound[OF fin, of _ B])
      (use ZM Zabs in auto)
  have int_LZ: "integrable M (\<lambda>\<omega>. Z \<omega> * (L * (t - s)))"
    using intZ by simp
  have int_ZAd: "integrable M (\<lambda>\<omega>. Z \<omega> * (?A t \<omega> - ?A s \<omega>))"
    using Bochner_Integration.integrable_diff[OF int_ZA[OF t0]
        int_ZA[OF st]]
    by (simp add: right_diff_distrib)
  have mono_step: "(\<integral>\<omega>. Z \<omega> * (?A t \<omega> - ?A s \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. Z \<omega> * (L * (t - s)) \<partial>M)"
  proof (rule integral_mono_AE[OF int_ZAd int_LZ])
    show "AE \<omega> in M. Z \<omega> * (?A t \<omega> - ?A s \<omega>)
        \<le> Z \<omega> * (L * (t - s))"
      using witness_compensator_increment_bounds[OF W st ts, where i = i]
    proof eventually_elim
      case (elim \<omega>)
      show ?case
        by (intro mult_left_mono) (use elim Zpos in auto)
    qed
  qed
  have "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * ?A t \<omega> \<partial>M) - (\<integral>\<omega>. Z \<omega> * ?A s \<omega> \<partial>M)"
    using LHS_eq czid splitE[OF t0] splitE[OF st] by linarith
  also have "\<dots> = (\<integral>\<omega>. Z \<omega> * (?A t \<omega> - ?A s \<omega>) \<partial>M)"
    using Bochner_Integration.integral_diff[OF int_ZA[OF t0]
        int_ZA[OF st]]
    by (simp add: right_diff_distrib)
  also have "\<dots> \<le> (\<integral>\<omega>. Z \<omega> * (L * (t - s)) \<partial>M)"
    by (rule mono_step)
  also have "\<dots> = L * (t - s) * (\<integral>\<omega>. Z \<omega> \<partial>M)"
    by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma past_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real"
  assumes st: "0 \<le> s" and sT: "s \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal (\<lambda>f. h (restrict f {0..s}))"
proof -
  have rc: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))
      (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal (h \<circ> (\<lambda>f. restrict f {0..s}))"
    by (rule continuous_map_compose[OF rc hc])
  then show ?thesis by (simp add: o_def)
qed

lemma covariation_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real" and c :: real
  assumes st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal
      (\<lambda>f. (rclamp c (f t $ i - f s $ i))\<^sup>2 * h (restrict f {0..s}))"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have part1': "continuous_map ?PT euclideanreal
      ((rclamp c \<circ> (\<lambda>v. v $ i)) \<circ> (\<lambda>f. f t - f s))"
    by (intro continuous_map_compose[OF evdiff]
        continuous_map_compose[OF cmp_i] rclamp_cont)
  have part1: "continuous_map ?PT euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i))"
    using part1' by (simp add: o_def vector_minus_component)
  have part1sq: "continuous_map ?PT euclideanreal
      (\<lambda>f. (rclamp c (f t $ i - f s $ i))\<^sup>2)"
    using continuous_map_real_mult[OF part1 part1]
    by (simp add: power2_eq_square)
  have part2: "continuous_map ?PT euclideanreal
      (\<lambda>f. h (restrict f {0..s}))"
    by (rule past_test_functional_cont[OF st sT hc])
  show ?thesis
    by (rule continuous_map_real_mult[OF part1sq part2])
qed

lemma mkt_path_laws_covariation_test:
  fixes Q :: "(real \<Rightarrow> real^'m::finite) measure"
    and h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real" and B r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and Q: "Q \<in> mkt_path_laws k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
    and hpos: "\<And>f. 0 \<le> h f" and hb: "\<And>f. h f \<le> B"
  shows "(\<integral>f. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
        * h (restrict f {0..s}) \<partial>Q)
      \<le> L * (t - s) * (\<integral>f. h (restrict f {0..s}) \<partial>Q)"
proof -
  let ?G = "\<lambda>f :: real \<Rightarrow> real^'m.
      (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2 * h (restrict f {0..s})"
  let ?H = "\<lambda>f :: real \<Rightarrow> real^'m. h (restrict f {0..s})"
  have B0: "0 \<le> B" using hpos[of "\<lambda>_. 0"] hb[of "\<lambda>_. 0"] by linarith
  have t0: "0 \<le> t" and sT: "s \<le> T" using st ts tT by linarith+
  have sI: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using st ts tT by auto
  from Q obtain M F X acov tau
    where W: "mkt_law_witness k L K x0 T Q M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  have QM: "Q = path_law M X T"
    and svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    using W unfolding mkt_law_witness_def by blast+
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have prj: "(\<lambda>x :: real^'m. x $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have Xm: "X u \<in> borel_measurable M" if "u \<in> {0..T}" for u
    using that by (intro sv.random_variable) simp
  have cont: "continuous_on {0..T} (\<lambda>u. X u \<omega>)" if "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>u. X u \<omega>) {0..T}) \<in> M \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF T0 Xm cont])
  have Gcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?G"
    by (rule covariation_test_functional_cont[OF st sT tI hc])
  have Gmeas: "?G \<in> borel_measurable (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF Gcont]
    by (simp add: borel_of_euclidean)
  have Hcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?H"
    by (rule past_test_functional_cont[OF st sT hc])
  have Hmeas: "?H \<in> borel_measurable (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF Hcont]
    by (simp add: borel_of_euclidean)
  have rr: "restrict (restrict g {0..T}) {0..s} = restrict g {0..s}"
    for g :: "real \<Rightarrow> real^'m"
    using sT by (auto simp: restrict_def fun_eq_iff)
  define Z where "Z = (\<lambda>\<omega>. h (restrict (\<lambda>u. X u \<omega>) {0..s}))"
  have Xm_Fs: "X u \<in> borel_measurable (F s)" if "u \<in> {0..s}" for u
    using that by (intro sv.adaptedD) auto
  have cont_Fs: "continuous_on {0..s} (\<lambda>u. X u \<omega>)"
    if "\<omega> \<in> space (F s)" for \<omega>
  proof -
    have "\<omega> \<in> space M" using that sv.space_F[OF st] by simp
    then show ?thesis
      by (intro continuous_on_subset[OF sv.X_paths_cont]) auto
  qed
  have pms: "(\<lambda>\<omega>. restrict (\<lambda>u. X u \<omega>) {0..s}) \<in> (F s) \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF st Xm_Fs cont_Fs])
  have hmeas: "h \<in> borel_measurable (borel_of
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF hc]
    by (simp add: borel_of_euclidean)
  have ZFs: "Z \<in> borel_measurable (F s)"
    unfolding Z_def
    using measurable_comp[OF pms hmeas] by (simp add: o_def)
  have ZM: "Z \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF sv.subalgebras[OF st] ZFs])
  have XiM: "(\<lambda>\<omega>. X u \<omega> $ i) \<in> borel_measurable M" if "u \<in> {0..T}" for u
    by (intro measurable_compose[OF Xm[OF that] prj])
  have step1: "(\<integral>f. ?G f \<partial>Q)
      = (\<integral>\<omega>. ?G (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)"
    unfolding QM path_law_def
    by (rule Bochner_Integration.integral_distr[OF pm Gmeas])
  have step1H: "(\<integral>f. ?H f \<partial>Q)
      = (\<integral>\<omega>. ?H (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)"
    unfolding QM path_law_def
    by (rule Bochner_Integration.integral_distr[OF pm Hmeas])
  have step2: "(\<integral>\<omega>. ?G (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)
      = (\<integral>\<omega>. (rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i))\<^sup>2 * Z \<omega> \<partial>M)"
    unfolding Z_def
    by (intro Bochner_Integration.integral_cong refl)
      (use st ts tT sT in \<open>simp add: rr\<close>)
  have step2H: "(\<integral>\<omega>. ?H (restrict (\<lambda>u. X u \<omega>) {0..T}) \<partial>M)
      = (\<integral>\<omega>. Z \<omega> \<partial>M)"
    unfolding Z_def
    by (intro Bochner_Integration.integral_cong refl)
      (use st ts tT sT in \<open>simp add: rr min_absorb2\<close>)
  have bnd_t: "AE \<omega> in M. norm (X t \<omega>) \<le> r"
    by (rule mkt_law_witness_bound[OF W Kball t0])
  have bnd_s: "AE \<omega> in M. norm (X s \<omega>) \<le> r"
    by (rule mkt_law_witness_bound[OF W Kball st])
  have ae_inc: "AE \<omega> in M. \<bar>X t \<omega> $ i - X s \<omega> $ i\<bar> \<le> 2 * r"
    using bnd_t bnd_s
  proof eventually_elim
    case (elim \<omega>)
    have "\<bar>X t \<omega> $ i - X s \<omega> $ i\<bar>
        \<le> \<bar>X t \<omega> $ i\<bar> + \<bar>X s \<omega> $ i\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> norm (X t \<omega>) + norm (X s \<omega>)"
      by (intro add_mono component_le_norm_cart)
    also have "\<dots> \<le> 2 * r" using elim by linarith
    finally show ?case .
  qed
  have rcm: "rclamp (2 * r) \<in> borel_measurable borel"
  proof -
    have "continuous_on UNIV (rclamp (2 * r))"
      using rclamp_cont[of "2 * r"]
      by (simp add: continuous_map_iff_continuous2)
    then show ?thesis by (rule borel_measurable_continuous_onI)
  qed
  have mcl2: "(\<lambda>\<omega>. (rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i))\<^sup>2 * Z \<omega>)
      \<in> borel_measurable M"
    by (intro borel_measurable_times ZM borel_measurable_power
        measurable_compose[OF _ rcm] borel_measurable_diff
        XiM[OF tI] XiM[OF sI])
  have mun2: "(\<lambda>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2)
      \<in> borel_measurable M"
    by (intro borel_measurable_times ZM borel_measurable_power
        borel_measurable_diff XiM[OF tI] XiM[OF sI])
  have step3: "(\<integral>\<omega>. (rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i))\<^sup>2
        * Z \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)"
  proof (rule integral_cong_AE[OF mcl2 mun2])
    show "AE \<omega> in M. (rclamp (2 * r) (X t \<omega> $ i - X s \<omega> $ i))\<^sup>2 * Z \<omega>
        = Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2"
      using ae_inc
    proof eventually_elim
      case (elim \<omega>)
      show ?case
        unfolding rclamp_id[OF elim] by (simp add: mult.commute)
    qed
  qed
  have Zpos: "\<And>\<omega>. 0 \<le> Z \<omega>" unfolding Z_def by (rule hpos)
  have Zb: "\<And>\<omega>. Z \<omega> \<le> B" unfolding Z_def by (rule hb)
  have step4: "(\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)
      \<le> L * (t - s) * (\<integral>\<omega>. Z \<omega> \<partial>M)"
    by (rule coord_sq_bounded_test[OF W Kball r0 st ts ZFs Zpos Zb])
  have "(\<integral>f. ?G f \<partial>Q)
      = (\<integral>\<omega>. Z \<omega> * (X t \<omega> $ i - X s \<omega> $ i)\<^sup>2 \<partial>M)"
    using step1 step2 step3 by simp
  also have "\<dots> \<le> L * (t - s) * (\<integral>\<omega>. Z \<omega> \<partial>M)"
    by (rule step4)
  also have "\<dots> = L * (t - s) * (\<integral>f. ?H f \<partial>Q)"
    using step1H step2H by simp
  finally show ?thesis .
qed

theorem mkt_law_closure_covariation_test:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure"
    and h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real" and B r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
    and hpos: "\<And>f. 0 \<le> h f" and hb: "\<And>f. h f \<le> B"
  shows "(\<integral>f. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
        * h (restrict f {0..s}) \<partial>\<Lambda>)
      \<le> L * (t - s) * (\<integral>f. h (restrict f {0..s}) \<partial>\<Lambda>)"
proof -
  let ?G = "\<lambda>f :: real \<Rightarrow> real^'m.
      (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2 * h (restrict f {0..s})"
  let ?H = "\<lambda>f :: real \<Rightarrow> real^'m. h (restrict f {0..s})"
  have B0: "0 \<le> B" using hpos[of "\<lambda>_. 0"] hb[of "\<lambda>_. 0"] by linarith
  have sT: "s \<le> T" using ts tT by linarith
  have tI: "t \<in> {0..T}" using st ts tT by auto
  obtain \<sigma> where r\<sigma>: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
    and lim: "limitin (weak_conv_topology (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric))) \<sigma> \<Lambda> sequentially"
    using closure_of_sequential_limit[OF metrizable_weak_conv_path_topology
        L[unfolded mkt_law_closure_def]] by blast
  have perj: "(\<integral>f. ?G f \<partial>(\<sigma> j))
      \<le> L * (t - s) * (\<integral>f. ?H f \<partial>(\<sigma> j))" for j
    using r\<sigma>
    by (intro mkt_path_laws_covariation_test[OF T0 Kball r0 _ st ts tT hc
        hpos hb]) blast
  have Gcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?G"
    by (rule covariation_test_functional_cont[OF st sT tI hc])
  have sqb: "(rclamp (2 * r) y)\<^sup>2 \<le> (2 * r)\<^sup>2" for y
  proof -
    have "(rclamp (2 * r) y)\<^sup>2 = \<bar>rclamp (2 * r) y\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> (2 * r)\<^sup>2"
      by (intro power_mono rclamp_bound) (use r0 in auto)
    finally show ?thesis .
  qed
  have Gbd: "\<exists>B'. \<forall>f\<in>topspace (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m) metric)). \<bar>?G f\<bar> \<le> B'"
  proof (intro exI[of _ "(2 * r)\<^sup>2 * B"] ballI)
    fix f :: "real \<Rightarrow> real^'m"
    have "\<bar>?G f\<bar> = (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2 * \<bar>?H f\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (2 * r)\<^sup>2 * B"
      by (intro mult_mono sqb)
        (use hpos hb B0 in \<open>auto simp: abs_of_nonneg\<close>)
    finally show "\<bar>?G f\<bar> \<le> (2 * r)\<^sup>2 * B" .
  qed
  have Hcont: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal ?H"
    by (rule past_test_functional_cont[OF st sT hc])
  have Hbd: "\<exists>B'. \<forall>f\<in>topspace (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m) metric)). \<bar>?H f\<bar> \<le> B'"
    by (intro exI[of _ B] ballI)
      (use hpos hb in \<open>auto simp: abs_of_nonneg\<close>)
  have blimG: "(\<lambda>j. \<integral>f. ?G f \<partial>(\<sigma> j)) \<longlonglongrightarrow> (\<integral>f. ?G f \<partial>\<Lambda>)"
    using lim Gcont Gbd unfolding weak_conv_on_def by blast
  have blimH: "(\<lambda>j. \<integral>f. ?H f \<partial>(\<sigma> j)) \<longlonglongrightarrow> (\<integral>f. ?H f \<partial>\<Lambda>)"
    using lim Hcont Hbd unfolding weak_conv_on_def by blast
  have blimH': "(\<lambda>j. L * (t - s) * (\<integral>f. ?H f \<partial>(\<sigma> j)))
      \<longlonglongrightarrow> L * (t - s) * (\<integral>f. ?H f \<partial>\<Lambda>)"
    by (rule tendsto_mult_left[OF blimH])
  show ?thesis
  proof (rule LIMSEQ_le[OF blimG blimH'])
    show "\<exists>N. \<forall>j\<ge>N. (\<integral>f. ?G f \<partial>(\<sigma> j))
        \<le> L * (t - s) * (\<integral>f. ?H f \<partial>(\<sigma> j))"
      using perj by blast
  qed
qed

text \<open>The matching lower bound holds at ANY measure: the integrand is
  pointwise nonnegative for a nonnegative test functional.\<close>

lemma covariation_test_nonneg:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure"
    and h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real"
  assumes hpos: "\<And>f. 0 \<le> h f"
  shows "0 \<le> (\<integral>f. (rclamp c (f t $ i - f s $ i))\<^sup>2
      * h (restrict f {0..s}) \<partial>\<Lambda>)"
  by (intro integral_nonneg_AE AE_I2 mult_nonneg_nonneg
      zero_le_power2 hpos)

subsection \<open>The paper-class value function and its usc majorant\<close>

text \<open>The class (1.7) of the paper consists of STOPPED markets: the process
  is stopped at its horizon, the covariance vanishes after it, and its
  diagonal entries are pathwise integrable --- exactly the witness
  predicate without its path-law clause.  \<open>val_fn\<close> (Value\_Function)
  quantifies over the bare locale; here we introduce the value function of
  the paper class and lift the per-witness domination
  \<open>witness_value_le_law_sup_ball\<close> to its supremum: the paper-class value
  function is dominated by the law-level value function, which
  \<open>vshift_sup_usc_mkt\<close> proves usc.  The bare-locale \<open>val_fn\<close> dominates the
  paper-class one by inclusion of the index sets; identifying the two is
  Doob's optional stopping for the whole class, which needs integrability
  of the unstopped process beyond its horizon --- information the locale
  does not carry.\<close>

definition stopped_market ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m
     \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) measure
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) measure)
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'m)
     \<Rightarrow> (real \<Rightarrow> ('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'m^'m)
     \<Rightarrow> (('m \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> bool"
  where
  "stopped_market k L K x0 M F X acov tau \<longleftrightarrow>
     sufficiently_volatile_market M F X acov k L K x0 tau
     \<and> (\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>)
     \<and> (\<forall>s \<omega>. \<omega> \<in> space M \<longrightarrow> tau \<omega> < s \<longrightarrow> acov s \<omega> = 0)
     \<and> (AE \<omega> in M. \<forall>l t. 0 \<le> t \<longrightarrow>
           set_integrable lborel {0..t} (\<lambda>s. acov s \<omega> $ l $ l))"

lemma mkt_law_witness_iff:
  "mkt_law_witness k L K x0 T Q M F X acov tau \<longleftrightarrow>
     Q = path_law M X T \<and> stopped_market k L K x0 M F X acov tau"
  unfolding mkt_law_witness_def stopped_market_def by blast

definition stopped_exit_vals ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> ennreal set"
  where
  "stopped_exit_vals k L K x0 =
     {c. \<exists>M F X acov tau. stopped_market k L K x0 M F X acov tau
           \<and> c = ess_inf_time M tau}"

definition stopped_val_fn ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> ennreal"
  where
  "stopped_val_fn k L K x0 = Sup (stopped_exit_vals k L K x0)"

lemma stopped_exit_vals_subset:
  "stopped_exit_vals k L K x0 \<subseteq> mkt_exit_vals k L K x0"
  unfolding stopped_exit_vals_def mkt_exit_vals_def stopped_market_def
  by blast

lemma stopped_val_fn_le_val_fn:
  "stopped_val_fn k L K x0 \<le> val_fn k L K x0"
  unfolding stopped_val_fn_def val_fn_def
  by (rule Sup_subset_mono[OF stopped_exit_vals_subset])

lemma stopped_exit_vals_nonempty:
  fixes x0 :: "real^'m::finite" and K :: "(real^'m) set"
  assumes k: "1 \<le> k" "k < CARD('m)" and L: "1 \<le> L" and x0K: "x0 \<in> K"
  shows "stopped_exit_vals k L K x0 \<noteq> {}"
proof -
  obtain Q where "Q \<in> mkt_path_laws k L K x0 0"
    using mkt_path_laws_nonempty[OF k L x0K] by blast
  then obtain M F X acov tau
    where "mkt_law_witness k L K x0 0 Q M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  then have "stopped_market k L K x0 M F X acov tau"
    unfolding mkt_law_witness_iff by blast
  then show ?thesis
    unfolding stopped_exit_vals_def by blast
qed

theorem stopped_val_fn_le_law_sup:
  fixes x0 :: "real^'m::finite" and K :: "(real^'m) set"
    and A :: "(real^'m) set" and T r :: real
  assumes Kball: "K \<subseteq> cball 0 r" and x0K: "x0 \<in> K"
    and A: "open A" and AK: "A \<inter> K = {}" and T0: "0 \<le> T"
    and bT: "ball_v r k x0 \<le> T"
  shows "stopped_val_fn k L K x0
      \<le> ennreal (Sup (vshift T A x0
          ` mkt_law_closure k L (cball 0 (2 * r)) 0 T))"
  unfolding stopped_val_fn_def
proof (rule Sup_least)
  fix c assume "c \<in> stopped_exit_vals k L K x0"
  then obtain M F X acov tau
    where SM: "stopped_market k L K x0 M F X acov tau"
      and c: "c = ess_inf_time M tau"
    unfolding stopped_exit_vals_def mem_Collect_eq by blast
  have W: "mkt_law_witness k L K x0 T (path_law M X T) M F X acov tau"
    unfolding mkt_law_witness_iff using SM by blast
  show "c \<le> ennreal (Sup (vshift T A x0
      ` mkt_law_closure k L (cball 0 (2 * r)) 0 T))"
    unfolding c
    by (rule witness_value_le_law_sup_ball[OF W Kball x0K A AK T0 bT])
qed

subsection \<open>From continuous tests to the past \<open>\<sigma>\<close>-algebra\<close>

text \<open>A finite Borel measure on a metric space is determined by its
  integrals against bounded continuous functions: apply the closed-set
  Portmanteau bound to the CONSTANT sequence in both directions, then
  extend from closed sets (an intersection-stable generator of the Borel
  \<open>\<sigma>\<close>-algebra, \<open>sets_borel_of_closed\<close>) by \<open>measure_eqI_generator_eq\<close>.
  This is the monotone-class engine that upgrades the integrated
  identities on closure points from continuous past functionals to
  arbitrary past events.\<close>

lemma metric_measure_eqI_bounded_cts:
  fixes m :: "'a metric" and M1 M2 :: "'a measure"
  assumes s1: "sets M1 = sets (borel_of (mtopology_of m))"
    and s2: "sets M2 = sets (borel_of (mtopology_of m))"
    and f1: "finite_measure M1" and f2: "finite_measure M2"
    and eq: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        \<exists>B. \<forall>x\<in>topspace (mtopology_of m). \<bar>g x\<bar> \<le> B \<Longrightarrow>
        (\<integral>x. g x \<partial>M1) = (\<integral>x. g x \<partial>M2)"
  shows "M1 = M2"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have tsp: "topspace (mtopology_of m) = mspace m"
    using top PM.topspace_mtopology by simp
  have le: "measure Ma A \<le> measure Mb A"
    if sa: "sets Ma = sets (borel_of (mtopology_of m))"
    and sb: "sets Mb = sets (borel_of (mtopology_of m))"
    and fa: "finite_measure Ma" and fb: "finite_measure Mb"
    and eqab: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        \<exists>B. \<forall>x\<in>topspace (mtopology_of m). \<bar>g x\<bar> \<le> B \<Longrightarrow>
        (\<integral>x. g x \<partial>Ma) = (\<integral>x. g x \<partial>Mb)"
    and clA: "closedin (mtopology_of m) A"
    for Ma Mb :: "'a measure" and A
  proof -
    interpret MW: mweak_conv_fin "mspace m" "mdist m" "\<lambda>_ :: nat. Ma"
        Mb sequentially
    proof
      show "\<forall>\<^sub>F i in sequentially.
          sets ((\<lambda>_ :: nat. Ma) i) = sets (borel_of PM.mtopology)"
        using sa top by simp
      show "sets Mb = sets (borel_of PM.mtopology)"
        using sb top by simp
      show "\<forall>\<^sub>F i in sequentially. finite_measure ((\<lambda>_ :: nat. Ma) i)"
        using fa by simp
      show "\<exists>A. countable A \<and> A \<subseteq> sets Mb \<and> \<Union> A = space Mb
          \<and> (\<forall>a\<in>A. emeasure Mb a \<noteq> \<infinity>)"
        by (intro exI[of _ "{space Mb}"])
          (auto simp: finite_measure.emeasure_eq_measure[OF fb])
      show "emeasure Mb (space Mb) \<noteq> \<top>"
        by (simp add: finite_measure.emeasure_eq_measure[OF fb])
    qed
    have key: "Limsup sequentially (\<lambda>x. ereal (measure Ma A))
        \<le> ereal (measure Mb A)"
    proof (rule MW.mweak_conv2)
      fix g :: "'a \<Rightarrow> real"
      assume u: "uniformly_continuous_map PM.Self euclidean_metric g"
        and b: "\<exists>B. \<forall>x\<in>mspace m. \<bar>g x\<bar> \<le> B"
      have cg: "continuous_map (mtopology_of m) euclideanreal g"
        using uniformly_continuous_imp_continuous_map[OF u]
        by (simp add: mtopology_of_def)
      have "(\<integral>x. g x \<partial>Ma) = (\<integral>x. g x \<partial>Mb)"
        by (rule eqab[OF cg]) (use b in \<open>simp add: tsp\<close>)
      then show "((\<lambda>i. \<integral>x. g x \<partial>((\<lambda>_ :: nat. Ma) i))
          \<longlongrightarrow> (\<integral>x. g x \<partial>Mb)) sequentially"
        by simp
    next
      show "closedin PM.mtopology A" using clA top by simp
    qed
    have "Limsup sequentially (\<lambda>x. ereal (measure Ma A))
        = ereal (measure Ma A)"
      by (simp add: Limsup_const)
    with key show ?thesis by simp
  qed
  have eqC: "emeasure M1 C = emeasure M2 C"
    if C: "closedin (mtopology_of m) C" for C
  proof -
    have "measure M1 C \<le> measure M2 C"
      by (rule le[OF s1 s2 f1 f2 eq C])
    moreover have "measure M2 C \<le> measure M1 C"
      by (rule le[OF s2 s1 f2 f1 eq[symmetric] C])
    ultimately have "measure M1 C = measure M2 C" by linarith
    then show ?thesis
      by (simp add: finite_measure.emeasure_eq_measure[OF f1]
          finite_measure.emeasure_eq_measure[OF f2])
  qed
  show ?thesis
  proof (rule measure_eqI_generator_eq[of "{C. closedin (mtopology_of m) C}"
      "topspace (mtopology_of m)" M1 M2
      "\<lambda>_ :: nat. topspace (mtopology_of m)"])
    show "Int_stable {C. closedin (mtopology_of m) C}"
      by (auto simp: Int_stable_def closedin_Int)
    show "{C. closedin (mtopology_of m) C} \<subseteq> Pow (topspace (mtopology_of m))"
      by (fastforce dest: closedin_subset)
    show "\<And>X. X \<in> {C. closedin (mtopology_of m) C}
        \<Longrightarrow> emeasure M1 X = emeasure M2 X"
      using eqC by auto
    show "sets M1 = sigma_sets (topspace (mtopology_of m))
        {C. closedin (mtopology_of m) C}"
      unfolding s1 by (rule sets_borel_of_closed)
    show "sets M2 = sigma_sets (topspace (mtopology_of m))
        {C. closedin (mtopology_of m) C}"
      unfolding s2 by (rule sets_borel_of_closed)
    show "range (\<lambda>_ :: nat. topspace (mtopology_of m))
        \<subseteq> {C. closedin (mtopology_of m) C}"
      using closedin_topspace[of "mtopology_of m"] by auto
    show "(\<Union>i :: nat. topspace (mtopology_of m)) = topspace (mtopology_of m)"
      by simp
    show "\<And>i :: nat. emeasure M1 (topspace (mtopology_of m)) \<noteq> \<infinity>"
      by (simp add: finite_measure.emeasure_eq_measure[OF f1])
  qed
qed

text \<open>The integrated martingale identity holds against EVERY past event, not
  just against continuous past functionals: split the clamped increment
  into its positive and negative parts, push both through the restriction
  map as densities, and observe that the two image measures integrate every
  bounded continuous function identically --- so they are EQUAL, and their
  agreement on all Borel sets is exactly the identity against indicator
  test functions.  This is the monotone-class step of the canonical-market
  construction.\<close>

theorem mkt_law_closure_martingale_event:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
  shows "(\<integral>f. rclamp (2 * r) (f t $ i - f s $ i)
      * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>) = 0"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  let ?PS = "mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)"
  let ?g = "\<lambda>f :: real \<Rightarrow> real^'m. rclamp (2 * r) (f t $ i - f s $ i)"
  let ?p = "\<lambda>f :: real \<Rightarrow> real^'m. restrict f {0..s}"
  have sT: "s \<le> T" and t0: "0 \<le> t" using st ts tT by linarith+
  have tI: "t \<in> {0..T}" using st ts tT by auto
  have finL: "finite_measure \<Lambda>"
    by (rule prob_space.finite_measure[OF mkt_law_closure_prob[OF T0 L]])
  have s\<Lambda>: "sets \<Lambda> = sets (borel_of ?PT)"
    by (rule mkt_law_closure_sets[OF L])
  have onec: "continuous_map ?PS euclideanreal (\<lambda>_. 1 :: real)" by simp
  have gcont: "continuous_map ?PT euclideanreal ?g"
    using martingale_test_functional_cont[OF st sT tI onec,
        where c = "2 * r" and i = i] by simp
  have gmeas: "?g \<in> borel_measurable (borel_of ?PT)"
    using continuous_map_measurable[OF gcont]
    by (simp add: borel_of_euclidean)
  have gmeasL: "?g \<in> borel_measurable \<Lambda>"
    using gmeas measurable_cong_sets[OF s\<Lambda> refl] by blast
  have gbnd: "\<bar>?g f\<bar> \<le> 2 * r" for f
    using rclamp_bound[of "2 * r"] r0 by simp
  have rc: "continuous_map ?PT ?PS ?p"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pim: "?p \<in> borel_of ?PT \<rightarrow>\<^sub>M borel_of ?PS"
    by (rule continuous_map_measurable[OF rc])
  have pimL: "?p \<in> \<Lambda> \<rightarrow>\<^sub>M borel_of ?PS"
    using pim measurable_cong_sets[OF s\<Lambda> refl] by blast
  define gp where "gp = (\<lambda>f :: real \<Rightarrow> real^'m. max (?g f) 0)"
  define gm where "gm = (\<lambda>f :: real \<Rightarrow> real^'m. max (- ?g f) 0)"
  have gp0: "\<And>f. 0 \<le> gp f" and gm0: "\<And>f. 0 \<le> gm f"
    unfolding gp_def gm_def by simp_all
  have gpb: "\<And>f. gp f \<le> 2 * r" and gmb: "\<And>f. gm f \<le> 2 * r"
    unfolding gp_def gm_def using gbnd r0 by (auto simp: abs_le_iff)
  have gdiff: "gp f - gm f = ?g f" for f
    unfolding gp_def gm_def by (simp add: max_def)
  have gpm: "gp \<in> borel_measurable \<Lambda>" and gmm: "gm \<in> borel_measurable \<Lambda>"
    unfolding gp_def gm_def
    by (intro borel_measurable_max gmeasL borel_measurable_const
        borel_measurable_uminus)+
  define N1 where
    "N1 = distr (density \<Lambda> (\<lambda>f. ennreal (gp f))) (borel_of ?PS) ?p"
  define N2 where
    "N2 = distr (density \<Lambda> (\<lambda>f. ennreal (gm f))) (borel_of ?PS) ?p"
  have sN1: "sets N1 = sets (borel_of ?PS)"
    and sN2: "sets N2 = sets (borel_of ?PS)"
    unfolding N1_def N2_def by simp_all
  have pdm: "?p \<in> density \<Lambda> (\<lambda>f. ennreal (w f)) \<rightarrow>\<^sub>M borel_of ?PS" for w
    using pimL measurable_cong_sets[OF sets_density refl] by blast
  have push: "(\<integral>x. u x \<partial>(distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
        (borel_of ?PS) ?p))
      = (\<integral>f. u (?p f) * w f \<partial>\<Lambda>)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and wm: "w \<in> borel_measurable \<Lambda>" and w0: "\<And>f. 0 \<le> w f"
    for u w
  proof -
    have cmp: "(\<lambda>f. u (?p f)) \<in> borel_measurable \<Lambda>"
      using measurable_comp[OF pimL um] by (simp add: o_def)
    have "(\<integral>x. u x \<partial>(distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
          (borel_of ?PS) ?p))
        = (\<integral>f. u (?p f) \<partial>(density \<Lambda> (\<lambda>f. ennreal (w f))))"
      by (rule Bochner_Integration.integral_distr[OF pdm um])
    also have "\<dots> = (\<integral>f. u (?p f) * w f \<partial>\<Lambda>)"
      by (subst integral_density)
        (use cmp wm w0 in \<open>auto simp: mult.commute intro!: AE_I2\<close>)
    finally show ?thesis .
  qed
  have finw: "finite_measure (distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
      (borel_of ?PS) ?p)"
    if wm: "w \<in> borel_measurable \<Lambda>" and w0: "\<And>f. 0 \<le> w f"
    and wb: "\<And>f. w f \<le> 2 * r" for w
  proof (rule finite_measureI)
    let ?D = "density \<Lambda> (\<lambda>f. ennreal (w f))"
    have sp: "space (distr ?D (borel_of ?PS) ?p) = space (borel_of ?PS)"
      by simp
    have pre: "?p -` space (borel_of ?PS) \<inter> space ?D = space \<Lambda>"
      using measurable_space[OF pdm[of w]] by (auto simp: space_density)
    have "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p))
        = emeasure ?D (?p -` space (borel_of ?PS) \<inter> space ?D)"
      unfolding sp
      by (intro emeasure_distr pdm)
        (metis sets.top space_borel_of)
    also have "\<dots> = emeasure ?D (space \<Lambda>)" unfolding pre ..
    also have "\<dots> = (\<integral>\<^sup>+f. ennreal (w f) * indicator (space \<Lambda>) f \<partial>\<Lambda>)"
      by (intro emeasure_density measurable_compose[OF wm measurable_ennreal])
        auto
    also have "\<dots> \<le> (\<integral>\<^sup>+f. ennreal (2 * r) \<partial>\<Lambda>)"
      by (intro nn_integral_mono)
        (auto simp: indicator_def intro: ennreal_leI wb)
    also have "\<dots> = ennreal (2 * r) * emeasure \<Lambda> (space \<Lambda>)"
      by (rule nn_integral_const)
    also have "\<dots> < \<infinity>"
      using finite_measure.emeasure_eq_measure[OF finL]
      by (simp add: ennreal_mult_less_top)
    finally show "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p)) \<noteq> \<infinity>"
      by simp
  qed
  have int_pair: "integrable \<Lambda> (\<lambda>f. u (?p f) * w f)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and ub: "\<And>x. \<bar>u x\<bar> \<le> C"
    and wm: "w \<in> borel_measurable \<Lambda>" and w0: "\<And>f. 0 \<le> w f"
    and wb: "\<And>f. w f \<le> 2 * r" for u w C
  proof (rule finite_measure.integrable_const_bound[OF finL,
      of _ "C * (2 * r)"])
    have cmp: "(\<lambda>f. u (?p f)) \<in> borel_measurable \<Lambda>"
      using measurable_comp[OF pimL um] by (simp add: o_def)
    show "(\<lambda>f. u (?p f) * w f) \<in> borel_measurable \<Lambda>"
      by (intro borel_measurable_times cmp wm)
    have C0: "0 \<le> C" using ub[of undefined] by auto
    show "AE f in \<Lambda>. norm (u (?p f) * w f) \<le> C * (2 * r)"
    proof (intro AE_I2)
      fix f :: "real \<Rightarrow> real^'m"
      have "\<bar>u (?p f) * w f\<bar> = \<bar>u (?p f)\<bar> * \<bar>w f\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> C * (2 * r)"
        by (intro mult_mono ub) (use w0 wb C0 in auto)
      finally show "norm (u (?p f) * w f) \<le> C * (2 * r)" by simp
    qed
  qed
  have zero_diff: "(\<integral>f. u (?p f) * gp f \<partial>\<Lambda>) = (\<integral>f. u (?p f) * gm f \<partial>\<Lambda>)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and ub: "\<And>x. \<bar>u x\<bar> \<le> C"
    and z: "(\<integral>f. ?g f * u (?p f) \<partial>\<Lambda>) = 0" for u C
  proof -
    have i1: "integrable \<Lambda> (\<lambda>f. u (?p f) * gp f)"
      by (rule int_pair[OF um ub gpm gp0 gpb])
    have i2: "integrable \<Lambda> (\<lambda>f. u (?p f) * gm f)"
      by (rule int_pair[OF um ub gmm gm0 gmb])
    have "(\<integral>f. u (?p f) * gp f \<partial>\<Lambda>) - (\<integral>f. u (?p f) * gm f \<partial>\<Lambda>)
        = (\<integral>f. u (?p f) * gp f - u (?p f) * gm f \<partial>\<Lambda>)"
      by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
    also have "\<dots> = (\<integral>f. ?g f * u (?p f) \<partial>\<Lambda>)"
      by (intro Bochner_Integration.integral_cong refl)
        (metis gdiff right_diff_distrib mult.commute)
    also have "\<dots> = 0" by (rule z)
    finally show ?thesis by simp
  qed
  have N12: "N1 = N2"
  proof (rule metric_measure_eqI_bounded_cts[where m = "path_metric s"])
    show "sets N1 = sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
      by (rule sN1)
    show "sets N2 = sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
      by (rule sN2)
    show "finite_measure N1"
      unfolding N1_def by (rule finw[OF gpm gp0 gpb])
    show "finite_measure N2"
      unfolding N2_def by (rule finw[OF gmm gm0 gmb])
  next
    fix h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real"
    assume hc: "continuous_map ?PS euclideanreal h"
      and hbex: "\<exists>B. \<forall>x\<in>topspace ?PS. \<bar>h x\<bar> \<le> B"
    obtain Bh where Bh: "\<And>x. x \<in> topspace ?PS \<Longrightarrow> \<bar>h x\<bar> \<le> Bh"
      using hbex by blast
    define BB where "BB = max Bh 0"
    define h' where "h' = (\<lambda>x. rclamp BB (h x))"
    have BB0: "0 \<le> BB" unfolding BB_def by simp
    have h'b: "\<And>x. \<bar>h' x\<bar> \<le> BB"
      unfolding h'_def by (intro rclamp_bound BB0)
    have h'c: "continuous_map ?PS euclideanreal h'"
      unfolding h'_def
      using continuous_map_compose[OF hc rclamp_cont]
      by (simp add: o_def)
    have h'meas: "h' \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF h'c]
      by (simp add: borel_of_euclidean)
    have hh': "h' x = h x" if x: "x \<in> topspace ?PS" for x
      unfolding h'_def
      by (intro rclamp_id order_trans[OF Bh[OF x]]) (simp add: BB_def)
    have z: "(\<integral>f. ?g f * h' (?p f) \<partial>\<Lambda>) = 0"
      by (rule mkt_law_closure_martingale_test[OF T0 Kball r0 L st ts tT
          h'c, of BB]) (use h'b in auto)
    have eqh': "(\<integral>x. h' x \<partial>N1) = (\<integral>x. h' x \<partial>N2)"
      unfolding N1_def N2_def
      unfolding push[OF h'meas gpm gp0] push[OF h'meas gmm gm0]
      by (rule zero_diff[OF h'meas h'b z])
    have c1: "(\<integral>x. h x \<partial>N1) = (\<integral>x. h' x \<partial>N1)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: hh' space_borel_of N1_def)
    have c2: "(\<integral>x. h x \<partial>N2) = (\<integral>x. h' x \<partial>N2)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: hh' space_borel_of N2_def)
    show "(\<integral>x. h x \<partial>N1) = (\<integral>x. h x \<partial>N2)"
      using eqh' c1 c2 by simp
  qed
  have iB: "indicat_real B \<in> borel_measurable (borel_of ?PS)"
    using B by (rule borel_measurable_indicator)
  have iBb: "\<And>x. \<bar>indicat_real B x\<bar> \<le> 1"
    by (simp add: indicator_def)
  have tr1: "(\<integral>x. indicat_real B x \<partial>N1)
      = (\<integral>f. indicat_real B (?p f) * gp f \<partial>\<Lambda>)"
    unfolding N1_def by (rule push[OF iB gpm gp0])
  have tr2: "(\<integral>x. indicat_real B x \<partial>N2)
      = (\<integral>f. indicat_real B (?p f) * gm f \<partial>\<Lambda>)"
    unfolding N2_def by (rule push[OF iB gmm gm0])
  have same: "(\<integral>f. indicat_real B (?p f) * gp f \<partial>\<Lambda>)
      = (\<integral>f. indicat_real B (?p f) * gm f \<partial>\<Lambda>)"
    using N12 tr1 tr2 by simp
  have i1: "integrable \<Lambda> (\<lambda>f. indicat_real B (?p f) * gp f)"
    by (rule int_pair[OF iB iBb gpm gp0 gpb])
  have i2: "integrable \<Lambda> (\<lambda>f. indicat_real B (?p f) * gm f)"
    by (rule int_pair[OF iB iBb gmm gm0 gmb])
  have "(\<integral>f. ?g f * indicat_real B (?p f) \<partial>\<Lambda>)
      = (\<integral>f. indicat_real B (?p f) * gp f
          - indicat_real B (?p f) * gm f \<partial>\<Lambda>)"
    by (intro Bochner_Integration.integral_cong refl)
      (metis gdiff right_diff_distrib mult.commute)
  also have "\<dots> = (\<integral>f. indicat_real B (?p f) * gp f \<partial>\<Lambda>)
      - (\<integral>f. indicat_real B (?p f) * gm f \<partial>\<Lambda>)"
    by (rule Bochner_Integration.integral_diff[OF i1 i2])
  also have "\<dots> = 0" using same by simp
  finally show ?thesis .
qed

text \<open>The one-sided companion of \<open>metric_measure_eqI_bounded_cts\<close>: if one
  finite Borel measure integrates every continuous \<open>[0,1]\<close>-valued function
  below another, it is dominated on every Borel set.  Closed sets first,
  by the Urysohn sandwich \<open>1\<^sub>C \<le> f\<^sub>m \<le> 1\<^bsub>U\<^sub>m\<^esub>\<close> with \<open>U\<^sub>m \<down> C\<close> and continuity
  from above; general Borel sets by inner regularity
  (\<open>finite_measure.inner_regular'\<close>, AFP Riesz--Representation).  One-sided
  bounds do NOT extend from a generator by a Dynkin argument, so the
  regularity detour is essential.\<close>

lemma metric_measure_mono_bounded_cts:
  fixes m :: "'a metric" and M1 M2 :: "'a measure"
  assumes s1: "sets M1 = sets (borel_of (mtopology_of m))"
    and s2: "sets M2 = sets (borel_of (mtopology_of m))"
    and f1: "finite_measure M1" and f2: "finite_measure M2"
    and le: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        (\<And>x. 0 \<le> g x) \<Longrightarrow> (\<And>x. g x \<le> 1) \<Longrightarrow>
        (\<integral>x. g x \<partial>M1) \<le> (\<integral>x. g x \<partial>M2)"
    and A: "A \<in> sets M1"
  shows "measure M1 A \<le> measure M2 A"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have tsp: "topspace (mtopology_of m) = mspace m"
    using top PM.topspace_mtopology by simp
  have leC: "measure M1 C \<le> measure M2 C"
    if Ccl: "closedin (mtopology_of m) C" for C
  proof (cases "C = {}")
    case True
    then show ?thesis by simp
  next
    case False
    have CM: "C \<subseteq> mspace m"
      using closedin_subset[OF Ccl] tsp by simp
    have Csets1: "C \<in> sets M1" and Csets2: "C \<in> sets M2"
      using borel_of_closed[OF Ccl] s1 s2 by simp_all
    define Um where "Um = (\<lambda>mm :: nat. \<Union>a\<in>C. PM.mball a (1 / Suc mm))"
    have Um_open: "openin (mtopology_of m) (Um mm)" for mm
      unfolding Um_def top[symmetric] by (auto intro!: PM.openin_mball)
    have Um_sets2: "Um mm \<in> sets M2" for mm
      using borel_of_open[OF Um_open] s2 by simp
    have C_Um: "C \<subseteq> Um mm" for mm
      unfolding Um_def using CM
      by (auto intro!: bexI PM.centre_in_mball_iff[THEN iffD2])
    have Um_dec: "decseq Um"
    proof (rule decseq_SucI)
      fix mm :: nat
      have "1 / Suc (Suc mm) \<le> 1 / Suc mm"
        by (simp add: frac_le)
      then show "Um (Suc mm) \<subseteq> Um mm"
        unfolding Um_def by (auto simp: PM.in_mball)
    qed
    have Um_Int: "(\<Inter>mm. Um mm) = C"
    proof
      show "C \<subseteq> (\<Inter>mm. Um mm)" using C_Um by blast
      show "(\<Inter>mm. Um mm) \<subseteq> C"
      proof
        fix x assume x: "x \<in> (\<Inter>mm. Um mm)"
        then have xM: "x \<in> mspace m"
          unfolding Um_def by (auto simp: PM.in_mball)
        show "x \<in> C"
        proof (rule ccontr)
          assume xC: "x \<notin> C"
          have op: "openin (mtopology_of m) (topspace (mtopology_of m) - C)"
            using Ccl unfolding closedin_def by blast
          have xin: "x \<in> topspace (mtopology_of m) - C"
            using xM xC tsp by simp
          obtain r where r0: "0 < r"
            and rsub: "PM.mball x r \<subseteq> topspace (mtopology_of m) - C"
            using op[unfolded top[symmetric] PM.openin_mtopology] xin
              top by auto
          obtain mm where mm: "1 / Suc mm < r"
            using reals_Archimedean[OF r0] by (auto simp: inverse_eq_divide)
          obtain a where a: "a \<in> C" "x \<in> PM.mball a (1 / Suc mm)"
            using x unfolding Um_def by blast
          have "mdist m a x < 1 / Suc mm" and aM: "a \<in> mspace m"
            using a by (auto simp: PM.in_mball)
          then have "a \<in> PM.mball x r"
            using mm xM by (auto simp: PM.in_mball PM.commute)
          then have "a \<notin> C" using rsub by auto
          with a show False by simp
        qed
      qed
    qed
    have bound: "measure M1 C \<le> measure M2 (Um mm)" for mm
    proof -
      have cl2: "closedin (mtopology_of m)
          (topspace (mtopology_of m) - Um mm)"
        using Um_open[of mm] openin_subset[OF Um_open[of mm]]
        by (auto simp: closedin_def Diff_Diff_Int Int_absorb1 tsp)
      have disj: "C \<inter> (topspace (mtopology_of m) - Um mm) = {}"
        using C_Um[of mm] by blast
      have sep: "1 / Suc mm \<le> mdist m x y"
        if xy: "x \<in> C" "y \<in> topspace (mtopology_of m) - Um mm" for x y
      proof (rule ccontr)
        assume "\<not> 1 / Suc mm \<le> mdist m x y"
        then have "mdist m x y < 1 / Suc mm" by simp
        then have "y \<in> PM.mball x (1 / Suc mm)"
          using xy CM tsp by (auto simp: PM.in_mball)
        then have "y \<in> Um mm"
          unfolding Um_def using xy by blast
        with xy show False by simp
      qed
      obtain fm :: "'a \<Rightarrow> real"
        where fmU: "uniformly_continuous_map m euclidean_metric fm"
        and fm0: "\<And>x. 0 \<le> fm x" and fm1: "\<And>x. fm x \<le> 1"
        and fmC: "\<And>x. x \<in> C \<Longrightarrow> fm x = 1"
        and fmZ: "\<And>x. x \<in> topspace (mtopology_of m) - Um mm \<Longrightarrow> fm x = 0"
        using Urysohn_lemma_uniform[OF Ccl cl2 disj sep] by auto
      have fmc: "continuous_map (mtopology_of m) euclideanreal fm"
        using uniformly_continuous_imp_continuous_map[OF fmU]
        by (simp add: mtopology_of_def)
      have fmmeas: "fm \<in> borel_measurable (borel_of (mtopology_of m))"
        using continuous_map_measurable[OF fmc]
        by (simp add: borel_of_euclidean)
      have fmm1: "fm \<in> borel_measurable M1"
        using fmmeas measurable_cong_sets[OF s1 refl] by blast
      have fmm2: "fm \<in> borel_measurable M2"
        using fmmeas measurable_cong_sets[OF s2 refl] by blast
      have int_fm1: "integrable M1 fm"
        by (rule finite_measure.integrable_const_bound[OF f1, of _ 1])
          (use fm0 fm1 fmm1 in auto)
      have int_fm2: "integrable M2 fm"
        by (rule finite_measure.integrable_const_bound[OF f2, of _ 1])
          (use fm0 fm1 fmm2 in auto)
      have int_indC: "integrable M1 (indicat_real C)"
        by (intro integrable_real_indicator Csets1)
          (simp add: finite_measure.emeasure_eq_measure[OF f1])
      have "measure M1 C = (\<integral>x. indicat_real C x \<partial>M1)"
        using Csets1 by simp
      also have "\<dots> \<le> (\<integral>x. fm x \<partial>M1)"
        by (intro integral_mono int_indC int_fm1)
          (use fm0 fmC in \<open>auto simp: indicator_def\<close>)
      also have "\<dots> \<le> (\<integral>x. fm x \<partial>M2)"
        by (rule le[OF fmc fm0 fm1])
      also have "\<dots> \<le> (\<integral>x. indicat_real (Um mm) x \<partial>M2)"
      proof (rule integral_mono_AE[OF int_fm2])
        show "integrable M2 (indicat_real (Um mm))"
          by (intro integrable_real_indicator Um_sets2)
            (simp add: finite_measure.emeasure_eq_measure[OF f2])
        show "AE x in M2. fm x \<le> indicat_real (Um mm) x"
        proof (intro AE_I2)
          fix x assume x: "x \<in> space M2"
          have xtop: "x \<in> topspace (mtopology_of m)"
            using x
            by (simp add: sets_eq_imp_space_eq[OF s2] space_borel_of)
          show "fm x \<le> indicat_real (Um mm) x"
          proof (cases "x \<in> Um mm")
            case True then show ?thesis
              using fm1 by (simp add: indicator_def)
          next
            case False then show ?thesis
              using fmZ xtop by (simp add: indicator_def)
          qed
        qed
      qed
      also have "\<dots> = measure M2 (Um mm)"
        using Um_sets2 by simp
      finally show ?thesis .
    qed
    have lim: "(\<lambda>mm. measure M2 (Um mm)) \<longlonglongrightarrow> measure M2 C"
      using finite_measure.finite_Lim_measure_decseq[OF f2 _ Um_dec]
        Um_sets2 Um_Int by auto
    show ?thesis
      by (rule LIMSEQ_le_const[OF lim]) (use bound in auto)
  qed
  have mtz: "metrizable_space (mtopology_of m)"
    using PM.metrizable_space_mtopology top by simp
  have ir: "inner_regular (mtopology_of m) M1"
    by (rule finite_measure.inner_regular'[OF f1 mtz s1[symmetric]])
  have "measure M1 A
      = (\<Squnion>C\<in>{C. closedin (mtopology_of m) C \<and> C \<subseteq> A}. measure M1 C)"
    by (rule finite_measure.inner_regularD[OF f1 ir A])
  also have "\<dots> \<le> measure M2 A"
  proof (rule cSUP_least)
    show "{C. closedin (mtopology_of m) C \<and> C \<subseteq> A} \<noteq> {}"
      by (auto intro!: exI[of _ "{}"])
    fix C assume "C \<in> {C. closedin (mtopology_of m) C \<and> C \<subseteq> A}"
    then have Ccl: "closedin (mtopology_of m) C" and CA: "C \<subseteq> A" by auto
    have "measure M1 C \<le> measure M2 C" by (rule leC[OF Ccl])
    also have "\<dots> \<le> measure M2 A"
      by (intro finite_measure.finite_measure_mono[OF f2 CA])
        (use A s1 s2 in simp)
    finally show "measure M1 C \<le> measure M2 A" .
  qed
  finally show ?thesis .
qed

text \<open>The covariation upper bound against EVERY past event: push the
  squared clamped increment and the constant \<open>L \<cdot> (t - s)\<close> through the
  restriction map as densities; the continuous-test inequality
  \<open>mkt_law_closure_covariation_test\<close> and the domination lemma turn the
  pair into measure domination on the whole past Borel \<open>\<sigma>\<close>-algebra.\<close>

theorem mkt_law_closure_covariation_event:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes T0: "0 \<le> T" and Kball: "K \<subseteq> cball 0 r" and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
  shows "(\<integral>f. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)
      \<le> L * (t - s) * (\<integral>f. indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  let ?PS = "mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)"
  let ?q = "\<lambda>f :: real \<Rightarrow> real^'m. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2"
  let ?p = "\<lambda>f :: real \<Rightarrow> real^'m. restrict f {0..s}"
  have sT: "s \<le> T" and t0: "0 \<le> t" using st ts tT by linarith+
  have tI: "t \<in> {0..T}" using st ts tT by auto
  have finL: "finite_measure \<Lambda>"
    by (rule prob_space.finite_measure[OF mkt_law_closure_prob[OF T0 L]])
  have s\<Lambda>: "sets \<Lambda> = sets (borel_of ?PT)"
    by (rule mkt_law_closure_sets[OF L])
  obtain \<sigma> :: "nat \<Rightarrow> (real \<Rightarrow> real^'m) measure"
    where r\<sigma>: "range \<sigma> \<subseteq> mkt_path_laws k L K x0 T"
    using closure_of_sequential_limit[OF metrizable_weak_conv_path_topology
        L[unfolded mkt_law_closure_def]] by blast
  have "\<sigma> 0 \<in> mkt_path_laws k L K x0 T" using r\<sigma> by blast
  then obtain M F X acov tau
    where W: "mkt_law_witness k L K x0 T (\<sigma> 0) M F X acov tau"
    unfolding mkt_path_laws_def mem_Collect_eq by blast
  then have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding mkt_law_witness_def by blast
  have L1: "1 \<le> L"
    by (rule sufficiently_volatile_market.L_ge[OF svm])
  have Lts0: "0 \<le> L * (t - s)"
    using L1 ts by auto
  have onec: "continuous_map ?PS euclideanreal (\<lambda>_. 1 :: real)" by simp
  have qcont: "continuous_map ?PT euclideanreal ?q"
    using covariation_test_functional_cont[OF st sT tI onec,
        where c = "2 * r" and i = i] by simp
  have qmeasL: "?q \<in> borel_measurable \<Lambda>"
    using continuous_map_measurable[OF qcont]
      measurable_cong_sets[OF s\<Lambda> refl]
    by (auto simp: borel_of_euclidean)
  have q0: "\<And>f. 0 \<le> ?q f" by simp
  have qb: "\<And>f. ?q f \<le> (2 * r)\<^sup>2"
  proof -
    fix f :: "real \<Rightarrow> real^'m"
    have "?q f = \<bar>rclamp (2 * r) (f t $ i - f s $ i)\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> (2 * r)\<^sup>2"
      by (intro power_mono rclamp_bound) (use r0 in auto)
    finally show "?q f \<le> (2 * r)\<^sup>2" .
  qed
  have rc: "continuous_map ?PT ?PS ?p"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pimL: "?p \<in> \<Lambda> \<rightarrow>\<^sub>M borel_of ?PS"
    using continuous_map_measurable[OF rc]
      measurable_cong_sets[OF s\<Lambda> refl] by blast
  have pdm: "?p \<in> density \<Lambda> (\<lambda>f. ennreal (w f)) \<rightarrow>\<^sub>M borel_of ?PS" for w
    using pimL measurable_cong_sets[OF sets_density refl] by blast
  have push: "(\<integral>x. u x \<partial>(distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
        (borel_of ?PS) ?p))
      = (\<integral>f. u (?p f) * w f \<partial>\<Lambda>)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and wm: "w \<in> borel_measurable \<Lambda>" and w0: "\<And>f. 0 \<le> w f"
    for u w
  proof -
    have cmp: "(\<lambda>f. u (?p f)) \<in> borel_measurable \<Lambda>"
      using measurable_comp[OF pimL um] by (simp add: o_def)
    have "(\<integral>x. u x \<partial>(distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
          (borel_of ?PS) ?p))
        = (\<integral>f. u (?p f) \<partial>(density \<Lambda> (\<lambda>f. ennreal (w f))))"
      by (rule Bochner_Integration.integral_distr[OF pdm um])
    also have "\<dots> = (\<integral>f. u (?p f) * w f \<partial>\<Lambda>)"
      by (subst integral_density)
        (use cmp wm w0 in \<open>auto simp: mult.commute intro!: AE_I2\<close>)
    finally show ?thesis .
  qed
  have finw: "finite_measure (distr (density \<Lambda> (\<lambda>f. ennreal (w f)))
      (borel_of ?PS) ?p)"
    if wm: "w \<in> borel_measurable \<Lambda>" and w0: "\<And>f. 0 \<le> w f"
    and wb: "\<And>f. w f \<le> c" for w c
  proof (rule finite_measureI)
    let ?D = "density \<Lambda> (\<lambda>f. ennreal (w f))"
    have sp: "space (distr ?D (borel_of ?PS) ?p) = space (borel_of ?PS)"
      by simp
    have pre: "?p -` space (borel_of ?PS) \<inter> space ?D = space \<Lambda>"
      using measurable_space[OF pdm[of w]] by (auto simp: space_density)
    have "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p))
        = emeasure ?D (?p -` space (borel_of ?PS) \<inter> space ?D)"
      unfolding sp
      by (intro emeasure_distr pdm)
        (metis sets.top space_borel_of)
    also have "\<dots> = emeasure ?D (space \<Lambda>)" unfolding pre ..
    also have "\<dots> = (\<integral>\<^sup>+f. ennreal (w f) * indicator (space \<Lambda>) f \<partial>\<Lambda>)"
      by (intro emeasure_density measurable_compose[OF wm measurable_ennreal])
        auto
    also have "\<dots> \<le> (\<integral>\<^sup>+f. ennreal c \<partial>\<Lambda>)"
      by (intro nn_integral_mono)
        (auto simp: indicator_def intro: ennreal_leI wb)
    also have "\<dots> = ennreal c * emeasure \<Lambda> (space \<Lambda>)"
      by (rule nn_integral_const)
    also have "\<dots> < \<infinity>"
      using finite_measure.emeasure_eq_measure[OF finL]
      by (simp add: ennreal_mult_less_top)
    finally show "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p)) \<noteq> \<infinity>"
      by simp
  qed
  define N1 where
    "N1 = distr (density \<Lambda> (\<lambda>f. ennreal (?q f))) (borel_of ?PS) ?p"
  define N2 where
    "N2 = distr (density \<Lambda> (\<lambda>f. ennreal (L * (t - s)))) (borel_of ?PS) ?p"
  have sN1: "sets N1 = sets (borel_of ?PS)"
    and sN2: "sets N2 = sets (borel_of ?PS)"
    unfolding N1_def N2_def by simp_all
  have BN1: "B \<in> sets N1" using B sN1 by simp
  have mono: "measure N1 B \<le> measure N2 B"
  proof (rule metric_measure_mono_bounded_cts[where m = "path_metric s"])
    show "sets N1 = sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
      by (rule sN1)
    show "sets N2 = sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
      by (rule sN2)
    show "finite_measure N1"
      unfolding N1_def by (rule finw[OF qmeasL q0 qb])
    show "finite_measure N2"
      unfolding N2_def
      by (rule finw[OF borel_measurable_const _ order_refl]) (use Lts0 in auto)
    show "B \<in> sets N1" by (rule BN1)
  next
    fix h :: "(real \<Rightarrow> real^'m) \<Rightarrow> real"
    assume hc: "continuous_map ?PS euclideanreal h"
      and h0: "\<And>x. 0 \<le> h x" and h1: "\<And>x. h x \<le> 1"
    have hmeas: "h \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF hc]
      by (simp add: borel_of_euclidean)
    have e1: "(\<integral>x. h x \<partial>N1) = (\<integral>f. h (?p f) * ?q f \<partial>\<Lambda>)"
      unfolding N1_def by (rule push[OF hmeas qmeasL q0])
    have e2: "(\<integral>x. h x \<partial>N2) = (\<integral>f. h (?p f) * (L * (t - s)) \<partial>\<Lambda>)"
      unfolding N2_def
      by (rule push[OF hmeas borel_measurable_const Lts0])
    have "(\<integral>f. h (?p f) * ?q f \<partial>\<Lambda>) = (\<integral>f. ?q f * h (?p f) \<partial>\<Lambda>)"
      by (simp add: mult.commute)
    also have "\<dots> \<le> L * (t - s) * (\<integral>f. h (?p f) \<partial>\<Lambda>)"
      by (rule mkt_law_closure_covariation_test[OF T0 Kball r0 L st ts tT
          hc h0 h1])
    also have "\<dots> = (\<integral>f. h (?p f) * (L * (t - s)) \<partial>\<Lambda>)"
      by (simp add: mult.commute)
    finally show "(\<integral>x. h x \<partial>N1) \<le> (\<integral>x. h x \<partial>N2)"
      using e1 e2 by simp
  qed
  have iB: "indicat_real B \<in> borel_measurable (borel_of ?PS)"
    using B by (rule borel_measurable_indicator)
  have m1: "measure N1 B = (\<integral>f. indicat_real B (?p f) * ?q f \<partial>\<Lambda>)"
  proof -
    have "measure N1 B = (\<integral>x. indicat_real B x \<partial>N1)"
      using BN1 by simp
    also have "\<dots> = (\<integral>f. indicat_real B (?p f) * ?q f \<partial>\<Lambda>)"
      unfolding N1_def by (rule push[OF iB qmeasL q0])
    finally show ?thesis .
  qed
  have m2: "measure N2 B
      = L * (t - s) * (\<integral>f. indicat_real B (?p f) \<partial>\<Lambda>)"
  proof -
    have "measure N2 B = (\<integral>x. indicat_real B x \<partial>N2)"
      using B sN2 by simp
    also have "\<dots> = (\<integral>f. indicat_real B (?p f) * (L * (t - s)) \<partial>\<Lambda>)"
      unfolding N2_def
      by (rule push[OF iB borel_measurable_const Lts0])
    also have "\<dots> = L * (t - s) * (\<integral>f. indicat_real B (?p f) \<partial>\<Lambda>)"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have "(\<integral>f. ?q f * indicat_real B (?p f) \<partial>\<Lambda>)
      = (\<integral>f. indicat_real B (?p f) * ?q f \<partial>\<Lambda>)"
    by (simp add: mult.commute)
  also have "\<dots> \<le> L * (t - s) * (\<integral>f. indicat_real B (?p f) \<partial>\<Lambda>)"
    using mono m1 m2 by simp
  finally show ?thesis .
qed

text \<open>For a CLOSED confinement set the clamp is invisible: closure laws are
  supported on confined paths, so the RAW coordinate increments satisfy
  the martingale identity and the covariation bound against every past
  event.  These are the two integrated inputs of the canonical-market
  construction, in their final form.\<close>

corollary mkt_law_closure_increment_event:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes T0: "0 \<le> T" and Kcl: "closed K" and Kball: "K \<subseteq> cball 0 r"
    and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
  shows "(\<integral>f. (f t $ i - f s $ i)
      * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>) = 0"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  let ?PS = "mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)"
  have sT: "s \<le> T" and t0: "0 \<le> t" using st ts tT by linarith+
  have sI: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using st ts tT by auto
  have s\<Lambda>: "sets \<Lambda> = sets (borel_of ?PT)"
    by (rule mkt_law_closure_sets[OF L])
  have ae: "AE f in \<Lambda>. rclamp (2 * r) (f t $ i - f s $ i)
      = f t $ i - f s $ i"
    using mkt_law_closure_confined_AE[OF T0 Kcl L]
  proof eventually_elim
    case (elim f)
    have ftK: "f t \<in> K" using elim tI by blast
    have fsK: "f s \<in> K" using elim sI by blast
    have nt: "norm (f t) \<le> r"
      using ftK Kball by (auto simp: dist_norm)
    have ns: "norm (f s) \<le> r"
      using fsK Kball by (auto simp: dist_norm)
    have "\<bar>f t $ i - f s $ i\<bar> \<le> \<bar>f t $ i\<bar> + \<bar>f s $ i\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> norm (f t) + norm (f s)"
      by (intro add_mono component_le_norm_cart)
    also have "\<dots> \<le> 2 * r" using nt ns by linarith
    finally show ?case by (rule rclamp_id)
  qed
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have inc_cont: "continuous_map ?PT euclideanreal
      (\<lambda>f. f t $ i - f s $ i)"
    using continuous_map_compose[OF evdiff cmp_i]
    by (simp add: o_def vector_minus_component)
  have incM: "(\<lambda>f. f t $ i - f s $ i) \<in> borel_measurable \<Lambda>"
    using continuous_map_measurable[OF inc_cont]
      measurable_cong_sets[OF s\<Lambda> refl]
    by (auto simp: borel_of_euclidean)
  have rcM: "(\<lambda>f. rclamp (2 * r) (f t $ i - f s $ i))
      \<in> borel_measurable \<Lambda>"
  proof -
    have "continuous_on UNIV (rclamp (2 * r))"
      using rclamp_cont[of "2 * r"]
      by (simp add: continuous_map_iff_continuous2)
    then show ?thesis
      by (intro measurable_compose[OF incM
          borel_measurable_continuous_onI])
  qed
  have rc: "continuous_map ?PT ?PS (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pimL: "(\<lambda>f. restrict f {0..s}) \<in> \<Lambda> \<rightarrow>\<^sub>M borel_of ?PS"
    using continuous_map_measurable[OF rc]
      measurable_cong_sets[OF s\<Lambda> refl] by blast
  have iB: "indicat_real B \<in> borel_measurable (borel_of ?PS)"
    using B by (rule borel_measurable_indicator)
  have indM: "(\<lambda>f. indicat_real B (restrict f {0..s}))
      \<in> borel_measurable \<Lambda>"
    using measurable_comp[OF pimL iB] by (simp add: o_def)
  have "(\<integral>f. (f t $ i - f s $ i)
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)
      = (\<integral>f. rclamp (2 * r) (f t $ i - f s $ i)
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)"
  proof (rule integral_cong_AE)
    show "(\<lambda>f. (f t $ i - f s $ i)
        * indicat_real B (restrict f {0..s})) \<in> borel_measurable \<Lambda>"
      by (intro borel_measurable_times incM indM)
    show "(\<lambda>f. rclamp (2 * r) (f t $ i - f s $ i)
        * indicat_real B (restrict f {0..s})) \<in> borel_measurable \<Lambda>"
      by (intro borel_measurable_times rcM indM)
    show "AE f in \<Lambda>. (f t $ i - f s $ i)
        * indicat_real B (restrict f {0..s})
        = rclamp (2 * r) (f t $ i - f s $ i)
          * indicat_real B (restrict f {0..s})"
      using ae by eventually_elim simp
  qed
  also have "\<dots> = 0"
    by (rule mkt_law_closure_martingale_event[OF T0 Kball r0 L st ts tT B])
  finally show ?thesis .
qed

corollary mkt_law_closure_sq_increment_event:
  fixes \<Lambda> :: "(real \<Rightarrow> real^'m::finite) measure" and r :: real
  assumes T0: "0 \<le> T" and Kcl: "closed K" and Kball: "K \<subseteq> cball 0 r"
    and r0: "0 \<le> r"
    and L: "\<Lambda> \<in> mkt_law_closure k L K x0 T"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)))"
  shows "(\<integral>f. (f t $ i - f s $ i)\<^sup>2
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)
      \<le> L * (t - s) * (\<integral>f. indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  let ?PS = "mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric)"
  have sT: "s \<le> T" and t0: "0 \<le> t" using st ts tT by linarith+
  have sI: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using st ts tT by auto
  have s\<Lambda>: "sets \<Lambda> = sets (borel_of ?PT)"
    by (rule mkt_law_closure_sets[OF L])
  have ae: "AE f in \<Lambda>. rclamp (2 * r) (f t $ i - f s $ i)
      = f t $ i - f s $ i"
    using mkt_law_closure_confined_AE[OF T0 Kcl L]
  proof eventually_elim
    case (elim f)
    have ftK: "f t \<in> K" using elim tI by blast
    have fsK: "f s \<in> K" using elim sI by blast
    have nt: "norm (f t) \<le> r"
      using ftK Kball by (auto simp: dist_norm)
    have ns: "norm (f s) \<le> r"
      using fsK Kball by (auto simp: dist_norm)
    have "\<bar>f t $ i - f s $ i\<bar> \<le> \<bar>f t $ i\<bar> + \<bar>f s $ i\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> norm (f t) + norm (f s)"
      by (intro add_mono component_le_norm_cart)
    also have "\<dots> \<le> 2 * r" using nt ns by linarith
    finally show ?case by (rule rclamp_id)
  qed
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have inc_cont: "continuous_map ?PT euclideanreal
      (\<lambda>f. f t $ i - f s $ i)"
    using continuous_map_compose[OF evdiff cmp_i]
    by (simp add: o_def vector_minus_component)
  have incM: "(\<lambda>f. f t $ i - f s $ i) \<in> borel_measurable \<Lambda>"
    using continuous_map_measurable[OF inc_cont]
      measurable_cong_sets[OF s\<Lambda> refl]
    by (auto simp: borel_of_euclidean)
  have rcM: "(\<lambda>f. rclamp (2 * r) (f t $ i - f s $ i))
      \<in> borel_measurable \<Lambda>"
  proof -
    have "continuous_on UNIV (rclamp (2 * r))"
      using rclamp_cont[of "2 * r"]
      by (simp add: continuous_map_iff_continuous2)
    then show ?thesis
      by (intro measurable_compose[OF incM
          borel_measurable_continuous_onI])
  qed
  have rc: "continuous_map ?PT ?PS (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pimL: "(\<lambda>f. restrict f {0..s}) \<in> \<Lambda> \<rightarrow>\<^sub>M borel_of ?PS"
    using continuous_map_measurable[OF rc]
      measurable_cong_sets[OF s\<Lambda> refl] by blast
  have iB: "indicat_real B \<in> borel_measurable (borel_of ?PS)"
    using B by (rule borel_measurable_indicator)
  have indM: "(\<lambda>f. indicat_real B (restrict f {0..s}))
      \<in> borel_measurable \<Lambda>"
    using measurable_comp[OF pimL iB] by (simp add: o_def)
  have "(\<integral>f. (f t $ i - f s $ i)\<^sup>2
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)
      = (\<integral>f. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
        * indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)"
  proof (rule integral_cong_AE)
    show "(\<lambda>f. (f t $ i - f s $ i)\<^sup>2
        * indicat_real B (restrict f {0..s})) \<in> borel_measurable \<Lambda>"
      by (intro borel_measurable_times borel_measurable_power incM indM)
    show "(\<lambda>f. (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
        * indicat_real B (restrict f {0..s})) \<in> borel_measurable \<Lambda>"
      by (intro borel_measurable_times borel_measurable_power rcM indM)
    show "AE f in \<Lambda>. (f t $ i - f s $ i)\<^sup>2
        * indicat_real B (restrict f {0..s})
        = (rclamp (2 * r) (f t $ i - f s $ i))\<^sup>2
          * indicat_real B (restrict f {0..s})"
      using ae by eventually_elim simp
  qed
  also have "\<dots> \<le> L * (t - s)
      * (\<integral>f. indicat_real B (restrict f {0..s}) \<partial>\<Lambda>)"
    by (rule mkt_law_closure_covariation_event[OF T0 Kball r0 L st ts tT B])
  finally show ?thesis .
qed

subsection \<open>Clause (1) of Theorem 1.1, law-level form\<close>

text \<open>The consolidation of Section 2: on a confinement set
  \<open>K \<subseteq> cball 0 r\<close>, the paper-class value function \<open>stopped_val_fn\<close> is
  dominated by the law-level value function
  \<open>w x = Sup (vshift T A x ` mkt_law_closure k L (cball 0 (2r)) 0 T)\<close>,
  and \<open>w\<close> is upper semicontinuous in the starting point --- with a
  horizon that is UNIFORM over \<open>K\<close>, namely any
  \<open>T \<ge> r\<^sup>2 / (n - k)\<close>, the exit-time bound of Lemma 2.1 at the origin.
  This is clause (1) of Theorem 1.1 in its law-level form; identifying
  \<open>w\<close> with the class supremum ("the closure adds no value") is the
  canonical-market construction, whose integrated inputs are
  \<open>mkt_law_closure_increment_event\<close> and
  \<open>mkt_law_closure_sq_increment_event\<close>.\<close>

lemma ball_v_le:
  fixes x :: "real^'n::finite"
  shows "ball_v r k x \<le> r\<^sup>2 / real (CARD('n) - k)"
  unfolding ball_v_def
  by (intro divide_right_mono) (auto simp: dot_square_norm)

theorem clause_one_law_level:
  fixes K :: "(real^'m::finite) set" and A :: "(real^'m) set"
    and T r :: real and k :: nat and L :: real
  defines "w \<equiv> (\<lambda>x :: real^'m.
      Sup (vshift T A x ` mkt_law_closure k L (cball 0 (2 * r)) 0 T))"
  assumes k: "1 \<le> k" "k < CARD('m)" and L1: "1 \<le> L"
    and r0: "0 \<le> r" and Kball: "K \<subseteq> cball 0 r"
    and A: "open A" and AK: "A \<inter> K = {}"
    and T0: "0 \<le> T" and bT: "r\<^sup>2 / real (CARD('m) - k) \<le> T"
  shows clause_one_usc:
    "\<And>x c. w x < c \<Longrightarrow> eventually (\<lambda>y. w y < c) (nhds x)"
  and clause_one_dom:
    "\<And>x. x \<in> K \<Longrightarrow> stopped_val_fn k L K x \<le> ennreal (w x)"
proof -
  have ne: "mkt_path_laws k L (cball 0 (2 * r)) (0 :: real^'m) T \<noteq> {}"
    by (rule mkt_path_laws_nonempty[OF k L1]) (use r0 in simp)
  show "eventually (\<lambda>y. w y < c) (nhds x)" if lt: "w x < c" for x c
    using lt unfolding w_def
    by (rule vshift_sup_usc_mkt[OF T0 A ne subset_refl])
  show "stopped_val_fn k L K x \<le> ennreal (w x)" if xK: "x \<in> K" for x
    unfolding w_def
  proof (rule stopped_val_fn_le_law_sup[OF Kball xK A AK T0])
    show "ball_v r k x \<le> T"
      by (rule order_trans[OF ball_v_le bT])
  qed
qed

subsection \<open>Clauses (0) and (3, ball) for the paper-class value function\<close>

text \<open>The bare-locale facts transfer to \<open>stopped_val_fn\<close> by the index
  inclusion: finiteness on bounded confinement sets (clause (0)), the
  Lemma 2.1 upper bound on the ball, and the zero boundary values on the
  sphere (clause (3) for the ball).\<close>

lemma stopped_val_fn_finite_bounded:
  fixes K :: "(real^'m::finite) set" and x0 :: "real^'m"
  assumes B: "bounded K"
  shows "stopped_val_fn k L K x0 < \<top>"
  using stopped_val_fn_le_val_fn val_fn_finite_bounded[OF B]
  by (rule le_less_trans)

lemma stopped_val_fn_le_ball_v:
  fixes x0 :: "real^'m::finite"
  shows "stopped_val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
  using stopped_val_fn_le_val_fn val_fn_le_ball_v
  by (rule order_trans)

lemma stopped_val_fn_boundary_zero:
  fixes x0 :: "real^'m::finite"
  assumes x0: "norm x0 = r"
  shows "stopped_val_fn k L (cball 0 r) x0 = 0"
proof -
  have "stopped_val_fn k L (cball 0 r) x0 \<le> val_fn k L (cball 0 r) x0"
    by (rule stopped_val_fn_le_val_fn)
  also have "\<dots> = 0" by (rule val_fn_boundary_zero[OF x0])
  finally show ?thesis by simp
qed

end
