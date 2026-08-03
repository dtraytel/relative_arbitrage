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

end
