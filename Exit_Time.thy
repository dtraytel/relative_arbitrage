(*
  Title:   Exit_Time.thy
  Content: The exit time of a closed set by a continuous adapted process is a
           stopping time, and up to it the process stays in the closed ball.
           This is the structural ingredient of Example 3.1 of the paper: the
           horizon there is the first exit time of a ball, and the results of
           Ito_Market ask for a stopping time whose stopped process stays in K.

  Everything here is about an arbitrary adapted process with continuous
  paths; nothing is Brownian-specific.
*)

theory Exit_Time
  imports Ito_Market
begin

section \<open>The capped exit time\<close>

text \<open>The first time in \<open>[0,T]\<close> at which the process is in \<open>A\<close>, capped at
  the horizon \<open>T\<close>.  Capping keeps the time real-valued and bounded, which is
  what the market locales need.\<close>

definition etime ::
  "real \<Rightarrow> 'b set \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> real" where
  "etime T A X \<omega> = Inf ({r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T})"

lemma etime_bdd_below:
  assumes T: "0 \<le> T"
  shows "bdd_below ({r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T})"
  using T by (intro bdd_belowI[of _ 0]) auto

lemma etime_le_T:
  assumes T: "0 \<le> T"
  shows "etime T A X \<omega> \<le> T"
  unfolding etime_def
  using etime_bdd_below[OF T] by (intro cInf_lower) auto

lemma etime_nonneg:
  assumes T: "0 \<le> T"
  shows "0 \<le> etime T A X \<omega>"
  unfolding etime_def
  using T by (intro cInf_greatest) auto

lemma etime_le_of_mem:
  assumes T: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" and mem: "X r \<omega> \<in> A"
  shows "etime T A X \<omega> \<le> r"
  unfolding etime_def
  using etime_bdd_below[OF T] r mem by (intro cInf_lower) auto

text \<open>The STRICT characterisation, which is the handle upper semicontinuity of
  the exit time needs.  Larsson--Ruf's Lemma 2.1 argues: if \<open>\<omega>\<^sub>n \<rightarrow> \<omega>\<close> and
  \<open>\<omega>(\<tau>(\<omega>)+\<epsilon>) \<notin> K\<close>, then \<open>\<omega>\<^sub>n(\<tau>(\<omega>)+\<epsilon>) \<notin> K\<close> for large \<open>n\<close>, so \<open>\<tau>(\<omega>\<^sub>n) \<le> \<tau>(\<omega>)+\<epsilon>\<close>.
  Unwound, that is exactly this: being strictly below \<open>c\<close> is WITNESSED, by a
  single time \<open>r < c\<close> at which the path is already in \<open>A\<close>.  Since \<open>A\<close> is open
  (it is the complement of the compact \<open>K\<close>) the witness survives small
  perturbations of the path at that one time, which is what makes the sublevel
  set \<open>{\<omega> : \<tau>(\<omega>) < c}\<close> open.

  Note the disjunct \<open>T < c\<close>: the infimum is over the hitting times TOGETHER with
  the cap \<open>T\<close>, so a path that never reaches \<open>A\<close> still has exit time \<open>T\<close>, and that
  branch is independent of \<open>\<omega>\<close> altogether.\<close>

lemma etime_less_iff:
  assumes T: "0 \<le> T"
  shows "etime T A X \<omega> < c
      \<longleftrightarrow> ((\<exists>r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A \<and> r < c) \<or> T < c)"
proof -
  have ne: "({r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T}) \<noteq> {}" by blast
  have bd: "bdd_below ({r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T})"
    by (rule etime_bdd_below[OF T])
  have "etime T A X \<omega> < c
      \<longleftrightarrow> (\<exists>x \<in> {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T}. x < c)"
    unfolding etime_def by (rule cInf_less_iff[OF ne bd])
  also have "\<dots> \<longleftrightarrow> ((\<exists>r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A \<and> r < c) \<or> T < c)"
    by blast
  finally show ?thesis .
qed

text \<open>And the perturbation step it powers: an OPEN \<open>A\<close> already entered at some
  \<open>r < c\<close> keeps the exit time below \<open>c\<close> for every path agreeing closely enough
  with \<open>\<omega>\<close> at that single time \<open>r\<close>.\<close>

lemma etime_less_of_open_witness:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes T: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" "r < c"
    and mem: "X r \<omega>' \<in> A"
  shows "etime T A X \<omega>' < c"
  unfolding etime_less_iff[OF T] using r mem by blast

subsection \<open>An open erosion of \<open>A\<close>: the uniformity device for item 2.4\<close>

text \<open>Item 2.4 of the Theorem 1.1 plan needs joint upper semicontinuity of
  \<open>f(x,P) = ((x+\<cdot>)\<^sub>*P)-essinf \<tau>\<^sub>K\<close>, where BOTH the shift \<open>x\<close> and the measure \<open>P\<close>
  vary.  Unfolding, \<open>f(x,P) < d\<close> says \<open>P{\<omega> : \<tau>\<^sub>K(x+\<omega>) < d} > 0\<close>, and by
  \<open>etime_less_iff\<close> that event is witnessed at a single time \<open>r\<close> by
  \<open>x + \<omega>(r) \<in> A\<close> with \<open>A\<close> open.

  The obstruction is uniformity: each \<open>\<omega>\<close> has its own room to move \<open>x\<close>, and a
  pointwise \<open>\<epsilon>(\<omega>)\<close> is useless against a measure.  The fix is to erode \<open>A\<close>: the
  sets \<open>{z. d < infdist z (-A)}\<close> are OPEN, increase to \<open>A\<close> as \<open>d \<downarrow> 0\<close>, and give a
  margin \<open>d\<close> that does NOT depend on \<open>\<omega>\<close>.  Choosing \<open>d\<close> so the eroded event still
  has positive mass makes the shift-perturbation uniform, and the eroded event
  being open is then exactly what the open-set form of Portmanteau
  (\<open>liminf Q\<^sub>m(G) \<ge> Q(G)\<close>) needs to keep the mass positive as the measure moves.

  These two lemmas are that device.  Note \<open>shift_stays_off\<close> needs no closedness
  and no completeness: if \<open>w\<close> were in \<open>S\<close> then \<open>infdist z S \<le> dist z w < d\<close>,
  contradicting the margin outright.\<close>

lemma open_gt_infdist: "open {z. d < infdist z S}"
proof -
  have "continuous_on UNIV (\<lambda>z. infdist z S)"
    by (intro continuous_intros)
  then show ?thesis
    by (rule open_Collect_less[OF continuous_on_const])
qed

lemma shift_stays_off:
  fixes z w :: "'b :: metric_space"
  assumes marg: "d < infdist z S" and near: "dist z w < d"
  shows "w \<notin> S"
proof
  assume wS: "w \<in> S"
  have "infdist z S \<le> dist z w" by (rule infdist_le[OF wS])
  with near marg show False by linarith
qed

subsection \<open>The erosion operator\<close>

text \<open>The two lemmas above are packaged here as a single operator, because the
  uniformity argument uses all three of its properties together and getting them
  from \<open>infdist\<close> afresh at each use is where the ``margin depends on \<open>\<omega>\<close>'' mistake
  creeps back in.

  The \<open>A = UNIV\<close> case has to be split off and is NOT bookkeeping. Isabelle's
  \<open>infdist z {} = 0\<close>, so the naive \<open>{z. \<delta> < infdist z (- A)}\<close> would be EMPTY exactly
  when \<open>A\<close> is everything --- the one case where no erosion is needed at all. With
  the split, \<open>eroded\<close> satisfies its three laws unconditionally.\<close>

definition eroded :: "real \<Rightarrow> 'b::metric_space set \<Rightarrow> 'b set" where
  "eroded d A = (if A = UNIV then UNIV else {z. d < infdist z (- A)})"

lemma open_eroded: "open (eroded d A)"
  unfolding eroded_def by (simp add: open_gt_infdist)

lemma eroded_subset:
  assumes d: "0 \<le> d"
  shows "eroded d A \<subseteq> A"
proof (cases "A = UNIV")
  case True thus ?thesis by simp
next
  case False
  have "z \<in> A" if z: "d < infdist z (- A)" for z
  proof (rule ccontr)
    assume "z \<notin> A"
    hence "z \<in> - A" by simp
    hence "infdist z (- A) = 0" by simp
    with z d show False by linarith
  qed
  thus ?thesis using False unfolding eroded_def by auto
qed

text \<open>The uniform-margin property: membership in \<open>eroded d A\<close> buys a shift budget
  \<open>d\<close> that is the SAME for every point of the eroded set.\<close>

lemma eroded_shift:
  fixes z w :: "'b::metric_space"
  assumes z: "z \<in> eroded d A" and near: "dist z w < d"
  shows "w \<in> A"
proof (cases "A = UNIV")
  case True thus ?thesis by simp
next
  case False
  have "d < infdist z (- A)" using z False unfolding eroded_def by simp
  from shift_stays_off[OF this near] show ?thesis by simp
qed

lemma eroded_mono:
  assumes "d' \<le> d"
  shows "eroded d A \<subseteq> eroded d' A"
  using assms unfolding eroded_def by auto

text \<open>The erosions exhaust an open set. This is the half that fails for general
  \<open>A\<close>: a point of \<open>A\<close> needs interior room before any positive margin exists.\<close>

lemma eroded_exhausts:
  fixes A :: "'b::metric_space set"
  assumes A: "open A"
  shows "(\<Union>n. eroded (1 / Suc n) A) = A"
proof
  show "(\<Union>n. eroded (1 / Suc n) A) \<subseteq> A"
  proof
    fix z assume "z \<in> (\<Union>n. eroded (1 / Suc n) A)"
    then obtain n where zn: "z \<in> eroded (1 / Suc n) A" by blast
    have "(0::real) \<le> 1 / Suc n" by simp
    from eroded_subset[OF this] zn show "z \<in> A" by blast
  qed
next
  show "A \<subseteq> (\<Union>n. eroded (1 / Suc n) A)"
  proof (cases "A = UNIV")
    case True thus ?thesis unfolding eroded_def by auto
  next
    case False
    have "z \<in> (\<Union>n. eroded (1 / Suc n) A)" if zA: "z \<in> A" for z
    proof -
      obtain e :: real where e: "0 < e" and ball: "ball z e \<subseteq> A"
        using A zA unfolding open_contains_ball by blast
      have far: "e \<le> dist z w" if w: "w \<in> - A" for w
      proof (rule ccontr)
        assume "\<not> e \<le> dist z w"
        hence "w \<in> ball z e" by simp
        with ball w show False by blast
      qed
      have neA: "- A \<noteq> {}" using False by auto
      have "e \<le> infdist z (- A)"
        unfolding infdist_notempty[OF neA]
        by (intro cINF_greatest[OF neA] far)
      moreover obtain n :: nat where n: "1 / Suc n < e"
        using e nat_approx_posE by blast
      ultimately have "1 / Suc n < infdist z (- A)" by linarith
      hence "z \<in> eroded (1 / Suc n) A" using False unfolding eroded_def by simp
      thus ?thesis by blast
    qed
    thus ?thesis by blast
  qed
qed

text \<open>The measure-theoretic companion to \<open>eroded_exhausts\<close> is deferred to just
  after \<open>positive_of_countable_UN\<close> below, which it uses.\<close>

text \<open>With closed \<open>A\<close> and continuous paths the infimum is attained, so the
  exit time is at most \<open>t\<close> exactly when the process visits \<open>A\<close> before
  \<open>t\<close>.\<close>

lemma etime_le_iff:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes T: "0 \<le> T" and t: "0 \<le> t" and tT: "t < T"
    and A: "closed A"
    and cont: "continuous_on {0..T} (\<lambda>s. X s \<omega>)"
  shows "etime T A X \<omega> \<le> t \<longleftrightarrow> (\<exists>r\<in>{0..t}. X r \<omega> \<in> A)"
proof
  have S_closed: "closed {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}"
  proof -
    have "{r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}
        = (\<lambda>r. X r \<omega>) -` A \<inter> {0..T}"
      by auto
    then show ?thesis
      using cont A by (simp add: continuous_on_closed_vimage)
  qed
  have S_bdd: "bdd_below {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}"
    by (intro bdd_belowI[of _ 0]) auto
  assume le: "etime T A X \<omega> \<le> t"
  have S_ne: "{r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<noteq> {}"
    then have empty: "{r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} = {}"
      by simp
    have "etime T A X \<omega> = T"
      unfolding etime_def empty by simp
    with le tT show False by simp
  qed
  have Inf_le: "Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<le> t"
  proof (rule ccontr)
    assume "\<not> Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<le> t"
    then have gt: "t < Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}"
      by simp
    have "min (Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}) T \<le> etime T A X \<omega>"
      unfolding etime_def
    proof (intro cInf_greatest)
      show "{r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T} \<noteq> {}"
        by auto
      fix x assume xin: "x \<in> {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<union> {T}"
      show "min (Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}) T \<le> x"
      proof (cases "x = T")
        case True
        then show ?thesis by simp
      next
        case False
        with xin have "x \<in> {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}"
          by simp
        then have "Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A} \<le> x"
          using S_bdd by (intro cInf_lower)
        then show ?thesis by simp
      qed
    qed
    with le gt tT show False by simp
  qed
  have "Inf {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}
      \<in> {r. 0 \<le> r \<and> r \<le> T \<and> X r \<omega> \<in> A}"
    using S_ne S_bdd S_closed by (intro closed_contains_Inf) auto
  then show "\<exists>r\<in>{0..t}. X r \<omega> \<in> A"
    using Inf_le by auto
next
  assume "\<exists>r\<in>{0..t}. X r \<omega> \<in> A"
  then obtain r where r: "0 \<le> r" "r \<le> t" and mem: "X r \<omega> \<in> A" by auto
  have "etime T A X \<omega> \<le> r"
    using T r tT mem by (intro etime_le_of_mem) auto
  with r show "etime T A X \<omega> \<le> t" by simp
qed

section \<open>A countable description of the hitting event\<close>

text \<open>The event that the process visits the closed set \<open>A\<close> before time \<open>t\<close>
  is a countable combination of events at rational times: continuity gives
  one inclusion, and attainment of the infimum of the (continuous) distance
  to \<open>A\<close> on the compact interval gives the other.\<close>

text \<open>The countable reduction step of item 2.4.  Unfolding \<open>f(x,P) < d\<close> gives
  \<open>P(\<Union>\<^bsub>r\<^esub> H\<^sub>r) > 0\<close> over the witness times \<open>r\<close>, but the erosion argument needs a
  SINGLE \<open>r\<close> with \<open>P(H\<^sub>r) > 0\<close>.  That is exactly the contrapositive of "a
  countable union of null sets is null", which is why the reduction to
  \<open>qtimes\<close> (via \<open>hit_iff_qtimes\<close> below) has to happen first: over an uncountable
  index set the step is FALSE.\<close>

lemma positive_of_countable_UN:
  assumes cR: "countable R"
    and meas: "\<And>r. r \<in> R \<Longrightarrow> H r \<in> sets M"
    and pos: "emeasure M (\<Union>r\<in>R. H r) \<noteq> 0"
  shows "\<exists>r \<in> R. emeasure M (H r) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>r \<in> R. emeasure M (H r) \<noteq> 0)"
  then have z: "\<And>r. r \<in> R \<Longrightarrow> H r \<in> null_sets M"
    using meas by (simp add: null_sets_def)
  have "(\<Union>r\<in>R. H r) \<in> null_sets M"
    by (rule null_sets_UN'[OF cR z])
  then have "emeasure M (\<Union>r\<in>R. H r) = 0"
    by (simp add: null_sets_def)
  with pos show False by simp
qed

text \<open>The measure-theoretic companion to \<open>eroded_exhausts\<close>. This is the step
  that converts ``\<open>A\<close> has positive mass'' into ``SOME erosion of \<open>A\<close> still has
  positive mass'' --- i.e. it buys a shift margin that is uniform over the whole
  sample space, at the cost of an unspecified level. Countability of the
  exhausting family is exactly what makes it work: over an uncountable family
  the step is false, since an uncountable union of null sets need not be null.\<close>

lemma positive_mass_at_some_erosion:
  fixes A :: "'b::metric_space set"
  assumes A: "open A"
    and meas: "\<And>n::nat. {\<omega> \<in> space M. Y \<omega> \<in> eroded (1 / Suc n) A} \<in> sets M"
    and pos: "emeasure M {\<omega> \<in> space M. Y \<omega> \<in> A} \<noteq> 0"
  shows "\<exists>n::nat. emeasure M {\<omega> \<in> space M. Y \<omega> \<in> eroded (1 / Suc n) A} \<noteq> 0"
proof -
  have "{\<omega> \<in> space M. Y \<omega> \<in> A}
      = (\<Union>n \<in> (UNIV :: nat set). {\<omega> \<in> space M. Y \<omega> \<in> eroded (1 / Suc n) A})"
    using eroded_exhausts[OF A] by blast
  with pos have un: "emeasure M
      (\<Union>n \<in> (UNIV :: nat set). {\<omega> \<in> space M. Y \<omega> \<in> eroded (1 / Suc n) A}) \<noteq> 0"
    by simp
  have cU: "countable (UNIV :: nat set)" by simp
  have "\<exists>n \<in> (UNIV :: nat set).
      emeasure M {\<omega> \<in> space M. Y \<omega> \<in> eroded (1 / Suc n) A} \<noteq> 0"
    by (rule positive_of_countable_UN[OF cU _ un]) (use meas in blast)
  thus ?thesis by blast
qed

definition qtimes :: "real \<Rightarrow> real set" where
  "qtimes t = insert t {q \<in> {0..t}. q \<in> \<rat>}"

lemma countable_qtimes: "countable (qtimes t)"
proof -
  have "{q \<in> {0..t}. q \<in> \<rat>} \<subseteq> \<rat>"
    by auto
  then have "countable {q \<in> {0..t}. q \<in> \<rat>}"
    using countable_rat by (rule countable_subset)
  then show ?thesis
    unfolding qtimes_def by simp
qed

lemma qtimes_subset: "0 \<le> t \<Longrightarrow> qtimes t \<subseteq> {0..t}"
  unfolding qtimes_def by auto

lemma qtimes_dense:
  assumes t: "0 \<le> t" and r: "r \<in> {0..t}" and d: "0 < d"
  shows "\<exists>q\<in>qtimes t. \<bar>q - r\<bar> < d"
proof (cases "r = t")
  case True
  then show ?thesis
    using d by (intro bexI[of _ t]) (auto simp: qtimes_def)
next
  case False
  with r have rt: "r < t" by auto
  have "max 0 (r - d) < min t (r + d)"
    using r d rt by auto
  then obtain q where q: "q \<in> \<rat>" "max 0 (r - d) < q" "q < min t (r + d)"
    using Rats_dense_in_real by blast
  then show ?thesis
    unfolding qtimes_def using r by (intro bexI[of _ q]) auto
qed

lemma hit_iff_qtimes:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes t: "0 \<le> t" and A: "closed A" "A \<noteq> {}"
    and cont: "continuous_on {0..t} (\<lambda>s. X s \<omega>)"
  shows "(\<exists>r\<in>{0..t}. X r \<omega> \<in> A)
     \<longleftrightarrow> (\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m))"
proof
  assume "\<exists>r\<in>{0..t}. X r \<omega> \<in> A"
  then obtain r where r: "r \<in> {0..t}" and mem: "X r \<omega> \<in> A" by auto
  show "\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m)"
  proof
    fix m :: nat
    have e: "0 < 1 / real (Suc m)" by simp
    have "continuous (at r within {0..t}) (\<lambda>s. X s \<omega>)"
      using cont r by (simp add: continuous_on_eq_continuous_within)
    then obtain d where d: "0 < d"
      and near: "\<And>s. s \<in> {0..t} \<Longrightarrow> dist s r < d
        \<Longrightarrow> dist (X s \<omega>) (X r \<omega>) < 1 / real (Suc m)"
      using e unfolding continuous_within_eps_delta by blast
    obtain q where q: "q \<in> qtimes t" and qr: "\<bar>q - r\<bar> < d"
      using qtimes_dense[OF t r d] by blast
    have qt: "q \<in> {0..t}"
      using q qtimes_subset[OF t] by blast
    have "infdist (X q \<omega>) A \<le> dist (X q \<omega>) (X r \<omega>)"
      using mem by (intro infdist_le)
    also have "\<dots> < 1 / real (Suc m)"
      using near[OF qt] qr by (simp add: dist_real_def)
    finally show "\<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m)"
      using q by blast
  qed
next
  assume approx: "\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m)"
  have f_cont: "continuous_on {0..t} (\<lambda>s. infdist (X s \<omega>) A)"
    using cont by (intro continuous_on_infdist) auto
  have ne: "{0..t} \<noteq> {}"
    using t by simp
  obtain r where r: "r \<in> {0..t}"
    and least: "\<And>s. s \<in> {0..t} \<Longrightarrow> infdist (X r \<omega>) A \<le> infdist (X s \<omega>) A"
    using continuous_attains_inf[OF compact_Icc ne f_cont] by blast
  have "infdist (X r \<omega>) A = 0"
  proof (rule ccontr)
    assume "infdist (X r \<omega>) A \<noteq> 0"
    with infdist_nonneg have pos: "0 < infdist (X r \<omega>) A"
      by (simp add: order_less_le)
    obtain m :: nat where m: "1 / real (Suc m) < infdist (X r \<omega>) A"
      using pos by (metis nat_approx_posE)
    obtain q where q: "q \<in> qtimes t"
      and qlt: "infdist (X q \<omega>) A < 1 / real (Suc m)"
      using approx by blast
    have "q \<in> {0..t}"
      using q qtimes_subset[OF t] by blast
    then have "infdist (X r \<omega>) A \<le> infdist (X q \<omega>) A"
      by (rule least)
    with qlt m show False by simp
  qed
  then have "X r \<omega> \<in> A"
    using A by (simp add: in_closed_iff_infdist_zero)
  with r show "\<exists>r\<in>{0..t}. X r \<omega> \<in> A" by blast
qed

section \<open>The exit time is a stopping time\<close>

locale cont_adapted_process = adapted_process M F "0 :: real" X
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}" +
  fixes T :: real
  assumes T_nonneg: "0 \<le> T"
    and paths_cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>s. X s \<omega>)"
begin

lemma infdist_measurable:
  assumes r: "0 \<le> r" and rt: "r \<le> t" and A: "closed A" "A \<noteq> {}"
  shows "{\<omega> \<in> space M. infdist (X r \<omega>) A < e} \<in> sets (F t)"
proof -
  have Xr: "X r \<in> borel_measurable (F t)"
    using r rt by (intro adaptedD) auto
  have "(\<lambda>y. infdist y A) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_on_infdist
        continuous_on_id)
  then have meas: "(\<lambda>\<omega>. infdist (X r \<omega>) A) \<in> borel_measurable (F t)"
    using Xr by simp
  have "{\<omega> \<in> space (F t). infdist (X r \<omega>) A < e} \<in> sets (F t)"
    using meas by measurable
  then show ?thesis
    using r rt by (simp add: space_F)
qed

theorem etime_stopping_time:
  assumes A: "closed A" "A \<noteq> {}" and t: "0 \<le> t"
  shows "{\<omega> \<in> space M. etime T A X \<omega> \<le> t} \<in> sets (F t)"
proof (cases "t < T")
  case True
  have cont_t: "continuous_on {0..t} (\<lambda>s. X s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
  proof (rule continuous_on_subset[OF paths_cont[OF w]])
    show "{0..t} \<subseteq> {0..T}"
      using True by auto
  qed
  have set_eq: "{\<omega> \<in> space M. etime T A X \<omega> \<le> t}
      = (\<Inter>m. \<Union>q\<in>qtimes t.
          {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)})"
  proof (intro set_eqI iffI)
    fix \<omega> assume "\<omega> \<in> {\<omega> \<in> space M. etime T A X \<omega> \<le> t}"
    then have w: "\<omega> \<in> space M" and le: "etime T A X \<omega> \<le> t" by auto
    have iff1: "etime T A X \<omega> \<le> t \<longleftrightarrow> (\<exists>r\<in>{0..t}. X r \<omega> \<in> A)"
      using T_nonneg t True A(1) paths_cont[OF w]
      by (rule etime_le_iff[of T t A X \<omega>])
    have iff2: "(\<exists>r\<in>{0..t}. X r \<omega> \<in> A)
        \<longleftrightarrow> (\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m))"
      using t A cont_t[OF w] by (rule hit_iff_qtimes[of t A X \<omega>])
    from le have "\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m)"
      unfolding iff1 iff2 .
    with w show "\<omega> \<in> (\<Inter>m. \<Union>q\<in>qtimes t.
        {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)})"
      by auto
  next
    fix \<omega> assume mem: "\<omega> \<in> (\<Inter>m. \<Union>q\<in>qtimes t.
        {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)})"
    then have w: "\<omega> \<in> space M"
      by auto
    have iff1: "etime T A X \<omega> \<le> t \<longleftrightarrow> (\<exists>r\<in>{0..t}. X r \<omega> \<in> A)"
      using T_nonneg t True A(1) paths_cont[OF w]
      by (rule etime_le_iff[of T t A X \<omega>])
    have iff2: "(\<exists>r\<in>{0..t}. X r \<omega> \<in> A)
        \<longleftrightarrow> (\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m))"
      using t A cont_t[OF w] by (rule hit_iff_qtimes[of t A X \<omega>])
    from mem have "\<forall>m. \<exists>q\<in>qtimes t. infdist (X q \<omega>) A < 1 / real (Suc m)"
      by auto
    then have "etime T A X \<omega> \<le> t"
      unfolding iff1 iff2 .
    with w show "\<omega> \<in> {\<omega> \<in> space M. etime T A X \<omega> \<le> t}" by simp
  qed
  have "(\<Inter>m. \<Union>q\<in>qtimes t.
      {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)}) \<in> sets (F t)"
  proof (rule sets.countable_INT)
    show "(UNIV :: nat set) \<noteq> {}" by simp
    show "(\<lambda>m. \<Union>q\<in>qtimes t.
        {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)}) ` UNIV
        \<subseteq> sets (F t)"
    proof (intro image_subsetI)
      fix m :: nat
      show "(\<Union>q\<in>qtimes t.
          {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)}) \<in> sets (F t)"
      proof (rule sets.countable_UN'[OF countable_qtimes])
        show "(\<lambda>q. {\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)})
            ` qtimes t \<subseteq> sets (F t)"
        proof (intro image_subsetI)
          fix q assume "q \<in> qtimes t"
          then have q: "0 \<le> q" "q \<le> t"
            using qtimes_subset[OF t] by auto
          show "{\<omega> \<in> space M. infdist (X q \<omega>) A < 1 / real (Suc m)}
              \<in> sets (F t)"
            by (intro infdist_measurable q A)
        qed
      qed
    qed
  qed
  then show ?thesis
    unfolding set_eq .
next
  case False
  have all_le: "etime T A X \<omega> \<le> t" for \<omega>
  proof -
    have "etime T A X \<omega> \<le> T"
      by (rule etime_le_T[OF T_nonneg])
    also have "T \<le> t"
      using False by simp
    finally show ?thesis .
  qed
  have "{\<omega> \<in> space M. etime T A X \<omega> \<le> t} = space M"
    using all_le by auto
  moreover have "space M \<in> sets (F t)"
    using t sets.top[of "F t"] by (simp add: space_F)
  ultimately show ?thesis by simp
qed

end

section \<open>Up to the exit time the process stays in the closed ball\<close>

text \<open>If \<open>A\<close> is the closed exterior of the open ball of radius \<open>r\<close> and the
  process starts strictly inside, then at all times up to and including the
  exit time the process lies in the closed ball: strictly before by the
  definition of the exit time, and at the exit time by continuity from the
  left.\<close>

lemma etime_stays_in_cball:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'c :: real_normed_vector"
  assumes T: "0 \<le> T" and rad: "0 < r"
    and start: "norm (X 0 \<omega>) < r"
    and cont: "continuous_on {0..T} (\<lambda>s. X s \<omega>)"
    and s: "0 \<le> s" and sle: "s \<le> etime T {y. r \<le> norm y} X \<omega>"
  shows "X s \<omega> \<in> cball 0 r"
proof -
  have tauT: "etime T {y. r \<le> norm y} X \<omega> \<le> T"
    by (rule etime_le_T[OF T])
  have sT: "s \<le> T"
    using sle tauT by simp
  have strict: "norm (X v \<omega>) < r"
    if v: "0 \<le> v" and vlt: "v < etime T {y. r \<le> norm y} X \<omega>" for v
  proof (rule ccontr)
    assume "\<not> norm (X v \<omega>) < r"
    then have mem: "X v \<omega> \<in> {y. r \<le> norm y}" by simp
    have "v \<le> T"
      using vlt tauT by simp
    then have "etime T {y. r \<le> norm y} X \<omega> \<le> v"
      using T v mem by (intro etime_le_of_mem) auto
    with vlt show False by simp
  qed
  show ?thesis
  proof (cases "s < etime T {y. r \<le> norm y} X \<omega>")
    case True
    then have "norm (X s \<omega>) < r"
      using s by (intro strict) auto
    then show ?thesis by (simp add: mem_cball dist_norm)
  next
    case False
    with sle have s_eq: "s = etime T {y. r \<le> norm y} X \<omega>" by simp
    show ?thesis
    proof (cases "s = 0")
      case True
      then show ?thesis
        using start rad by (simp add: mem_cball dist_norm)
    next
      case False
      then have spos: "0 < s"
        using s by simp
      define p where "p = (\<lambda>n :: nat. s - s * inverse (real (Suc n)))"
      have p_lt: "p n < s" for n
        unfolding p_def using spos by simp
      have p_nonneg: "0 \<le> p n" for n
      proof -
        have inv1: "inverse (real (Suc n)) \<le> 1"
          using le_imp_inverse_le[of 1 "real (Suc n)"] by simp
        have "s * inverse (real (Suc n)) \<le> s * 1"
          using s inv1 by (intro mult_left_mono) auto
        then show ?thesis
          unfolding p_def by simp
      qed
      have p_inS: "p n \<in> {0..T}" for n
        using p_nonneg[of n] p_lt[of n] sT by auto
      have plim: "p \<longlonglongrightarrow> s"
      proof -
        have "(\<lambda>n. s * inverse (real (Suc n))) \<longlonglongrightarrow> s * 0"
          by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
        then have z: "(\<lambda>n. s * inverse (real (Suc n))) \<longlonglongrightarrow> 0"
          by simp
        then have "(\<lambda>n. s - s * inverse (real (Suc n))) \<longlonglongrightarrow> s - 0"
          by (intro tendsto_diff tendsto_const)
        then show ?thesis
          unfolding p_def by simp
      qed
      have "((\<lambda>v. X v \<omega>) \<circ> p) \<longlonglongrightarrow> X s \<omega>"
        using cont[unfolded continuous_on_sequentially] s sT p_inS plim
        by auto
      then have lim: "(\<lambda>n. norm (X (p n) \<omega>)) \<longlonglongrightarrow> norm (X s \<omega>)"
        by (auto intro: tendsto_norm simp: comp_def)
      have bnd: "norm (X (p n) \<omega>) \<le> r" for n
      proof -
        have "p n < etime T {y. r \<le> norm y} X \<omega>"
          using p_lt[of n] s_eq by simp
        then have "norm (X (p n) \<omega>) < r"
          using p_nonneg[of n] by (intro strict) auto
        then show ?thesis by simp
      qed
      have "norm (X s \<omega>) \<le> r"
        using bnd by (intro tendsto_upperbound[OF lim]) auto
      then show ?thesis by (simp add: mem_cball dist_norm)
    qed
  qed
qed

end
