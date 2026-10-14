
(*<*)
theory Berge
  imports "HOL-Analysis.Analysis"
begin

(*>*)

section \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close>: the upper semicontinuity half, without a selection theorem\<close>

text \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close> cites Larsson--Ruf's proof of their Proposition 2.2(ii),
  (iii): \<open>\<P>\<^sub>x\<close> is the pushforward of \<open>\<P>\<^sub>0\<close> under \<open>x+\<cdot>\<close>, so
  \<open>v(x) = sup\<^bsub>P \<in> \<P>\<^sub>0\<^esub> f(x,P)\<close> with \<open>f\<close> jointly upper semicontinuous and
  \<open>\<P>\<^sub>0\<close> compact; a selection theorem (Bertsekas--Shreve, Prop. 7.33) then
  gives both upper semicontinuity of \<open>v\<close> and a measurable optimiser.

  Of those two conclusions only the measurable optimiser needs a selection
  theorem: upper semicontinuity of a supremum of a jointly usc function over a
  compact index set is the upper half of Berge's maximum theorem, needing no
  measurable selection or descriptive set theory, and is proved directly here,
  leaving Bertsekas--Shreve 7.33 needed only for the dynamic programming
  principle's measurable optimiser.

  The hypothesis \<open>box\<close> below is joint upper semicontinuity at \<open>(x,P)\<close>,
  written via a product neighbourhood rather than \<open>nhds (x,P)\<close>, independent
  of how the product topology is packaged.  The index space carries a
  \<open>topology\<close> value \<open>Y\<close> rather than a type-class topology: the weak topology
  on laws is a \<open>topology\<close> value (\<open>weak_conv_topology\<close>), not a type-class
  instance, since different base spaces induce different weak topologies on
  the same type \<open>'a measure\<close>.  The conclusion stays in the type class, being
  about \<open>nhds x\<close>.

  Proof idea: pick \<open>c'\<close> strictly between the supremum and \<open>c\<close>; every
  \<open>P \<in> C\<close> has \<open>F x P < c'\<close>, so joint usc gives a box \<open>U\<^sub>P \<times> V\<^sub>P\<close> with
  \<open>F < c'\<close> there; the \<open>V\<^sub>P\<close> cover the compact \<open>C\<close>, so finitely many suffice
  (\<open>compactinD\<close> hands back a finite set of opens, turned back into a finite
  set of indices by \<open>finite_subset_image\<close>), and the matching finite
  intersection of the \<open>U\<^sub>P\<close> is a neighbourhood of \<open>x\<close> on which the whole
  supremum is \<open>\<le> c' < c\<close>.\<close>

theorem usc_sup_over_compactin:
  fixes F :: "'a::topological_space \<Rightarrow> 'b \<Rightarrow> real"
    and Y :: "'b topology" and C :: "'b set" and x :: 'a and c :: real
  assumes cC: "compactin Y C" and neC: "C \<noteq> {}"
    and bdd: "\<And>y. bdd_above (F y ` C)"
    and lt: "Sup (F x ` C) < c"
    and box: "\<And>P d. P \<in> C \<Longrightarrow> F x P < d \<Longrightarrow>
        \<exists>U V. open U \<and> openin Y V \<and> x \<in> U \<and> P \<in> V
              \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. F y Q < d)"
  shows "eventually (\<lambda>y. Sup (F y ` C) < c) (nhds x)"
proof -
  obtain c' where c1: "Sup (F x ` C) < c'" and c2: "c' < c"
    using lt dense by blast
  have small: "F x P < c'" if P: "P \<in> C" for P
  proof -
    have "F x P \<le> Sup (F x ` C)"
      by (rule cSup_upper) (use P bdd in auto)
    with c1 show ?thesis by linarith
  qed
  have ex: "\<forall>P \<in> C. \<exists>U V. open U \<and> openin Y V \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. F y Q < c')"
    using box small by blast
  have ex': "\<forall>P \<in> C. \<exists>W :: 'a set \<times> 'b set.
      open (fst W) \<and> openin Y (snd W) \<and> x \<in> fst W \<and> P \<in> snd W
      \<and> (\<forall>y \<in> fst W. \<forall>Q \<in> snd W \<inter> C. F y Q < c')"
  proof
    fix P assume P: "P \<in> C"
    from bspec[OF ex P] obtain U V where
      "open U" "openin Y V" "x \<in> U" "P \<in> V" "\<forall>y\<in>U. \<forall>Q\<in>V \<inter> C. F y Q < c'"
      by blast
    then show "\<exists>W :: 'a set \<times> 'b set.
        open (fst W) \<and> openin Y (snd W) \<and> x \<in> fst W \<and> P \<in> snd W
        \<and> (\<forall>y \<in> fst W. \<forall>Q \<in> snd W \<inter> C. F y Q < c')"
      by (intro exI[of _ "(U,V)"]) simp
  qed
  have exf: "\<exists>WW. \<forall>P\<in>C.
      open (fst (WW P)) \<and> openin Y (snd (WW P)) \<and> x \<in> fst (WW P)
      \<and> P \<in> snd (WW P)
      \<and> (\<forall>y \<in> fst (WW P). \<forall>Q \<in> snd (WW P) \<inter> C. F y Q < c')"
    by (rule bchoice[OF ex'])
  then obtain WW where Wb: "\<forall>P\<in>C.
      open (fst (WW P)) \<and> openin Y (snd (WW P)) \<and> x \<in> fst (WW P)
      \<and> P \<in> snd (WW P)
      \<and> (\<forall>y \<in> fst (WW P). \<forall>Q \<in> snd (WW P) \<inter> C. F y Q < c')"
    by (rule exE)
  define UU where "UU = (\<lambda>P. fst (WW P))"
  define VV where "VV = (\<lambda>P. snd (WW P))"
  have oU: "open (UU P)" if P: "P \<in> C" for P
    unfolding UU_def using bspec[OF Wb P] by simp
  have oV: "openin Y (VV P)" if P: "P \<in> C" for P
    unfolding VV_def using bspec[OF Wb P] by simp
  have xU: "x \<in> UU P" if P: "P \<in> C" for P
    unfolding UU_def using bspec[OF Wb P] by simp
  have PV: "P \<in> VV P" if P: "P \<in> C" for P
    unfolding VV_def using bspec[OF Wb P] by simp
  have less: "F y Q < c'" if P: "P \<in> C" and y: "y \<in> UU P"
    and Q: "Q \<in> VV P" and QC: "Q \<in> C"
    for P y Q
    using bspec[OF Wb P] y Q QC unfolding UU_def VV_def by simp
  text \<open>The covering step, in the \<open>openin\<close> world: cover by the set \<open>VV ` C\<close>, then
    turn the finite subcover back into a finite set of indices.\<close>
  have cover: "C \<subseteq> \<Union>(VV ` C)" using PV by blast
  have opens: "openin Y V" if "V \<in> VV ` C" for V using that oV by blast
  obtain \<F> where F1: "\<F> \<subseteq> VV ` C" and F2: "finite \<F>" and F3: "C \<subseteq> \<Union>\<F>"
    using compactinD[OF cC opens cover] by blast
  obtain D where D1: "D \<subseteq> C" and D2: "finite D" and Deq: "\<F> = VV ` D"
    using finite_subset_image[OF F2 F1] by blast
  have D3: "C \<subseteq> (\<Union>P\<in>D. VV P)" using F3 unfolding Deq by simp

  define U where "U = (\<Inter>P\<in>D. UU P)"
  have oUD: "\<forall>P\<in>D. open (UU P)" using oU D1 by blast
  have openU: "open U" unfolding U_def by (rule open_INT[OF D2 oUD])
  have xinU: "x \<in> U" unfolding U_def using xU D1 by blast
  have key: "Sup (F y ` C) \<le> c'" if yU: "y \<in> U" for y
  proof (rule cSup_least)
    show "F y ` C \<noteq> {}" using neC by blast
  next
    fix z assume "z \<in> F y ` C"
    then obtain Q where Q: "Q \<in> C" and zdef: "z = F y Q" by blast
    from Q D3 obtain P where P: "P \<in> D" and QV: "Q \<in> VV P" by blast
    have "y \<in> UU P" using yU P unfolding U_def by blast
    then have "F y Q < c'" using less[of P y Q] P D1 QV Q by blast
    then show "z \<le> c'" unfolding zdef by linarith
  qed
  have final: "Sup (F y ` C) < c" if yU: "y \<in> U" for y
    using key[OF yU] c2 by linarith
  have ballU: "\<forall>y \<in> U. Sup (F y ` C) < c" by (intro ballI) (rule final)
  show ?thesis
    unfolding eventually_nhds
    by (rule exI[of _ U]) (intro conjI openU xinU ballU)
qed

text \<open>The type-class instance: \<open>Y = euclidean\<close>, where \<open>compactin\<close> is
  \<open>compact\<close> and \<open>openin\<close> is \<open>open\<close>.\<close>

theorem usc_sup_over_compact:
  fixes F :: "'a::topological_space \<Rightarrow> 'b::topological_space \<Rightarrow> real"
    and C :: "'b set" and x :: 'a and c :: real
  assumes cC: "compact C" and neC: "C \<noteq> {}"
    and bdd: "\<And>y. bdd_above (F y ` C)"
    and lt: "Sup (F x ` C) < c"
    and box: "\<And>P d. P \<in> C \<Longrightarrow> F x P < d \<Longrightarrow>
        \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> P \<in> V
              \<and> (\<forall>y \<in> U. \<forall>Q \<in> V. F y Q < d)"
  shows "eventually (\<lambda>y. Sup (F y ` C) < c) (nhds x)"
proof (rule usc_sup_over_compactin[where Y = euclidean])
  fix P d assume "P \<in> C" "F x P < d"
  from box[OF this] show "\<exists>U V. open U \<and> openin euclidean V \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. F y Q < d)"
    by auto
qed (use cC neC bdd lt in auto)

section \<open>Feeding \<open>box\<close> from a sequential statement\<close>

text \<open>Two helpers.  \<open>metrizable_space_def\<close> quantifies over the carrier as well
  as the metric; the carrier can always be taken to be \<open>topspace X\<close>.  And a
  sequence converges once its distance to the limit is dominated by a null
  sequence.\<close>

lemma metrizable_space_metric:
  assumes "metrizable_space X"
  obtains d where "Metric_space (topspace X) d"
    and "Metric_space.mtopology (topspace X) d = X"
  using assms unfolding metrizable_space_def by (metis Metric_space.topspace_mtopology)

lemma (in Metric_space) limitin_of_dist_bound:
  assumes "\<And>n. x n \<in> M" and "y \<in> M" and "\<And>n. d (x n) y \<le> r n"
    and "(r \<longlongrightarrow> 0) F"
  shows "limitin mtopology x y F"
proof -
  have "((\<lambda>n. d (x n) y) \<longlongrightarrow> 0) F"
    by (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ r]) (use assms in auto)
  then show ?thesis using assms unfolding limitin_metric_dist_null by simp
qed

text \<open>
  \<open>usc_sup_over_compactin\<close> asks for \<open>box\<close> topologically, but weak convergence
  of measures is naturally a statement about sequences -- the form of the
  AFP's Portmanteau theorems and of \<open>Path_Exit_Times.etime_shift_box\<close>.

  The two are equivalent when both spaces are metrizable, by the
  Levy--Prokhorov theorem (\<open>metrizable_weak_conv_topology\<close>), applicable
  since the path space is metrizable and separable. This lemma is that
  equivalence; nothing about measures enters it.

  The direction proved is sequences to neighbourhoods. Its contrapositive
  picks, for each \<open>n\<close>, a counterexample inside the \<open>1/Suc n\<close> balls, and
  those assemble into convergent sequences the hypothesis forbids --
  countable choice does the work, so metrizability cannot be dropped.
\<close>

lemma box_of_sequential:
  fixes X :: "'a topology" and Y :: "'b topology" and S :: "'b set"
  assumes mX: "metrizable_space X" and mY: "metrizable_space Y"
    and x: "x \<in> topspace X" and P: "P \<in> topspace Y"
    and seq: "\<And>yi Qi. limitin X yi x sequentially
        \<Longrightarrow> limitin Y Qi P sequentially
        \<Longrightarrow> (\<And>i. Qi i \<in> S)
        \<Longrightarrow> eventually (\<lambda>i. R (yi i) (Qi i)) sequentially"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> S. R y Q)"
proof (rule ccontr)
  assume neg: "\<not> ?thesis"
  obtain dX dY where dX: "Metric_space (topspace X) dX"
    and tX: "Metric_space.mtopology (topspace X) dX = X"
    and dY: "Metric_space (topspace Y) dY"
    and tY: "Metric_space.mtopology (topspace Y) dY = Y"
    using metrizable_space_metric[OF mX] metrizable_space_metric[OF mY] by metis
  interpret MX: Metric_space "topspace X" dX by (rule dX)
  interpret MY: Metric_space "topspace Y" dY by (rule dY)
  have "\<exists>z W. z \<in> MX.mball x (1 / Suc n)
      \<and> W \<in> MY.mball P (1 / Suc n) \<and> W \<in> S \<and> \<not> R z W" for n :: nat
  proof -
    have "openin X (MX.mball x (1 / Suc n))" "openin Y (MY.mball P (1 / Suc n))"
      using MX.openin_mball MY.openin_mball unfolding tX tY by blast+
    moreover have "x \<in> MX.mball x (1 / Suc n)" "P \<in> MY.mball P (1 / Suc n)"
      using x P by simp_all
    ultimately show ?thesis using neg by blast
  qed
  then obtain y Q where yQ: "\<And>n. y n \<in> MX.mball x (1 / Suc n)"
    "\<And>n. Q n \<in> MY.mball P (1 / Suc n)" "\<And>n. Q n \<in> S"
    "\<And>n. \<not> R (y n) (Q n)"
    by metis
  have r: "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0" by (rule LIMSEQ_Suc[OF lim_1_over_n])
  have limy: "limitin X y x sequentially"
    using MX.limitin_of_dist_bound[OF _ x _ r] yQ(1) unfolding tX
    by (simp add: MX.commute less_imp_le)
  have limQ: "limitin Y Q P sequentially"
    using MY.limitin_of_dist_bound[OF _ P _ r] yQ(2) unfolding tY
    by (simp add: MY.commute less_imp_le)
  from seq[OF limy limQ yQ(3)] show False using yQ(4) by simp
qed

text \<open>The specialisation used: the first factor is a metric type, so Berge's
  \<open>box\<close> wants type-class \<open>open\<close> rather than \<open>openin euclidean\<close>.  Since
  \<open>euclidean\<close> abbreviates \<open>topology open\<close>, \<open>unfolding open_openin\<close> rewrites
  the bare \<open>open\<close> inside \<open>euclidean\<close> and regenerates its own redex, looping;
  the \<open>[symmetric]\<close> orientation is the safe declared simp rule.\<close>

lemma box_of_sequential_euclidean:
  fixes Y :: "'b topology" and S :: "'b set" and x :: "'a::metric_space"
  assumes mY: "metrizable_space Y" and P: "P \<in> topspace Y"
    and seq: "\<And>yi Qi. yi \<longlonglongrightarrow> x
        \<Longrightarrow> limitin Y Qi P sequentially
        \<Longrightarrow> (\<And>i. Qi i \<in> S)
        \<Longrightarrow> eventually (\<lambda>i. R (yi i) (Qi i)) sequentially"
  shows "\<exists>U V. open U \<and> openin Y V \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> S. R y Q)"
proof -
  have "\<exists>U V. openin (euclidean :: 'a topology) U \<and> openin Y V
      \<and> x \<in> U \<and> P \<in> V \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> S. R y Q)"
  proof (rule box_of_sequential)
    show "metrizable_space (euclidean :: 'a topology)"
      by (rule metrizable_space_euclidean)
    show "metrizable_space Y" by (rule mY)
    show "x \<in> topspace (euclidean :: 'a topology)" by simp
    show "P \<in> topspace Y" by (rule P)
  next
    fix yi :: "nat \<Rightarrow> 'a" and Qi :: "nat \<Rightarrow> 'b"
    assume ly: "limitin (euclidean :: 'a topology) yi x sequentially"
      and lQ: "limitin Y Qi P sequentially" and inS: "\<And>i. Qi i \<in> S"
    have "yi \<longlonglongrightarrow> x" using ly by simp
    from seq[OF this lQ inS]
    show "eventually (\<lambda>i. R (yi i) (Qi i)) sequentially" .
  qed
  thus ?thesis by simp
qed

section \<open>Sequential compactness gives \<open>compactin\<close> in a metrizable space\<close>

text \<open>
  The glue between Lemmas 2.2 and 2.3 of \<^cite>\<open>LaiShkolnikovSoner\<close> and Berge's theorem. Those lemmas
  deliver sequential compactness of the law set -- 2.2 extracts a weakly
  convergent subsequence, 2.3 puts the limit back in the set -- whereas
  \<open>usc_sup_over_compactin\<close> consumes \<open>compactin\<close>. In a metrizable space the
  two coincide (\<open>Metric_space.compactin_sequentially\<close>); this lemma
  transports that fact to a \<open>topology\<close> value, the interface Lemma 2.3 needs
  to supply.
\<close>

lemma compactin_of_seq_compact:
  fixes Y :: "'b topology" and C :: "'b set"
  assumes mY: "metrizable_space Y" and sub: "C \<subseteq> topspace Y"
    and seq: "\<And>\<sigma> :: nat \<Rightarrow> 'b. range \<sigma> \<subseteq> C \<Longrightarrow>
        \<exists>l r. l \<in> C \<and> strict_mono r \<and> limitin Y (\<sigma> \<circ> r) l sequentially"
  shows "compactin Y C"
proof -
  obtain dY where dY: "Metric_space (topspace Y) dY"
    and tY: "Metric_space.mtopology (topspace Y) dY = Y"
    using metrizable_space_metric[OF mY] by metis
  interpret MY: Metric_space "topspace Y" dY by (rule dY)
  show ?thesis
    using MY.compactin_sequentially[of C] sub seq unfolding tY by blast
qed

(*<*)
end
(*>*)
