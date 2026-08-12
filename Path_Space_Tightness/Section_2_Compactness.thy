section \<open>The Arzela--Ascoli step of Lemma 2.2\<close>

text \<open>
  Lemma 2.2 -- relative compactness of continuous martingale laws with
  covariation rates in a bounded set @{text S} -- follows the chain:

  \<^item> Ito's formula and the Burkholder-Davis-Gundy inequality give the fourth
    moment bound of Eq. (2.7), @{text "E |X t - X s| ^ 4 \<le> 66 C\<^sup>2 (t - s)\<^sup>2"};
  \<^item> Kolmogorov's continuity criterion gives locally Holder paths;
  \<^item> the Arzela-Ascoli theorem gives compact sets of paths;
  \<^item> Prokhorov's theorem converts tightness into relative compactness.

  The last three are available in the AFP:

  \<^item> Kolmogorov's criterion is @{text Kolmogorov_Chentsov.Kolmogorov_Chentsov},
    whose hypothesis is literally the moment bound of Eq. (2.7) with
    @{text "a = 4"}, @{text "b = 1"}, @{text "C = 66 C\<^sup>2"}, and whose
    conclusion is a modification with all paths @{text "local_holder_on \<gamma>"} for
    @{text "\<gamma> < 1/4"};
  \<^item> @{text Kolmogorov_Chentsov.local_holder_compact_imp_holder} upgrades that to
    a genuine Holder bound on each compact @{text "{0..T}"};
  \<^item> Arzela-Ascoli is @{text "HOL-Complex_Analysis.Arzela_Ascoli"};
  \<^item> Prokhorov's theorem is @{text Levy_Prokhorov_Metric.Prokhorov_theorem_LP}.

  This theory supplies the Arzela-Ascoli step in the form the rest of the chain
  needs it: a Holder bound with a constant @{text c} common to the whole
  family, since @{text "\<gamma>-holder_on"} quantifies its constant existentially per
  function, and Arzela-Ascoli genuinely requires a common one. Producing that
  uniform constant from Eq. (2.7) is the remaining probabilistic content of
  Lemma 2.2.
\<close>

theory Section_2_Compactness
  imports
    "HOL-Complex_Analysis.Great_Picard"
    "Kolmogorov_Chentsov.Holder_Continuous"
begin

subsection \<open>Uniform bounds and equicontinuity from a Holder bound\<close>

text \<open>A Holder path on @{term "{0..T}"} is bounded in terms of its initial value.\<close>

lemma holder_bound_norm:
  fixes F :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c" and t: "t \<in> {0..T}"
    and hol: "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                 \<Longrightarrow> norm (F t - F s) \<le> c * \<bar>t - s\<bar> powr ga"
  shows "norm (F t) \<le> norm (F 0) + c * T powr ga"
proof -
  have "norm (F t - F 0) \<le> c * \<bar>t - 0\<bar> powr ga"
    using hol[of 0 t] t T by simp
  also have "\<bar>t - 0\<bar> powr ga \<le> T powr ga"
    using t ga by (simp add: powr_mono2)
  then have "c * \<bar>t - 0\<bar> powr ga \<le> c * T powr ga"
    using c by (simp add: mult_left_mono)
  finally have "norm (F t - F 0) \<le> c * T powr ga" .
  moreover have "norm (F t) \<le> norm (F 0) + norm (F t - F 0)"
    by (rule norm_triangle_sub)
  ultimately show ?thesis by simp
qed

text \<open>A Holder bound with a constant common to the family gives equicontinuity.\<close>

lemma holder_equicontinuous:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> 'b::real_normed_vector"
  assumes ga: "0 < ga" and c: "0 \<le> c" and e: "0 < e" and u: "u \<in> S"
    and hol: "\<And>m s t. s \<in> S \<Longrightarrow> t \<in> S
                 \<Longrightarrow> norm (F m t - F m s) \<le> c * \<bar>t - s\<bar> powr ga"
  shows "\<exists>d>0. \<forall>m y. y \<in> S \<and> \<bar>u - y\<bar> < d \<longrightarrow> norm (F m u - F m y) < e"
proof -
  define d where "d = (e / (c + 1)) powr (1 / ga)"
  have dpos: "0 < d" unfolding d_def using e c by simp
  have dga: "d powr ga = e / (c + 1)"
    unfolding d_def using ga e c by (simp add: powr_powr)
  have "\<forall>m y. y \<in> S \<and> \<bar>u - y\<bar> < d \<longrightarrow> norm (F m u - F m y) < e"
  proof (intro allI impI)
    fix m y assume y: "y \<in> S \<and> \<bar>u - y\<bar> < d"
    show "norm (F m u - F m y) < e"
    proof (cases "u = y")
      case True
      thus ?thesis using e by simp
    next
      case False
      have h1: "norm (F m u - F m y) \<le> c * \<bar>u - y\<bar> powr ga"
        using hol[where m = m and s = y and t = u] y u by simp
      have "\<bar>u - y\<bar> powr ga < d powr ga"
        using y False ga by (simp add: powr_less_mono2)
      then have "\<bar>u - y\<bar> powr ga \<le> e / (c + 1)" using dga by simp
      then have h2: "c * \<bar>u - y\<bar> powr ga \<le> c * (e / (c + 1))"
        using c by (rule mult_left_mono)
      have h3: "c * (e / (c + 1)) < e"
        using c e by (simp add: field_simps)
      from h1 h2 h3 show ?thesis by simp
    qed
  qed
  with dpos show ?thesis by blast
qed

subsection \<open>The Arzela-Ascoli step\<close>

text \<open>
  A family of paths on @{term "{0..T}"} sharing an initial value and a Holder
  constant has a uniformly convergent subsequence, and the limit is a path with
  the same initial value and the same Holder bound. This is the form in which
  Lemma 2.2's proof uses the Arzela-Ascoli theorem.
\<close>

theorem holder_family_subsequence:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c"
    and start: "\<And>m. F m 0 = x"
    and hol: "\<And>m s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                 \<Longrightarrow> norm (F m t - F m s) \<le> c * \<bar>t - s\<bar> powr ga"
  obtains L and k :: "nat \<Rightarrow> nat"
    where "strict_mono k" "continuous_on {0..T} L" "L 0 = x"
    "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
        \<Longrightarrow> norm (L t - L s) \<le> c * \<bar>t - s\<bar> powr ga"
    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. norm (F (k m) t - L t) < e"
proof -
  have cpt: "compact {0..T::real}" by simp
  have bnd: "\<And>m t. t \<in> {0..T} \<Longrightarrow> norm (F m t) \<le> norm x + c * T powr ga"
  proof -
    fix m t assume t: "t \<in> {0..T}"
    have "norm (F m t) \<le> norm (F m 0) + c * T powr ga"
      by (rule holder_bound_norm[OF T ga c t]) (rule hol)
    thus "norm (F m t) \<le> norm x + c * T powr ga" by (simp add: start)
  qed
  have eqc: "\<And>u e. u \<in> {0..T} \<Longrightarrow> 0 < e \<Longrightarrow>
      \<exists>d. 0 < d \<and> (\<forall>m y. y \<in> {0..T} \<and> norm (u - y) < d
                          \<longrightarrow> norm (F m u - F m y) < e)"
  proof -
    fix u e :: real assume "u \<in> {0..T}" "0 < e"
    from holder_equicontinuous[OF ga c this(2) this(1) hol]
    show "\<exists>d. 0 < d \<and> (\<forall>m y. y \<in> {0..T} \<and> norm (u - y) < d
                          \<longrightarrow> norm (F m u - F m y) < e)" by simp
  qed
  obtain L and k :: "nat \<Rightarrow> nat"
    where L1: "continuous_on {0..T} L" and L2: "strict_mono k"
    and L3: "\<And>e. 0 < e \<Longrightarrow>
        \<exists>N. \<forall>m t. m \<ge> N \<and> t \<in> {0..T} \<longrightarrow> norm (F (k m) t - L t) < e"
    using Arzela_Ascoli[OF cpt bnd eqc] by blast
  have ptw: "(\<lambda>m. F (k m) t) \<longlonglongrightarrow> L t" if t: "t \<in> {0..T}" for t
  proof (unfold LIMSEQ_iff, intro allI impI)
    fix r :: real assume r: "0 < r"
    from L3[OF r] obtain N where
      "\<forall>m t'. m \<ge> N \<and> t' \<in> {0..T} \<longrightarrow> norm (F (k m) t' - L t') < r" by blast
    thus "\<exists>no. \<forall>m\<ge>no. norm (F (k m) t - L t) < r" using t by blast
  qed
  have L0: "L 0 = x"
  proof -
    have z: "(0::real) \<in> {0..T}" using T by simp
    have "(\<lambda>m. F (k m) 0) \<longlonglongrightarrow> L 0" by (rule ptw[OF z])
    moreover have "(\<lambda>m. F (k m) 0) = (\<lambda>m. x)" using start by simp
    ultimately have "(\<lambda>m::nat. x) \<longlonglongrightarrow> L 0" by simp
    thus ?thesis using LIMSEQ_const_iff by metis
  qed
  have Lhol: "norm (L t - L s) \<le> c * \<bar>t - s\<bar> powr ga"
    if s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for s t
  proof -
    have "(\<lambda>m. norm (F (k m) t - F (k m) s)) \<longlonglongrightarrow> norm (L t - L s)"
      by (intro tendsto_norm tendsto_diff ptw[OF t] ptw[OF s])
    moreover have "\<forall>\<^sub>F m in sequentially.
        norm (F (k m) t - F (k m) s) \<le> c * \<bar>t - s\<bar> powr ga"
      using hol s t by (intro always_eventually) blast
    ultimately show ?thesis by (rule tendsto_upperbound) simp
  qed
  have L4: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. norm (F (k m) t - L t) < e"
    using L3 by blast
  show ?thesis by (rule that[OF L2 L1 L0 Lhol L4])
qed

subsection \<open>Composing with the AFP's Holder predicate\<close>

text \<open>
  The same statement phrased with @{const dist}, which is how
  @{const holder_on} -- and hence the output of Kolmogorov's criterion -- states
  its bound.
\<close>

corollary holder_family_subsequence_dist:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes T: "0 \<le> T" and ga: "0 < ga" and c: "0 \<le> c"
    and start: "\<And>m. F m 0 = x"
    and hol: "\<And>m s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                 \<Longrightarrow> dist (F m t) (F m s) \<le> c * dist t s powr ga"
  obtains L and k :: "nat \<Rightarrow> nat"
    where "strict_mono k" "continuous_on {0..T} L" "L 0 = x"
    "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
        \<Longrightarrow> dist (L t) (L s) \<le> c * dist t s powr ga"
    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. dist (F (k m) t) (L t) < e"
proof -
  have hol': "\<And>m s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                 \<Longrightarrow> norm (F m t - F m s) \<le> c * \<bar>t - s\<bar> powr ga"
    using hol by (simp add: dist_norm dist_real_def)
  show ?thesis
  proof (rule holder_family_subsequence[OF T ga c start hol'])
    fix L and k :: "nat \<Rightarrow> nat"
    assume k: "strict_mono k" and Lc: "continuous_on {0..T} L" and L0: "L 0 = x"
      and Lh: "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                   \<Longrightarrow> norm (L t - L s) \<le> c * \<bar>t - s\<bar> powr ga"
      and Lu: "\<And>e. 0 < e \<Longrightarrow>
          \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. norm (F (k m) t - L t) < e"
    have Lh': "\<And>s t. s \<in> {0..T} \<Longrightarrow> t \<in> {0..T}
                   \<Longrightarrow> dist (L t) (L s) \<le> c * dist t s powr ga"
      using Lh by (simp add: dist_norm dist_real_def)
    have Lu': "\<And>e. 0 < e \<Longrightarrow>
        \<exists>N. \<forall>m\<ge>N. \<forall>t\<in>{0..T}. dist (F (k m) t) (L t) < e"
      using Lu by (simp add: dist_norm)
    show thesis by (rule that[OF k Lc L0 Lh' Lu'])
  qed
qed
text \<open>
  The limit produced above is itself @{term "ga-holder_on {0..T}"}, so the
  Arzela-Ascoli step stays inside the class delivered by Kolmogorov's
  criterion.
\<close>

lemma holder_onI_bound:
  fixes L :: "real \<Rightarrow> 'b::metric_space"
  assumes ga: "ga \<in> {0<..1}" and c: "0 \<le> c"
    and bnd: "\<And>s t. s \<in> D \<Longrightarrow> t \<in> D \<Longrightarrow> dist (L t) (L s) \<le> c * dist t s powr ga"
  shows "ga-holder_on D L"
  unfolding holder_on_def
proof (intro conjI ga exI[of _ c] conjI c ballI)
  fix r s assume "r \<in> D" "s \<in> D"
  thus "dist (L r) (L s) \<le> c * dist r s powr ga"
    using bnd by (simp add: dist_commute)
qed


section \<open>Proposition 2.4: the upper semicontinuity half, without a selection theorem\<close>

text \<open>Proposition 2.4 cites Larsson--Ruf's proof of their Proposition 2.2(ii),
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
  of how the product topology is packaged.

  Proof idea: pick \<open>c'\<close> strictly between the supremum and \<open>c\<close>; every
  \<open>P \<in> C\<close> has \<open>F x P < c'\<close>, so joint usc gives a box \<open>U\<^sub>P \<times> V\<^sub>P\<close> with
  \<open>F < c'\<close> there; the \<open>V\<^sub>P\<close> cover the compact \<open>C\<close>, so finitely many suffice,
  and the matching finite intersection of the \<open>U\<^sub>P\<close> is a neighbourhood of
  \<open>x\<close> on which the whole supremum is \<open>\<le> c' < c\<close>.\<close>

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
proof -
  obtain c' where c1: "Sup (F x ` C) < c'" and c2: "c' < c"
    using lt dense by blast
  have small: "F x P < c'" if P: "P \<in> C" for P
  proof -
    have "F x P \<le> Sup (F x ` C)"
      by (rule cSup_upper) (use P bdd in auto)
    with c1 show ?thesis by linarith
  qed
  have ex: "\<forall>P \<in> C. \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V. F y Q < c')"
    using box small by blast
  \<comment> \<open>choose the two neighbourhoods together, as a pair: a double \<open>bchoice\<close> is
      beyond \<open>metis\<close> here, but one choice over pairs is routine\<close>
  have ex': "\<forall>P \<in> C. \<exists>W :: 'a set \<times> 'b set.
      open (fst W) \<and> open (snd W) \<and> x \<in> fst W \<and> P \<in> snd W
      \<and> (\<forall>y \<in> fst W. \<forall>Q \<in> snd W. F y Q < c')"
  proof
    fix P assume P: "P \<in> C"
    \<comment> \<open>eliminate only the two existentials: chaining the bounded \<open>\<forall>P\<in>C\<close> into
        the same \<open>blast\<close> makes it search without terminating\<close>
    from bspec[OF ex P] obtain U V where
      "open U" "open V" "x \<in> U" "P \<in> V" "\<forall>y\<in>U. \<forall>Q\<in>V. F y Q < c'"
      by blast
    then show "\<exists>W :: 'a set \<times> 'b set.
        open (fst W) \<and> open (snd W) \<and> x \<in> fst W \<and> P \<in> snd W
        \<and> (\<forall>y \<in> fst W. \<forall>Q \<in> snd W. F y Q < c')"
      by (intro exI[of _ "(U,V)"]) simp
  qed
  \<comment> \<open>eliminate the choice in exactly the shape \<open>bchoice\<close> produces: bridging
      \<open>\<forall>P\<in>C\<close> to \<open>\<And>P. P \<in> C \<Longrightarrow>\<close> inside the \<open>obtain\<close> sends \<open>blast\<close> searching
      without terminating\<close>
  have exf: "\<exists>WW. \<forall>P\<in>C.
      open (fst (WW P)) \<and> open (snd (WW P)) \<and> x \<in> fst (WW P) \<and> P \<in> snd (WW P)
      \<and> (\<forall>y \<in> fst (WW P). \<forall>Q \<in> snd (WW P). F y Q < c')"
    by (rule bchoice[OF ex'])
  then obtain WW where Wb: "\<forall>P\<in>C.
      open (fst (WW P)) \<and> open (snd (WW P)) \<and> x \<in> fst (WW P) \<and> P \<in> snd (WW P)
      \<and> (\<forall>y \<in> fst (WW P). \<forall>Q \<in> snd (WW P). F y Q < c')"
    by (rule exE)
  define UU where "UU = (\<lambda>P. fst (WW P))"
  define VV where "VV = (\<lambda>P. snd (WW P))"
  have oU: "open (UU P)" if P: "P \<in> C" for P
    unfolding UU_def using bspec[OF Wb P] by simp
  have oV: "open (VV P)" if P: "P \<in> C" for P
    unfolding VV_def using bspec[OF Wb P] by simp
  have xU: "x \<in> UU P" if P: "P \<in> C" for P
    unfolding UU_def using bspec[OF Wb P] by simp
  have PV: "P \<in> VV P" if P: "P \<in> C" for P
    unfolding VV_def using bspec[OF Wb P] by simp
  have less: "F y Q < c'" if P: "P \<in> C" and y: "y \<in> UU P" and Q: "Q \<in> VV P"
    for P y Q
    using bspec[OF Wb P] y Q unfolding UU_def VV_def by simp
  have cover: "C \<subseteq> (\<Union>P\<in>C. VV P)" using PV by blast
  have oVall: "\<And>T. T \<in> C \<Longrightarrow> open (VV T)" by (rule oV)
  obtain D where D1: "D \<subseteq> C" and D2: "finite D" and D3: "C \<subseteq> (\<Union>P\<in>D. VV P)"
    by (rule compactE_image[OF cC oVall cover])
  define U where "U = (\<Inter>P\<in>D. UU P)"
  \<comment> \<open>\<open>open_INT\<close> takes a bounded-\<open>\<forall>\<close> premise, not a \<open>\<And>\<close>-rule\<close>
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
    then have "F y Q < c'" using less[of P y Q] P D1 QV by blast
    then show "z \<le> c'" unfolding zdef by linarith
  qed
  have final: "Sup (F y ` C) < c" if yU: "y \<in> U" for y
    using key[OF yU] c2 by linarith
  have ballU: "\<forall>y \<in> U. Sup (F y ` C) < c" by (intro ballI) (rule final)
  show ?thesis
    unfolding eventually_nhds
    by (rule exI[of _ U]) (intro conjI openU xinU ballU)
qed

section \<open>Feeding \<open>box\<close> from a sequential statement\<close>

text \<open>
  \<open>usc_sup_over_compact\<close> asks for \<open>box\<close> topologically, but weak convergence
  of measures is naturally a statement about sequences -- the form of the
  AFP's Portmanteau theorems and of \<open>Section_2_Usc.etime_shift_box\<close>.

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
  text \<open>\<open>metrizable_space_def\<close> quantifies over the carrier as well as the metric,
    so the carrier has to be identified with \<open>topspace X\<close> afterwards rather than
    assumed to be it.\<close>
  obtain MXs dX where dX: "Metric_space MXs dX"
    and tX: "X = Metric_space.mtopology MXs dX"
    using mX unfolding metrizable_space_def by blast
  obtain MYs dY where dY: "Metric_space MYs dY"
    and tY: "Y = Metric_space.mtopology MYs dY"
    using mY unfolding metrizable_space_def by blast
  interpret MX: Metric_space MXs dX by (rule dX)
  interpret MY: Metric_space MYs dY by (rule dY)
  have tsX: "topspace X = MXs" unfolding tX by (rule MX.topspace_mtopology)
  have tsY: "topspace Y = MYs" unfolding tY by (rule MY.topspace_mtopology)
  have xM: "x \<in> MXs" using x tsX by simp
  have PM: "P \<in> MYs" using P tsY by simp

  have pick: "\<exists>z W. z \<in> MX.mball x (1 / Suc n)
      \<and> W \<in> MY.mball P (1 / Suc n) \<and> W \<in> S \<and> \<not> R z W" for n :: nat
  proof -
    have oU: "openin X (MX.mball x (1 / Suc n))"
      unfolding tX by (rule MX.openin_mball)
    have oV: "openin Y (MY.mball P (1 / Suc n))"
      unfolding tY by (rule MY.openin_mball)
    have xU: "x \<in> MX.mball x (1 / Suc n)" using xM by simp
    have PV: "P \<in> MY.mball P (1 / Suc n)" using PM by simp
    show ?thesis using neg oU oV xU PV by blast
  qed
  obtain y Q where yQ: "\<And>n. y n \<in> MX.mball x (1 / Suc n)"
    "\<And>n. Q n \<in> MY.mball P (1 / Suc n)" "\<And>n. Q n \<in> S"
    "\<And>n. \<not> R (y n) (Q n)"
    using pick by metis

  have limy: "limitin X y x sequentially"
  proof -
    have "limitin MX.mtopology y x sequentially"
      unfolding MX.limitin_metric
    proof (intro conjI allI impI xM)
      fix e :: real assume e: "0 < e"
      obtain N :: nat where N: "1 / Suc N < e" using e nat_approx_posE by blast
      have "y n \<in> MXs \<and> dX (y n) x < e" if n: "N \<le> n" for n
      proof -
        have lt: "dX x (y n) < 1 / Suc n"
          using yQ(1)[of n] unfolding MX.mball_def by simp
        have "(1::real) / Suc n \<le> 1 / Suc N" using n by (simp add: frac_le)
        with lt N have "dX x (y n) < e" by linarith
        thus ?thesis
          using yQ(1)[of n] unfolding MX.mball_def by (simp add: MX.commute)
      qed
      thus "eventually (\<lambda>n. y n \<in> MXs \<and> dX (y n) x < e) sequentially"
        unfolding eventually_sequentially by blast
    qed
    thus ?thesis unfolding tX .
  qed
  have limQ: "limitin Y Q P sequentially"
  proof -
    have "limitin MY.mtopology Q P sequentially"
      unfolding MY.limitin_metric
    proof (intro conjI allI impI PM)
      fix e :: real assume e: "0 < e"
      obtain N :: nat where N: "1 / Suc N < e" using e nat_approx_posE by blast
      have "Q n \<in> MYs \<and> dY (Q n) P < e" if n: "N \<le> n" for n
      proof -
        have lt: "dY P (Q n) < 1 / Suc n"
          using yQ(2)[of n] unfolding MY.mball_def by simp
        have "(1::real) / Suc n \<le> 1 / Suc N" using n by (simp add: frac_le)
        with lt N have "dY P (Q n) < e" by linarith
        thus ?thesis
          using yQ(2)[of n] unfolding MY.mball_def by (simp add: MY.commute)
      qed
      thus "eventually (\<lambda>n. Q n \<in> MYs \<and> dY (Q n) P < e) sequentially"
        unfolding eventually_sequentially by blast
    qed
    thus ?thesis unfolding tY .
  qed
  from seq[OF limy limQ yQ(3)]
  have "eventually (\<lambda>i. R (y i) (Q i)) sequentially" .
  thus False using yQ(4) by simp
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
  The glue between Lemmas 2.2/2.3 of the paper and Berge. Those lemmas
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
  obtain MYs dY where dY: "Metric_space MYs dY"
    and tY: "Y = Metric_space.mtopology MYs dY"
    using mY unfolding metrizable_space_def by blast
  interpret MY: Metric_space MYs dY by (rule dY)
  have tsY: "topspace Y = MYs" unfolding tY by (rule MY.topspace_mtopology)
  have "compactin MY.mtopology C"
    unfolding MY.compactin_sequentially
  proof
    show "C \<subseteq> MYs" using sub tsY by simp
  next
    show "\<forall>\<sigma>::nat \<Rightarrow> 'b. range \<sigma> \<subseteq> C \<longrightarrow>
        (\<exists>l r. l \<in> C \<and> strict_mono r
             \<and> limitin MY.mtopology (\<sigma> \<circ> r) l sequentially)"
      using seq unfolding tY[symmetric] by blast
  qed
  thus ?thesis unfolding tY .
qed

text \<open>Two closure companions, both for a metrizable topology: a point of the
  closure of \<open>A\<close> is a sequential limit of points of \<open>A\<close>; and -- the form
  Lemma 2.3 consumes -- subsequence extraction on \<open>A\<close> extends to its
  closure, by approximating the given sequence within \<open>1/(n+1)\<close> and carrying
  the extracted limit across via the triangle inequality.\<close>

lemma closure_of_sequential_limit:
  fixes Y :: "'b topology" and A :: "'b set"
  assumes mY: "metrizable_space Y"
    and Q: "Q \<in> Y closure_of A"
  shows "\<exists>\<sigma>. range \<sigma> \<subseteq> A \<and> limitin Y \<sigma> Q sequentially"
proof -
  obtain MYs dY where dY: "Metric_space MYs dY"
    and tY: "Y = Metric_space.mtopology MYs dY"
    using mY unfolding metrizable_space_def by blast
  interpret MY: Metric_space MYs dY by (rule dY)
  have QM: "Q \<in> MYs" and near: "\<And>\<rho>. 0 < \<rho> \<Longrightarrow> \<exists>y\<in>A. y \<in> MY.mball Q \<rho>"
    using Q unfolding tY MY.metric_closure_of by auto
  have apx: "\<exists>y. y \<in> A \<and> y \<in> MYs \<and> dY Q y < 1 / real (Suc n)" for n
  proof -
    have "0 < 1 / real (Suc n)" by simp
    from near[OF this] obtain y where "y \<in> A" "y \<in> MY.mball Q (1 / real (Suc n))"
      by blast
    then show ?thesis by auto
  qed
  define \<sigma> where "\<sigma> = (\<lambda>n. SOME y. y \<in> A \<and> y \<in> MYs
      \<and> dY Q y < 1 / real (Suc n))"
  have \<sigma>A: "\<sigma> n \<in> A" and \<sigma>M: "\<sigma> n \<in> MYs"
    and \<sigma>d: "dY Q (\<sigma> n) < 1 / real (Suc n)" for n
    using someI_ex[OF apx[of n]] by (auto simp: \<sigma>_def)
  have "limitin MY.mtopology \<sigma> Q sequentially"
    unfolding MY.limitin_metric
  proof (intro conjI QM allI impI)
    fix \<epsilon> :: real assume e: "0 < \<epsilon>"
    obtain n0 where n0: "1 / real (Suc n0) < \<epsilon>"
      using e nat_approx_posE by blast
    show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> MYs \<and> dY (\<sigma> n) Q < \<epsilon>"
    proof (intro eventually_sequentiallyI[of n0] conjI \<sigma>M)
      fix n assume n: "n0 \<le> n"
      have "dY (\<sigma> n) Q = dY Q (\<sigma> n)" by (rule MY.commute)
      also have "\<dots> < 1 / real (Suc n)" by (rule \<sigma>d)
      also have "\<dots> \<le> 1 / real (Suc n0)"
        using n by (intro divide_left_mono) auto
      also have "\<dots> < \<epsilon>" by (rule n0)
      finally show "dY (\<sigma> n) Q < \<epsilon>" .
    qed
  qed
  then show ?thesis using \<sigma>A unfolding tY by blast
qed

lemma seq_compact_closure_of:
  fixes Y :: "'b topology" and A :: "'b set" and \<tau> :: "nat \<Rightarrow> 'b"
  assumes mY: "metrizable_space Y" and sub: "A \<subseteq> topspace Y"
    and seq: "\<And>\<sigma> :: nat \<Rightarrow> 'b. range \<sigma> \<subseteq> A \<Longrightarrow>
        \<exists>l r. l \<in> topspace Y \<and> strict_mono r \<and> limitin Y (\<sigma> \<circ> r) l sequentially"
    and rng: "range \<tau> \<subseteq> Y closure_of A"
  shows "\<exists>l r. l \<in> Y closure_of A \<and> strict_mono r
      \<and> limitin Y (\<tau> \<circ> r) l sequentially"
proof -
  obtain MYs dY where dY: "Metric_space MYs dY"
    and tY: "Y = Metric_space.mtopology MYs dY"
    using mY unfolding metrizable_space_def by blast
  interpret MY: Metric_space MYs dY by (rule dY)
  have tsY: "topspace Y = MYs" unfolding tY by (rule MY.topspace_mtopology)
  have \<tau>M: "\<tau> n \<in> MYs" and near: "\<And>\<rho>. 0 < \<rho> \<Longrightarrow> \<exists>y\<in>A. y \<in> MY.mball (\<tau> n) \<rho>" for n
    using rng unfolding tY MY.metric_closure_of by auto
  have apx: "\<exists>y. y \<in> A \<and> y \<in> MYs \<and> dY (\<tau> n) y < 1 / real (Suc n)" for n
  proof -
    have "0 < 1 / real (Suc n)" by simp
    from near[OF this] obtain y where "y \<in> A" "y \<in> MY.mball (\<tau> n) (1 / real (Suc n))"
      by blast
    then show ?thesis by auto
  qed
  define a where "a = (\<lambda>n. SOME y. y \<in> A \<and> y \<in> MYs
      \<and> dY (\<tau> n) y < 1 / real (Suc n))"
  have aA: "a n \<in> A" and aM: "a n \<in> MYs"
    and ad: "dY (\<tau> n) (a n) < 1 / real (Suc n)" for n
    using someI_ex[OF apx[of n]] by (auto simp: a_def)
  have raA: "range a \<subseteq> A" using aA by blast
  obtain l r where l: "l \<in> topspace Y" and r: "strict_mono r"
    and lim: "limitin Y (a \<circ> r) l sequentially"
    using seq[OF raA] by blast
  have lM: "l \<in> MYs" using l tsY by simp
  have limM: "limitin MY.mtopology (a \<circ> r) l sequentially"
    using lim unfolding tY .
  have lim\<tau>: "limitin MY.mtopology (\<tau> \<circ> r) l sequentially"
    unfolding MY.limitin_metric
  proof (intro conjI lM allI impI)
    fix \<epsilon> :: real assume e: "0 < \<epsilon>"
    have e2: "0 < \<epsilon> / 2" using e by simp
    have ev1: "\<forall>\<^sub>F n in sequentially. (a \<circ> r) n \<in> MYs \<and> dY ((a \<circ> r) n) l < \<epsilon> / 2"
      using limM e2 unfolding MY.limitin_metric by blast
    obtain n0 where n0: "1 / real (Suc n0) < \<epsilon> / 2"
      using e2 nat_approx_posE by blast
    have ev2: "\<forall>\<^sub>F n in sequentially. dY (\<tau> (r n)) (a (r n)) < \<epsilon> / 2"
    proof (intro eventually_sequentiallyI[of n0])
      fix n assume n: "n0 \<le> n"
      have "dY (\<tau> (r n)) (a (r n)) < 1 / real (Suc (r n))" by (rule ad)
      also have "\<dots> \<le> 1 / real (Suc n)"
        using seq_suble[OF r, of n] by (intro divide_left_mono) auto
      also have "\<dots> \<le> 1 / real (Suc n0)"
        using n by (intro divide_left_mono) auto
      also have "\<dots> < \<epsilon> / 2" by (rule n0)
      finally show "dY (\<tau> (r n)) (a (r n)) < \<epsilon> / 2" .
    qed
    show "\<forall>\<^sub>F n in sequentially. (\<tau> \<circ> r) n \<in> MYs \<and> dY ((\<tau> \<circ> r) n) l < \<epsilon>"
      using ev1 ev2
    proof eventually_elim
      case (elim n)
      have "dY (\<tau> (r n)) l \<le> dY (\<tau> (r n)) (a (r n)) + dY (a (r n)) l"
        by (intro MY.triangle \<tau>M aM lM)
      also have "\<dots> < \<epsilon> / 2 + \<epsilon> / 2"
        using elim by (intro add_strict_mono) (auto simp: o_def)
      finally show ?case using \<tau>M by (simp add: o_def)
    qed
  qed
  have lcl: "l \<in> Y closure_of A"
    unfolding tY MY.metric_closure_of
  proof (intro CollectI conjI lM allI impI)
    fix \<rho> :: real assume \<rho>: "0 < \<rho>"
    have "\<forall>\<^sub>F n in sequentially. (a \<circ> r) n \<in> MYs \<and> dY ((a \<circ> r) n) l < \<rho>"
      using limM \<rho> unfolding MY.limitin_metric by blast
    then obtain n where n: "a (r n) \<in> MYs" "dY (a (r n)) l < \<rho>"
      unfolding eventually_sequentially o_def by blast
    have "a (r n) \<in> MY.mball l \<rho>"
      using n lM by (auto simp: MY.commute)
    then show "\<exists>y\<in>A. y \<in> MY.mball l \<rho>"
      using aA by blast
  qed
  show ?thesis
    using lcl r lim\<tau> unfolding tY by blast
qed

section \<open>Berge over a \<open>topology\<close>-valued index space\<close>

text \<open>
  \<open>usc_sup_over_compact\<close> is stated with type-class \<open>open\<close>/\<open>compact\<close> on both
  factors -- fine for \<open>x\<close> in \<open>real^'n\<close>, but not for the laws: the weak
  topology is a \<open>topology\<close> value (\<open>weak_conv_topology\<close>), not a type-class
  instance, since different base spaces induce different weak topologies on
  the same type \<open>'a measure\<close>.

  So the second factor is re-stated with \<open>openin\<close>/\<open>compactin\<close>. Only the
  covering argument changes: \<open>compactinD\<close> hands back a finite set of opens
  rather than a finite index set, recovered via \<open>finite_subset_image\<close>. The
  conclusion stays in the type class, being about \<open>nhds x\<close>.
\<close>

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

end
