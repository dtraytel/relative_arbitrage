section \<open>The finite-dimensional distributions and their projectivity\<close>

(*<*)
theory Brownian_Finite_Dimensional_Distributions
  imports Gaussian_Increments
begin

(*>*)

section \<open>Finite-dimensional distributions\<close>

text \<open>For a finite set \<open>J\<close> of times, the Brownian finite-dimensional
  distribution is the pushforward of the product of independent Gaussian
  increment measures (one per time, with variance the gap to the previous
  time) under the cumulative-sum map.  Indexing the increment product by the
  times themselves avoids all list/index bookkeeping in the product measure.\<close>

definition prevt :: "real \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real" where
  "prevt t J s = Max (insert t {u \<in> J. u < s})"

definition inc_prod :: "real \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real) measure" where
  "inc_prod t J = Pi\<^sub>M J (\<lambda>s. gauss_measure (s - prevt t J s))"

definition csum :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "csum J \<omega> = (\<lambda>t\<in>J. \<Sum>u\<in>{u \<in> J. u \<le> t}. \<omega> u)"

definition bm_fdd :: "real set \<Rightarrow> (real \<Rightarrow> real) measure" where
  "bm_fdd J = distr (inc_prod 0 J) (Pi\<^sub>M J (\<lambda>_. borel)) (csum J)"

lemma sets_inc_prod [simp, measurable_cong]:
  "sets (inc_prod t J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  unfolding inc_prod_def by (rule sets_PiM_cong) simp_all

lemma prob_space_inc_prod [intro, simp]: "prob_space (inc_prod t J)"
  unfolding inc_prod_def by (intro prob_space_PiM prob_space_gauss_measure)

lemma measurable_csum [measurable]:
  "csum J \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  unfolding csum_def
  by (intro measurable_restrict borel_measurable_sum
      measurable_component_singleton) auto

lemma measurable_csum_inc_prod [measurable]:
  "csum J \<in> inc_prod t J \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  by (subst measurable_cong_sets[OF sets_inc_prod refl])
    (rule measurable_csum)

lemma sets_bm_fdd [simp]:
  "sets (bm_fdd J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  by (simp add: bm_fdd_def)

lemma space_bm_fdd:
  "space (bm_fdd J) = space (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  by (rule sets_eq_imp_space_eq) simp

lemma prob_space_bm_fdd [intro, simp]: "prob_space (bm_fdd J)"
  unfolding bm_fdd_def
  by (intro prob_space.prob_space_distr prob_space_inc_prod
      measurable_csum_inc_prod)

subsection \<open>The nested-integral kernel of the FDDs\<close>

text \<open>\<open>wr t x ps\<close> is the probability that a Brownian path started at time
  \<open>t\<close> in position \<open>x\<close> passes through the window \<open>A\<close> at each time \<open>s\<close>, for
  \<open>(s, A)\<close> in the list \<open>ps\<close> --- written as iterated Gaussian integrals.\<close>

fun wr :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real set) list \<Rightarrow> ennreal" where
  "wr t x [] = 1"
| "wr t x ((s, A) # ps) =
    (\<integral>\<^sup>+z. indicator A (x + z) * wr s (x + z) ps
     \<partial>gauss_measure (s - t))"

lemma wr_measurable:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> snd p \<in> sets borel"
  shows "(\<lambda>x. wr t x ps) \<in> borel_measurable (borel :: real measure)"
  using assms
proof (induction ps arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain s A where p [simp]: "p = (s, A)" by (cases p)
  from Cons.prems have A [measurable]: "A \<in> sets borel" by force
  have rec [measurable]: "(\<lambda>x. wr s x ps) \<in> borel_measurable borel"
    using Cons.prems by (intro Cons.IH) auto
  interpret G: sigma_finite_measure "gauss_measure (s - t)"
    by simp
  have "(\<lambda>(x, z). indicator A (x + z) * wr s (x + z) ps)
      \<in> borel_measurable (borel \<Otimes>\<^sub>M gauss_measure (s - t))"
    by measurable
  then have "(\<lambda>x. \<integral>\<^sup>+z. indicator A (x + z) * wr s (x + z) ps
      \<partial>gauss_measure (s - t)) \<in> borel_measurable borel"
    by (rule G.borel_measurable_nn_integral)
  then show ?case by simp
qed

subsection \<open>Marginalization: inserting an unconstrained time\<close>

fun ins :: "real \<Rightarrow> (real \<times> real set) list \<Rightarrow> (real \<times> real set) list" where
  "ins s [] = [(s, UNIV)]"
| "ins s (p # ps) = (if s < fst p then (s, UNIV) # p # ps else p # ins s ps)"

text \<open>The heart of projectivity: integrating out an unconstrained time
  merges two adjacent Gaussian increments, which is the convolution law.\<close>

lemma wr_ins:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> snd p \<in> sets borel"
    and "t \<le> s"
  shows "wr t x (ins s ps) = wr t x ps"
  using assms
proof (induction ps arbitrary: t x)
  case Nil
  interpret G: prob_space "gauss_measure (s - t)" by simp
  show ?case
    using G.emeasure_space_1
    by (simp add: indicator_def)
next
  case (Cons p ps)
  obtain u A where p [simp]: "p = (u, A)" by (cases p)
  from Cons.prems have A [measurable]: "A \<in> sets borel" by force
  have ps_sets: "\<And>q. q \<in> set ps \<Longrightarrow> snd q \<in> sets borel"
    using Cons.prems by auto
  show ?case
  proof (cases "s < u")
    case True
    have wrm [measurable]: "(\<lambda>y. wr u y ps) \<in> borel_measurable borel"
      by (rule wr_measurable) fact
    have fmeas: "(\<lambda>y. indicator A (x + y) * wr u (x + y) ps)
        \<in> borel_measurable (borel :: real measure)"
      by measurable
    have "wr t x (ins s (p # ps))
        = (\<integral>\<^sup>+z. indicator (UNIV :: real set) (x + z) * wr s (x + z) (p # ps)
           \<partial>gauss_measure (s - t))"
      using True by simp
    also have "\<dots> = (\<integral>\<^sup>+z. \<integral>\<^sup>+w. indicator A (x + (z + w)) * wr u (x + (z + w)) ps
        \<partial>gauss_measure (u - s) \<partial>gauss_measure (s - t))"
      by (simp add: indicator_def add_ac)
    also have "\<dots> = (\<integral>\<^sup>+y. indicator A (x + y) * wr u (x + y) ps
        \<partial>gauss_measure ((s - t) + (u - s)))"
      by (rule gauss_measure_conv_nn
          [where f = "\<lambda>y. indicator A (x + y) * wr u (x + y) ps"])
        (use True \<open>t \<le> s\<close> fmeas in auto)
    also have "\<dots> = wr t x (p # ps)"
      by simp
    finally show ?thesis .
  next
    case False
    then have us: "u \<le> s" by simp
    have IH': "\<And>y. wr u y (ins s ps) = wr u y ps"
      using ps_sets us by (intro Cons.IH) auto
    have "wr t x (ins s (p # ps))
        = (\<integral>\<^sup>+z. indicator A (x + z) * wr u (x + z) (ins s ps)
           \<partial>gauss_measure (u - t))"
      using False by simp
    also have "\<dots> = (\<integral>\<^sup>+z. indicator A (x + z) * wr u (x + z) ps
        \<partial>gauss_measure (u - t))"
      by (intro nn_integral_cong) (simp add: IH')
    also have "\<dots> = wr t x (p # ps)"
      by simp
    finally show ?thesis .
  qed
qed

subsection \<open>Rectangle emeasure formula\<close>

text \<open>\<open>prod_indicator_conj\<close> lives in @{theory Wiener_Measure.Sorted_Lists}.\<close>

lemma sumprod_measurable:
  fixes Mm :: "real \<Rightarrow> real measure"
  assumes Mm: "\<And>s. sets (Mm s) = sets borel"
    and A: "\<And>s. s \<in> J \<Longrightarrow> A s \<in> sets borel"
  shows "(\<lambda>\<omega>. \<Prod>s\<in>J. (indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))
          :: ennreal)) \<in> borel_measurable (Pi\<^sub>M J Mm)"
proof (rule borel_measurable_prod_ennreal)
  fix s assume s: "s \<in> J"
  have comp: "(\<lambda>\<omega>. \<omega> u) \<in> borel_measurable (Pi\<^sub>M J Mm)"
    if u: "u \<in> {u \<in> J. u \<le> s}" for u
  proof -
    from u have "u \<in> J" by blast
    then have "(\<lambda>\<omega>. \<omega> u) \<in> Pi\<^sub>M J Mm \<rightarrow>\<^sub>M Mm u"
      by (rule measurable_component_singleton)
    then show ?thesis
      by (simp add: measurable_cong_sets[OF refl Mm])
  qed
  have inner: "(\<lambda>\<omega>. x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))
      \<in> borel_measurable (Pi\<^sub>M J Mm)"
    by (intro borel_measurable_add borel_measurable_const
        borel_measurable_sum comp)
  show "(\<lambda>\<omega>. (indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))
      \<in> borel_measurable (Pi\<^sub>M J Mm)"
    by (rule measurable_compose[OF inner borel_measurable_indicator])
      (rule A[OF s])
qed

lemma inc_prod_rect:
  "finite J \<Longrightarrow> \<forall>s\<in>J. t \<le> s \<Longrightarrow> \<forall>s\<in>J. A s \<in> sets borel \<Longrightarrow>
   (\<integral>\<^sup>+\<omega>. (\<Prod>s\<in>J. indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)))
     \<partial>inc_prod t J)
   = wr t x (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
proof (induction J arbitrary: t x rule: finite_psubset_induct)
  case (psubset J)
  note finJ = psubset.hyps
  note lower = psubset.prems(1)
  note Asets = psubset.prems(2)
  show ?case
  proof (cases "J = {}")
    case True
    interpret E: prob_space "inc_prod t J" by simp
    show ?thesis
      using E.emeasure_space_1
      by (simp add: True)
  next
    case False
    define t0 where "t0 = Min J"
    define J' where "J' = J - {t0}"
    have t0J: "t0 \<in> J"
      using False finJ by (simp add: t0_def)
    have t0min: "\<And>s. s \<in> J \<Longrightarrow> t0 \<le> s"
      using finJ by (simp add: t0_def)
    have Jins: "J = insert t0 J'"
      using t0J by (auto simp: J'_def)
    have finJ': "finite J'" and t0J': "t0 \<notin> J'"
      using finJ by (auto simp: J'_def)
    have J'less: "\<And>s. s \<in> J' \<Longrightarrow> t0 < s"
      using t0min by (auto simp: J'_def order_less_le)
    have tt0: "t \<le> t0"
      using lower t0J by simp
    let ?M = "\<lambda>s. gauss_measure (s - prevt t J s)"
    let ?f = "\<lambda>w. \<Prod>s\<in>J. (indicator (A s)
        (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. w u)) :: ennreal)"
    let ?rest = "map (\<lambda>s. (s, A s)) (sorted_list_of_set J')"
    interpret PSF: product_sigma_finite ?M
      by (intro product_sigma_finite.intro sigma_finite_gauss_measure)
    have J'sub: "J' \<subset> J"
      using t0J by (auto simp: J'_def)
    have f_meas: "?f \<in> borel_measurable (Pi\<^sub>M J ?M)"
      using Asets by (intro sumprod_measurable) auto
    have prevt_t0: "prevt t J t0 = t"
    proof -
      have e: "{u \<in> J. u < t0} = {}"
        using t0min by fastforce
      show ?thesis unfolding prevt_def e by simp
    qed
    have prevt_eq: "\<And>s. s \<in> J' \<Longrightarrow> prevt t J s = prevt t0 J' s"
    proof -
      fix s assume s: "s \<in> J'"
      have below: "{u \<in> J. u < s} = insert t0 {u \<in> J'. u < s}"
        using J'less[OF s] t0J by (auto simp: J'_def)
      have fin': "finite (insert t0 {u \<in> J'. u < s})"
        using finJ' by simp
      have "prevt t J s = max t (Max (insert t0 {u \<in> J'. u < s}))"
        by (simp add: prevt_def below Max_insert[OF fin'])
      also have "\<dots> = Max (insert t0 {u \<in> J'. u < s})"
        using tt0 fin' by (intro max_absorb2 order_trans[OF tt0 Max_ge]) auto
      also have "\<dots> = prevt t0 J' s"
        by (simp add: prevt_def)
      finally show "prevt t J s = prevt t0 J' s" .
    qed
    have PiM_J': "Pi\<^sub>M J' ?M = inc_prod t0 J'"
      unfolding inc_prod_def
      by (rule PiM_cong[OF refl]) (simp add: prevt_eq)
    have sum_t0: "{u \<in> J. u \<le> t0} = {t0}"
      using t0J t0min by (auto intro: antisym)
    have sum_ins: "\<And>s. s \<in> J' \<Longrightarrow> {u \<in> J. u \<le> s} = insert t0 {u \<in> J'. u \<le> s}"
      using t0min t0J by (auto simp: J'_def)
    have inner: "?f (w(t0 := z)) = indicator (A t0) (x + z) *
        (\<Prod>s\<in>J'. (indicator (A s)
          ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))" for z w
    proof -
      have sum_eq: "(\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
          = z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)" if s: "s \<in> J'" for s
      proof -
        have fin'': "finite {u \<in> J'. u \<le> s}" using finJ' by simp
        have notin: "t0 \<notin> {u \<in> J'. u \<le> s}" using t0J' by simp
        have "(\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
            = (\<Sum>u\<in>insert t0 {u \<in> J'. u \<le> s}. (w(t0 := z)) u)"
          by (simp add: sum_ins[OF s])
        also have "\<dots> = z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. (w(t0 := z)) u)"
          by (simp add: sum.insert[OF fin'' notin])
        also have "(\<Sum>u\<in>{u \<in> J'. u \<le> s}. (w(t0 := z)) u)
            = (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)"
          using t0J' by (intro sum.cong) auto
        finally show ?thesis .
      qed
      have "?f (w(t0 := z)) = (indicator (A t0)
          (x + (\<Sum>u\<in>{u \<in> J. u \<le> t0}. (w(t0 := z)) u)) :: ennreal) *
          (\<Prod>s\<in>J'. (indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal))"
        by (subst Jins) (rule prod.insert[OF finJ' t0J'])
      also have "(indicator (A t0)
          (x + (\<Sum>u\<in>{u \<in> J. u \<le> t0}. (w(t0 := z)) u)) :: ennreal)
          = indicator (A t0) (x + z)"
        by (simp add: sum_t0)
      also have "(\<Prod>s\<in>J'. (indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal))
          = (\<Prod>s\<in>J'. (indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))"
      proof (rule prod.cong[OF refl])
        fix s assume s: "s \<in> J'"
        have "x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
            = x + (z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))"
          using sum_eq[OF s] by (rule arg_cong[where f = "(+) x"])
        also have "\<dots> = (x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)"
          by (rule add.assoc[symmetric])
        finally show "(indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal)
            = indicator (A s) ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))"
          by (rule arg_cong[where f = "indicator (A s)"])
      qed
      finally show ?thesis .
    qed
    have g_meas: "\<And>z. (\<lambda>w. \<Prod>s\<in>J'. (indicator (A s)
        ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))
        \<in> borel_measurable (Pi\<^sub>M J' ?M)"
      using Asets by (intro sumprod_measurable) (auto simp: J'_def)
    have IH': "(\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
        (y + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>inc_prod t0 J')
        = wr t0 y ?rest" for y
      using J'less Asets
      by (intro psubset.IH[OF J'sub]) (auto simp: J'_def order_less_imp_le)
    have "(\<integral>\<^sup>+w. ?f w \<partial>inc_prod t J) = integral\<^sup>N (Pi\<^sub>M (insert t0 J') ?M) ?f"
      using Jins by (simp add: inc_prod_def)
    also have "\<dots> = (\<integral>\<^sup>+z. (\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M) \<partial>?M t0)"
      using f_meas Jins
      by (intro PSF.product_nn_integral_insert_rev[OF finJ' t0J']) simp
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
          ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M) \<partial>?M t0)"
    proof (rule nn_integral_cong)
      fix z :: real
      have "(\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M)
          = (\<integral>\<^sup>+w. indicator (A t0) (x + z) *
            (\<Prod>s\<in>J'. indicator (A s)
              ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)"
      proof (rule nn_integral_cong)
        fix v :: "real \<Rightarrow> real"
        show "?f (v(t0 := z)) = indicator (A t0) (x + z) *
            (\<Prod>s\<in>J'. indicator (A s)
              ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. v u)))"
          by (rule inner)
      qed
      also have "\<dots> = indicator (A t0) (x + z) *
          (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)"
        by (rule nn_integral_cmult) (rule g_meas)
      finally show "(\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M)
          = indicator (A t0) (x + z) *
          (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)" .
    qed
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        wr t0 (x + z) ?rest \<partial>?M t0)"
      by (intro nn_integral_cong) (simp add: PiM_J' IH')
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        wr t0 (x + z) ?rest \<partial>gauss_measure (t0 - t))"
      by (simp add: prevt_t0)
    also have "\<dots> = wr t x ((t0, A t0) # ?rest)"
      by simp
    also have "\<dots> = wr t x (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
    proof -
      have slos: "sorted_list_of_set J = t0 # sorted_list_of_set J'"
        unfolding t0_def J'_def using finJ False
        by (rule sorted_list_of_set_nonempty)
      show ?thesis by (simp add: slos)
    qed
    finally show ?thesis .
  qed
qed

lemma emeasure_bm_fdd:
  assumes fin: "finite J" and J: "J \<subseteq> {0..}"
    and A: "\<And>s. s \<in> J \<Longrightarrow> A s \<in> sets borel"
  shows "emeasure (bm_fdd J) (Pi\<^sub>E J A)
       = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
proof -
  have PiE_sets: "Pi\<^sub>E J A \<in> sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
    by (intro sets_PiM_I_finite fin A)
  have "emeasure (bm_fdd J) (Pi\<^sub>E J A)
      = emeasure (inc_prod 0 J)
        (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J))"
    unfolding bm_fdd_def
    by (rule emeasure_distr[OF measurable_csum_inc_prod PiE_sets])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator
      (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega> \<partial>inc_prod 0 J)"
    by (rule nn_integral_indicator[symmetric])
      (rule measurable_sets[OF measurable_csum_inc_prod PiE_sets])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<Prod>s\<in>J. indicator (A s)
      (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))) \<partial>inc_prod 0 J)"
  proof (rule nn_integral_cong)
    fix \<omega> assume \<omega>: "\<omega> \<in> space (inc_prod 0 J)"
    have mem: "csum J \<omega> \<in> Pi\<^sub>E J A
        \<longleftrightarrow> (\<forall>s\<in>J. (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u) \<in> A s)"
      by (auto simp: csum_def PiE_iff extensional_def)
    have "(\<Prod>s\<in>J. (indicator (A s)
          (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))
        = (if \<forall>s\<in>J. (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u) \<in> A s then 1 else 0)"
      by (simp add: prod_indicator_conj[OF fin])
    also have "\<dots> = indicator (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega>"
      using \<omega> mem by (auto simp: indicator_def)
    finally show "indicator (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega>
        = (\<Prod>s\<in>J. (indicator (A s)
          (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))" ..
  qed
  also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
    using fin J A by (intro inc_prod_rect) auto
  finally show ?thesis .
qed

subsection \<open>Projectivity\<close>

lemma map_pair_insort:
  "s \<notin> set xs \<Longrightarrow> B s = UNIV \<Longrightarrow>
   map (\<lambda>t. (t, B t)) (insort s xs) = ins s (map (\<lambda>t. (t, B t)) xs)"
  by (induction xs) auto

lemma wr_pairs_extend:
  "finite D \<Longrightarrow> finite J \<Longrightarrow> D \<inter> J = {} \<Longrightarrow> \<forall>s\<in>D. (0::real) \<le> s \<Longrightarrow>
   \<forall>s\<in>J. B s \<in> sets borel \<Longrightarrow> \<forall>s\<in>D. B s = UNIV \<Longrightarrow>
   wr 0 0 (map (\<lambda>s. (s, B s)) (sorted_list_of_set (J \<union> D)))
     = wr 0 0 (map (\<lambda>s. (s, B s)) (sorted_list_of_set J))"
proof (induction D rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert s D)
  have sJD: "s \<notin> J \<union> D"
    using insert.prems insert.hyps by auto
  have finJD: "finite (J \<union> D)"
    using insert.prems insert.hyps by auto
  have "J \<union> insert s D = insert s (J \<union> D)" by auto
  then have "sorted_list_of_set (J \<union> insert s D)
      = insort s (sorted_list_of_set (J \<union> D))"
    using finJD sJD by simp
  then have "map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> insert s D))
      = ins s (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
    using sJD insert.prems
    by (simp add: map_pair_insort set_sorted_list_of_set[OF finJD])
  moreover have "wr 0 0 (ins s (map (\<lambda>u. (u, B u))
      (sorted_list_of_set (J \<union> D))))
      = wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
  proof (rule wr_ins)
    fix p assume "p \<in> set (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
    then obtain u where u: "u \<in> J \<union> D" "p = (u, B u)"
      by (auto simp: set_sorted_list_of_set[OF finJD])
    then show "snd p \<in> sets borel"
      using insert.prems by auto
  next
    show "0 \<le> s" using insert.prems by simp
  qed
  moreover have "wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))
      = wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set J))"
    using insert.prems insert.hyps by (intro insert.IH) auto
  ultimately show ?case by simp
qed

theorem bm_fdd_projective:
  assumes JH: "J \<subseteq> H" and finH: "finite H" and H: "H \<subseteq> {0..}"
  shows "bm_fdd J
       = distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))
           (\<lambda>f. restrict f J)"
proof -
  have finJ: "finite J" using JH finH by (rule finite_subset)
  have J0: "J \<subseteq> {0..}" using JH H by blast
  interpret PJ: prob_space "bm_fdd J" by simp
  have restr_meas: "(\<lambda>f. restrict f J) \<in>
      bm_fdd H \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
    by (subst measurable_cong_sets[OF sets_bm_fdd refl])
      (rule measurable_restrict_subset[OF JH])
  show ?thesis
  proof (rule measure_eqI_PiM_finite[OF finJ])
    show "sets (bm_fdd J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by simp
    show "sets (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
        = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by simp
    show "range (\<lambda>_::nat. Pi\<^sub>E J (\<lambda>_. UNIV :: real set))
        \<subseteq> prod_algebra J (\<lambda>_. borel)"
      by (auto intro!: prod_algebraI_finite[OF finJ])
    show "(\<Union>i::nat. Pi\<^sub>E J (\<lambda>_. UNIV :: real set))
        = space (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by (auto simp: space_PiM)
    show "\<And>i::nat. emeasure (bm_fdd J) (Pi\<^sub>E J (\<lambda>_. UNIV)) \<noteq> \<infinity>"
      by simp
    fix A :: "real \<Rightarrow> real set"
    assume A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets borel"
    define A' where "A' s = (if s \<in> J then A s else (UNIV :: real set))" for s
    have A'H: "\<And>s. s \<in> H \<Longrightarrow> A' s \<in> sets borel"
      using A by (auto simp: A'_def)
    have space_H: "space (bm_fdd H) = space (Pi\<^sub>M H (\<lambda>_. (borel :: real measure)))"
      by (rule space_bm_fdd)
    have restr_pre: "(\<lambda>f. restrict f J) -` Pi\<^sub>E J A \<inter> space (bm_fdd H)
        = Pi\<^sub>E H A'"
    proof (intro equalityI subsetI)
      fix f assume "f \<in> (\<lambda>f. restrict f J) -` Pi\<^sub>E J A \<inter> space (bm_fdd H)"
      then have f: "restrict f J \<in> Pi\<^sub>E J A"
        and fsp: "f \<in> Pi\<^sub>E H (\<lambda>_. UNIV :: real set)"
        by (auto simp: space_H space_PiM)
      have "f s \<in> A' s" if sH: "s \<in> H" for s
      proof (cases "s \<in> J")
        case True
        then have "restrict f J s \<in> A s"
          using f by (auto simp: PiE_iff)
        then show ?thesis using True by (simp add: A'_def)
      next
        case False
        then show ?thesis by (simp add: A'_def)
      qed
      with fsp show "f \<in> Pi\<^sub>E H A'"
        by (auto simp: PiE_iff)
    next
      fix f assume fH: "f \<in> Pi\<^sub>E H A'"
      then have vals: "\<And>s. s \<in> H \<Longrightarrow> f s \<in> A' s"
        by (auto simp: PiE_iff)
      have "restrict f J \<in> Pi\<^sub>E J A"
      proof (rule PiE_I)
        fix s assume sJ: "s \<in> J"
        have "f s \<in> A' s" using vals JH sJ by blast
        then show "restrict f J s \<in> A s"
          using sJ by (simp add: A'_def)
      next
        fix s assume "s \<notin> J"
        then show "restrict f J s = undefined" by simp
      qed
      moreover have "f \<in> space (bm_fdd H)"
        using fH by (auto simp: space_H space_PiM PiE_iff)
      ultimately show "f \<in> (\<lambda>f. restrict f J) -` Pi\<^sub>E J A
          \<inter> space (bm_fdd H)"
        by auto
    qed
    have "emeasure (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) (Pi\<^sub>E J A)
        = emeasure (bm_fdd H) ((\<lambda>f. restrict f J) -` Pi\<^sub>E J A
          \<inter> space (bm_fdd H))"
      by (rule emeasure_distr[OF restr_meas sets_PiM_I_finite[OF finJ A]])
    also have "\<dots> = emeasure (bm_fdd H) (Pi\<^sub>E H A')"
      unfolding restr_pre by (rule refl)
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A' s)) (sorted_list_of_set H))"
      by (rule emeasure_bm_fdd[OF finH H A'H])
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A' s)) (sorted_list_of_set J))"
    proof -
      have HJ: "H = J \<union> (H - J)" using JH by auto
      show ?thesis
        by (subst HJ)
          (intro wr_pairs_extend finJ, use finH H A JH in \<open>auto simp: A'_def\<close>)
    qed
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
      by (intro arg_cong[where f = "wr 0 0"] map_cong refl)
        (simp add: A'_def set_sorted_list_of_set[OF finJ])
    also have "\<dots> = emeasure (bm_fdd J) (Pi\<^sub>E J A)"
      by (rule emeasure_bm_fdd[OF finJ J0 A, symmetric])
    finally show "emeasure (bm_fdd J) (Pi\<^sub>E J A)
        = emeasure (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel))
          (\<lambda>f. restrict f J)) (Pi\<^sub>E J A)" ..
  qed
qed


(*<*)
end
(*>*)
