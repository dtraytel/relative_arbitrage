
(*<*)
theory Semicontinuous_Selection
  imports "HOL-Probability.Probability" "Standard_Borel_Spaces.Lemmas_StandardBorel"
begin

(*>*)

section \<open>A measurable selection theorem for upper semicontinuous payoffs\<close>

text \<open>A measurable selection theorem for upper semicontinuous payoffs on
  compact sets, in the form of Bertsekas--Shreve (1978), Prop. 7.33, which
  Larsson--Ruf's Proposition 2.2(ii) appeals to.  The construction is a
  greedy nested bisection along a countable dense sequence.\<close>

text \<open>A helper: @{typ ennreal} is densely ordered.  The instance is
  declared for @{typ ereal} but not for @{typ ennreal}.\<close>

lemma ennreal_strict_between:
  fixes a b :: ennreal
  assumes ab: "a < b"
  shows "\<exists>c. a < c \<and> c < b"
proof -
  have "enn2ereal a < enn2ereal b" using ab by (simp add: less_ennreal.rep_eq)
  then obtain e where e1: "enn2ereal a < e" and e2: "e < enn2ereal b"
    using dense by blast
  have "(0::ereal) \<le> enn2ereal a" by simp
  then have e0: "0 \<le> e" using order.strict_implies_order[OF e1] by (rule order_trans)
  have re: "enn2ereal (e2ennreal e) = e" by (rule enn2ereal_e2ennreal[OF e0])
  show ?thesis
  proof (intro exI[of _ "e2ennreal e"] conjI)
    show "a < e2ennreal e" using e1 by (simp add: less_ennreal.rep_eq re)
    show "e2ennreal e < b" using e2 by (simp add: less_ennreal.rep_eq re)
  qed
qed

text \<open>A compact metric space carries a dense sequence (it is nonempty, so
  the countable dense set can be enumerated).\<close>

lemma (in Metric_space) compact_space_dense_seq:
  assumes cpt: "compact_space mtopology" and ne: "M \<noteq> {}"
  shows "\<exists>z :: nat \<Rightarrow> 'a. (\<forall>j. z j \<in> M)
      \<and> (\<forall>y \<in> M. \<forall>e > 0. \<exists>j. d (z j) y < e)"
proof -
  have cover: "\<exists>K. finite K \<and> K \<subseteq> M \<and> M \<subseteq> (\<Union>x\<in>K. mball x e)" if e: "0 < e" for e
  proof -
    have "M \<subseteq> \<Union> ((\<lambda>x. mball x e) ` M)" using e by auto
    moreover have "openin mtopology U" if "U \<in> (\<lambda>x. mball x e) ` M" for U
      using that by auto
    ultimately obtain F where F: "finite F" "F \<subseteq> (\<lambda>x. mball x e) ` M"
        "M \<subseteq> \<Union>F"
      using cpt unfolding compact_space_alt by (metis topspace_mtopology)
    from F(2) obtain K where K: "K \<subseteq> M" "finite K" "F = (\<lambda>x. mball x e) ` K"
      by (meson finite_subset_image F(1))
    show ?thesis using K F(3) by auto
  qed
  have "\<forall>n::nat. \<exists>K. finite K \<and> K \<subseteq> M \<and> M \<subseteq> (\<Union>x\<in>K. mball x ((1/2)^n))"
    by (intro allI cover) simp
  then obtain KK where KK: "\<And>n::nat. finite (KK n)" "\<And>n::nat. KK n \<subseteq> M"
      "\<And>n::nat. M \<subseteq> (\<Union>x\<in>KK n. mball x ((1/2)^n))"
    by metis
  define D where "D = (\<Union>n::nat. KK n)"
  have Dc: "countable D" unfolding D_def using KK(1) by (blast intro: countable_finite)
  have DM: "D \<subseteq> M" unfolding D_def using KK(2) by blast
  have Dne: "D \<noteq> {}"
  proof -
    from ne obtain y where y: "y \<in> M" by blast
    then obtain x where "x \<in> KK 0" using KK(3)[of 0] by auto
    then show ?thesis unfolding D_def by blast
  qed
  define z where "z = from_nat_into D"
  have zr: "range z = D" unfolding z_def by (rule range_from_nat_into[OF Dne Dc])
  have zM: "z j \<in> M" for j using zr DM by blast
  have zd: "\<exists>j. d (z j) y < e" if y: "y \<in> M" and e: "0 < e" for y e
  proof -
    have "(\<lambda>n. (1/2::real)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) auto
    then have "\<forall>\<^sub>F n in sequentially. (1/2::real)^n < e"
      using e by (rule order_tendstoD(2))
    then obtain n :: nat where n: "(1/2::real)^n < e"
      by (auto simp: eventually_sequentially)
    from KK(3)[of n] y obtain x where x: "x \<in> KK n" "y \<in> mball x ((1/2)^n)" by auto
    then have "d x y < (1/2)^n" by simp
    with n have "d x y < e" by simp
    moreover have "x \<in> D" unfolding D_def using x(1) by blast
    ultimately show ?thesis using zr by (metis rangeE)
  qed
  show ?thesis using zM zd by blast
qed

text \<open>The greedy construction: \<open>usc_sel_set Y dd z js\<close> is the set reached
  by the index sequence \<open>js\<close> (most recent first), \<open>usc_sel_good\<close> the
  greedy criterion, \<open>usc_sel_code\<close> the index sequence chosen for payoff
  \<open>g\<close>, and \<open>usc_sel\<close> the point the nested sets shrink to --- all
  parametrized by the carrier, distance and dense sequence, so no new
  locale is needed.\<close>

definition usc_sel_set ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat list \<Rightarrow> 'a set" where
  "usc_sel_set Y dd z
     = rec_list Y (\<lambda>j js S. {y \<in> S. dd (z j) y \<le> (1/2)^(Suc (length js))})"

lemma usc_sel_set_Nil [simp]: "usc_sel_set Y dd z [] = Y"
  by (simp add: usc_sel_set_def)

lemma usc_sel_set_Cons [simp]:
  "usc_sel_set Y dd z (j # js)
     = {y \<in> usc_sel_set Y dd z js. dd (z j) y \<le> (1/2)^(Suc (length js))}"
  by (simp add: usc_sel_set_def)

lemma usc_sel_set_subset: "usc_sel_set Y dd z js \<subseteq> Y"
  by (induct js) auto

lemma usc_sel_set_mono: "usc_sel_set Y dd z (j # js) \<subseteq> usc_sel_set Y dd z js"
  by auto

definition usc_sel_good ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "usc_sel_good Y dd z g js j \<longleftrightarrow>
     usc_sel_set Y dd z (j # js) \<noteq> {}
       \<and> Sup (g ` usc_sel_set Y dd z (j # js)) = Sup (g ` usc_sel_set Y dd z js)"

definition usc_sel_code ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow> nat list"
  where "usc_sel_code Y dd z g
     = rec_nat [] (\<lambda>n js. (LEAST j. usc_sel_good Y dd z g js j) # js)"

lemma usc_sel_code_0 [simp]: "usc_sel_code Y dd z g 0 = []"
  by (simp add: usc_sel_code_def)

lemma usc_sel_code_Suc [simp]:
  "usc_sel_code Y dd z g (Suc n)
     = (LEAST j. usc_sel_good Y dd z g (usc_sel_code Y dd z g n) j)
        # usc_sel_code Y dd z g n"
  by (simp add: usc_sel_code_def)

lemma length_usc_sel_code [simp]: "length (usc_sel_code Y dd z g n) = n"
  by (induct n) simp_all

definition usc_sel ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a" where
  "usc_sel Y dd z g
     = (SOME y. y \<in> (\<Inter>n. usc_sel_set Y dd z (usc_sel_code Y dd z g n)))"

context Metric_space
begin

lemma usc_sel_set_closedin:
  assumes z: "\<And>j. z j \<in> M"
  shows "closedin mtopology (usc_sel_set M d z js)"
proof (induct js)
  case Nil
  show ?case by simp
next
  case (Cons j js)
  have eq: "usc_sel_set M d z (j # js)
      = usc_sel_set M d z js \<inter> mcball (z j) ((1/2)^(Suc (length js)))"
    using usc_sel_set_subset[of M d z js] z by auto
  show ?case unfolding eq by (rule closedin_Int[OF Cons closedin_mcball])
qed

lemma usc_sel_set_compactin:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
  shows "compactin mtopology (usc_sel_set M d z js)"
  by (rule closedin_compact_space[OF cpt usc_sel_set_closedin[OF z]])

text \<open>The greedy step always succeeds: the balls of the current radius
  cover the current compact set, so finitely many do, and the supremum
  over a finite union is the maximum of the pieces' suprema.  No
  semicontinuity is needed --- this holds for arbitrary \<open>g\<close>, making
  \<open>usc_sel\<close> total.\<close>

lemma usc_sel_good_ex:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "usc_sel_set M d z js \<noteq> {}"
  shows "\<exists>j. usc_sel_good M d z g js j"
proof -
  define S where "S = usc_sel_set M d z js"
  define r where "r = (1/2::real)^(Suc (length js))"
  have r0: "0 < r" unfolding r_def by simp
  have SM: "S \<subseteq> M" unfolding S_def by (rule usc_sel_set_subset)
  have Sne: "S \<noteq> {}" using ne unfolding S_def .
  have Scpt: "compactin mtopology S"
    unfolding S_def by (rule usc_sel_set_compactin[OF cpt z])
  have cov: "S \<subseteq> \<Union> (range (\<lambda>j. mball (z j) r))"
  proof
    fix y assume yS: "y \<in> S"
    then have yM: "y \<in> M" using SM by blast
    from dns[OF yM r0] obtain j where "d (z j) y < r" by blast
    then have "y \<in> mball (z j) r" using yM z by simp
    then show "y \<in> \<Union> (range (\<lambda>j. mball (z j) r))" by blast
  qed
  have opn: "openin mtopology U" if "U \<in> range (\<lambda>j. mball (z j) r)" for U
    using that by auto
  have "\<exists>F. finite F \<and> F \<subseteq> range (\<lambda>j. mball (z j) r) \<and> S \<subseteq> \<Union>F"
    using Scpt cov opn unfolding compactin_def by blast
  then obtain F where F: "finite F" "F \<subseteq> range (\<lambda>j. mball (z j) r)" "S \<subseteq> \<Union>F"
    by blast
  from F(1,2) obtain J0 :: "nat set" where J0: "finite J0"
      "F = (\<lambda>j. mball (z j) r) ` J0"
    by (meson finite_subset_image subset_UNIV)
  define J where "J = {j \<in> J0. S \<inter> mball (z j) r \<noteq> {}}"
  have Jfin: "finite J" unfolding J_def using J0(1) by simp
  have Scov: "S = (\<Union>j\<in>J. S \<inter> mball (z j) r)"
  proof
    show "S \<subseteq> (\<Union>j\<in>J. S \<inter> mball (z j) r)"
    proof
      fix y assume yS: "y \<in> S"
      with F(3) J0(2) obtain j where j: "j \<in> J0" "y \<in> mball (z j) r" by auto
      with yS have yj: "y \<in> S \<inter> mball (z j) r" by blast
      with j(1) have "j \<in> J" unfolding J_def by blast
      with yj show "y \<in> (\<Union>j\<in>J. S \<inter> mball (z j) r)" by blast
    qed
  qed blast
  have Jne: "J \<noteq> {}" using Scov Sne by auto
  define h where "h = (\<lambda>j. Sup (g ` (S \<inter> mball (z j) r)))"
  have supS: "Sup (g ` S) = Sup (h ` J)"
  proof (rule antisym)
    show "Sup (g ` S) \<le> Sup (h ` J)"
    proof (rule Sup_least)
      fix v assume "v \<in> g ` S"
      then obtain y where y: "y \<in> S" "v = g y" by blast
      then obtain j where j: "j \<in> J" "y \<in> S \<inter> mball (z j) r" using Scov by blast
      have "v \<le> h j" unfolding h_def using y j by (auto intro: Sup_upper)
      also have "\<dots> \<le> Sup (h ` J)" using j by (auto intro: Sup_upper)
      finally show "v \<le> Sup (h ` J)" .
    qed
    show "Sup (h ` J) \<le> Sup (g ` S)"
    proof (rule Sup_least)
      fix v assume "v \<in> h ` J"
      then obtain j where j: "j \<in> J" "v = h j" by blast
      have "h j \<le> Sup (g ` S)" unfolding h_def
        by (intro Sup_subset_mono image_mono) auto
      then show "v \<le> Sup (g ` S)" using j by simp
    qed
  qed
  have maxin: "Max (h ` J) \<in> h ` J" using Jne Jfin by simp
  have supmax: "Sup (h ` J) = Max (h ` J)"
  proof (rule antisym)
    show "Sup (h ` J) \<le> Max (h ` J)"
      using Jfin by (intro Sup_least) simp
    show "Max (h ` J) \<le> Sup (h ` J)" using maxin by (rule Sup_upper)
  qed
  from maxin obtain j0 where j0eq: "Max (h ` J) = h j0" and j0J: "j0 \<in> J"
    by (rule imageE)
  have j0: "j0 \<in> J" "h j0 = Max (h ` J)" using j0J j0eq by simp_all
  have sub: "S \<inter> mball (z j0) r \<subseteq> usc_sel_set M d z (j0 # js)"
    unfolding S_def r_def by auto
  have "usc_sel_good M d z g js j0"
    unfolding usc_sel_good_def
  proof
    from j0(1) have "S \<inter> mball (z j0) r \<noteq> {}" unfolding J_def by blast
    with sub show "usc_sel_set M d z (j0 # js) \<noteq> {}" by blast
  next
    show "Sup (g ` usc_sel_set M d z (j0 # js))
        = Sup (g ` usc_sel_set M d z js)"
    proof (rule antisym)
      show "Sup (g ` usc_sel_set M d z (j0 # js))
          \<le> Sup (g ` usc_sel_set M d z js)"
        by (intro Sup_subset_mono image_mono usc_sel_set_mono)
      have "Sup (g ` usc_sel_set M d z js) = h j0"
        using supS supmax j0 unfolding S_def by simp
      also have "\<dots> \<le> Sup (g ` usc_sel_set M d z (j0 # js))"
        unfolding h_def using sub by (intro Sup_subset_mono image_mono)
      finally show "Sup (g ` usc_sel_set M d z js)
          \<le> Sup (g ` usc_sel_set M d z (j0 # js))" .
    qed
  qed
  then show ?thesis ..
qed

text \<open>Along the code every set is nonempty and carries the full supremum:
  that is the whole point of the greedy criterion.\<close>

lemma usc_sel_code_set:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}
       \<and> Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) = Sup (g ` M)"
proof (induct n)
  case 0
  show ?case using ne by simp
next
  case (Suc n)
  then have ne': "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}" by blast
  have "usc_sel_good M d z g (usc_sel_code M d z g n)
      (LEAST j. usc_sel_good M d z g (usc_sel_code M d z g n) j)"
    by (rule LeastI_ex[OF usc_sel_good_ex[OF cpt z dns ne']])
  then show ?case using Suc by (simp add: usc_sel_good_def)
qed

lemma usc_sel_code_set_ne:
  assumes "compact_space mtopology" "\<And>j. z j \<in> M"
    "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e" "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}"
  using usc_sel_code_set[OF assms] by blast

lemma usc_sel_code_set_sup:
  assumes "compact_space mtopology" "\<And>j. z j \<in> M"
    "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e" "M \<noteq> {}"
  shows "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) = Sup (g ` M)"
  using usc_sel_code_set[OF assms] by blast

lemma usc_sel_code_mono:
  assumes mn: "m \<le> n"
  shows "usc_sel_set M d z (usc_sel_code M d z g n)
       \<subseteq> usc_sel_set M d z (usc_sel_code M d z g m)"
  using mn
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m \<le> n")
    case True
    have "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
        \<subseteq> usc_sel_set M d z (usc_sel_code M d z g n)" by auto
    with Suc.hyps[OF True] show ?thesis by blast
  next
    case False
    with Suc.prems have "m = Suc n" by simp
    then show ?thesis by simp
  qed
qed

lemma usc_sel_code_decseq:
  "decseq (\<lambda>n. usc_sel_set M d z (usc_sel_code M d z g n))"
  unfolding decseq_def using usc_sel_code_mono by blast

text \<open>The nested compact sets have a common point, and \<open>usc_sel\<close> is one.\<close>

lemma usc_sel_in_code_set:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel M d z g \<in> usc_sel_set M d z (usc_sel_code M d z g n)"
proof -
  have "(\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n)) \<noteq> {}"
  proof (rule compact_space_imp_nest[OF cpt])
    show "closedin mtopology (usc_sel_set M d z (usc_sel_code M d z g k))" for k
      by (rule usc_sel_set_closedin[OF z])
    show "usc_sel_set M d z (usc_sel_code M d z g k) \<noteq> {}" for k
      by (rule usc_sel_code_set_ne[OF cpt z dns ne])
    show "decseq (\<lambda>n. usc_sel_set M d z (usc_sel_code M d z g n))"
      by (rule usc_sel_code_decseq)
  qed
  then obtain y0 where "y0 \<in> (\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n))"
    by blast
  then have "usc_sel M d z g \<in> (\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n))"
    unfolding usc_sel_def by (rule someI)
  then show ?thesis by blast
qed

lemma usc_sel_in_M:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel M d z g \<in> M"
  using usc_sel_in_code_set[OF cpt z dns ne, of g 0] by simp

text \<open>The sets shrink: at stage \<open>Suc n\<close> everything is within \<open>2\<^sup>-\<^sup>n\<close> of the
  selected point, by the triangle inequality through the chosen centre.\<close>

lemma usc_sel_code_set_small:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
      \<subseteq> mcball (usc_sel M d z g) ((1/2)^n)"
proof -
  define jn where "jn = (LEAST j. usc_sel_good M d z g (usc_sel_code M d z g n) j)"
  have code: "usc_sel_code M d z g (Suc n) = jn # usc_sel_code M d z g n"
    unfolding jn_def by simp
  have zjn: "z jn \<in> M" by (rule z)
  have half: "d (z jn) w \<le> (1/2)^(Suc n)"
    if "w \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))" for w
    using that unfolding code by simp
  have sel: "usc_sel M d z g \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))"
    by (rule usc_sel_in_code_set[OF cpt z dns ne])
  have sM: "usc_sel M d z g \<in> M" by (rule usc_sel_in_M[OF cpt z dns ne])
  show ?thesis
  proof
    fix y assume y: "y \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))"
    have yM: "y \<in> M"
      using usc_sel_set_subset[of M d z "usc_sel_code M d z g (Suc n)"] y by blast
    have "d (usc_sel M d z g) y \<le> d (usc_sel M d z g) (z jn) + d (z jn) y"
      by (rule triangle[OF sM zjn yM])
    also have "\<dots> \<le> (1/2)^(Suc n) + (1/2)^(Suc n)"
      using half[OF sel] half[OF y] by (simp add: commute)
    also have "\<dots> = (1/2::real)^n" by simp
    finally show "y \<in> mcball (usc_sel M d z g) ((1/2)^n)"
      using sM yM by simp
  qed
qed

lemma usc_sel_code_set_in_open:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
    and U: "openin mtopology U" and mem: "usc_sel M d z g \<in> U"
  shows "\<exists>n. usc_sel_set M d z (usc_sel_code M d z g n) \<subseteq> U"
proof -
  from U mem obtain r where r: "0 < r" "mball (usc_sel M d z g) r \<subseteq> U"
    unfolding openin_mtopology by blast
  have "(\<lambda>n. (1/2::real)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) auto
  then have "\<forall>\<^sub>F n in sequentially. (1/2::real)^n < r"
    using r(1) by (rule order_tendstoD(2))
  then obtain n :: nat where n: "(1/2::real)^n < r"
    by (auto simp: eventually_sequentially)
  have "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
      \<subseteq> mcball (usc_sel M d z g) ((1/2)^n)"
    by (rule usc_sel_code_set_small[OF cpt z dns ne])
  also have "\<dots> \<subseteq> mball (usc_sel M d z g) r" using n by auto
  also have "\<dots> \<subseteq> U" by (rule r(2))
  finally show ?thesis by blast
qed

text \<open>Upper semicontinuity turns the shrinking into optimality.\<close>

lemma usc_sel_optimal:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
    and usc: "\<And>c. openin mtopology {y \<in> M. g y < c}"
  shows "g (usc_sel M d z g) = Sup (g ` M)"
proof (rule antisym)
  show "g (usc_sel M d z g) \<le> Sup (g ` M)"
    using usc_sel_in_M[OF cpt z dns ne] by (auto intro: Sup_upper)
  show "Sup (g ` M) \<le> g (usc_sel M d z g)"
  proof (rule ccontr)
    assume "\<not> Sup (g ` M) \<le> g (usc_sel M d z g)"
    then have lt: "g (usc_sel M d z g) < Sup (g ` M)" by simp
    then obtain c where c1: "g (usc_sel M d z g) < c" and c2: "c < Sup (g ` M)"
      using ennreal_strict_between by blast
    have Uopen: "openin mtopology {y \<in> M. g y < c}" by (rule usc)
    have Umem: "usc_sel M d z g \<in> {y \<in> M. g y < c}"
      using usc_sel_in_M[OF cpt z dns ne] c1 by simp
    from usc_sel_code_set_in_open[OF cpt z dns ne Uopen Umem]
    obtain n where n: "usc_sel_set M d z (usc_sel_code M d z g n)
        \<subseteq> {y \<in> M. g y < c}" by blast
    have "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) \<le> c"
    proof (rule Sup_least)
      fix v assume "v \<in> g ` usc_sel_set M d z (usc_sel_code M d z g n)"
      then obtain y where y: "y \<in> usc_sel_set M d z (usc_sel_code M d z g n)"
          "v = g y" by blast
      then have "g y < c" using n by blast
      then show "v \<le> c" using y by simp
    qed
    moreover have "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n))
        = Sup (g ` M)"
      by (rule usc_sel_code_set_sup[OF cpt z dns ne])
    ultimately show False using c2 by simp
  qed
qed

text \<open>A characterisation of @{term Least} on @{typ nat} that turns the
  greedy choice into a Boolean combination of countably many conditions.\<close>

lemma Least_nat_eq_iff:
  fixes Q :: "nat \<Rightarrow> bool"
  assumes ex: "\<exists>i. Q i"
  shows "((LEAST i. Q i) = j) \<longleftrightarrow> (Q j \<and> (\<forall>i<j. \<not> Q i))"
proof
  assume L: "(LEAST i. Q i) = j"
  have "Q (LEAST i. Q i)" using ex by (rule LeastI_ex)
  with L have Qj: "Q j" by simp
  have "\<not> Q i" if ij: "i < j" for i
  proof
    assume "Q i"
    then have "(LEAST i. Q i) \<le> i" by (rule Least_le)
    with L ij show False by simp
  qed
  with Qj show "Q j \<and> (\<forall>i<j. \<not> Q i)" by blast
next
  assume R: "Q j \<and> (\<forall>i<j. \<not> Q i)"
  show "(LEAST i. Q i) = j"
  proof (rule Least_equality)
    show "Q j" using R by blast
    show "j \<le> i" if "Q i" for i
    proof (rule ccontr)
      assume "\<not> j \<le> i"
      then have "i < j" by simp
      with R have "\<not> Q i" by blast
      with that show False by blast
    qed
  qed
qed

text \<open>The measurable selection theorem.  The payoff is upper semicontinuous
  in the second argument for every parameter, and its supremum over every
  closed set is measurable in the parameter --- the latter is what joint
  upper semicontinuity supplies in the intended application.\<close>

theorem usc_measurable_selection:
  fixes P :: "'b measure" and f :: "'b \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes cpt: "compact_space mtopology" and ne: "M \<noteq> {}"
    and usc: "\<And>x c. x \<in> space P \<Longrightarrow> openin mtopology {y \<in> M. f x y < c}"
    and meas: "\<And>C. closedin mtopology C
        \<Longrightarrow> (\<lambda>x. Sup (f x ` C)) \<in> borel_measurable P"
  obtains s where "s \<in> P \<rightarrow>\<^sub>M borel_of mtopology" and "\<And>x. s x \<in> M"
    and "\<And>x. x \<in> space P \<Longrightarrow> f x (s x) = Sup (f x ` M)"
proof -
  obtain z :: "nat \<Rightarrow> 'a" where z0: "\<forall>j. z j \<in> M"
    and dns0: "\<forall>y \<in> M. \<forall>e > 0. \<exists>j. d (z j) y < e"
    using compact_space_dense_seq[OF cpt ne] by blast
  have z: "z j \<in> M" for j using z0 by blast
  have dns: "\<exists>j. d (z j) y < e" if "y \<in> M" and "0 < e" for y e
    using dns0 that by blast
  define s where "s = (\<lambda>x. usc_sel M d z (f x))"
  have sM: "s x \<in> M" for x
    unfolding s_def by (rule usc_sel_in_M[OF cpt z dns ne])
  have sopt: "f x (s x) = Sup (f x ` M)" if x: "x \<in> space P" for x
    unfolding s_def by (rule usc_sel_optimal[OF cpt z dns ne usc[OF x]])
  define A where "A = (\<lambda>n js. {x \<in> space P. usc_sel_code M d z (f x) n = js})"
  have Gmeas: "{x \<in> space P. usc_sel_good M d z (f x) js i} \<in> sets P" for js i
  proof (cases "usc_sel_set M d z (i # js) = {}")
    case True
    have empty: "{x \<in> space P. usc_sel_good M d z (f x) js i} = {}"
      using True unfolding usc_sel_good_def by auto
    show ?thesis unfolding empty by simp
  next
    case False
    have eq: "{x \<in> space P. usc_sel_good M d z (f x) js i}
        = {x \<in> space P. Sup (f x ` usc_sel_set M d z (i # js))
             = Sup (f x ` usc_sel_set M d z js)}"
      using False unfolding usc_sel_good_def by auto
    have m1: "(\<lambda>x. Sup (f x ` usc_sel_set M d z (i # js))) \<in> borel_measurable P"
      by (rule meas[OF usc_sel_set_closedin[OF z]])
    have m2: "(\<lambda>x. Sup (f x ` usc_sel_set M d z js)) \<in> borel_measurable P"
      by (rule meas[OF usc_sel_set_closedin[OF z]])
    show ?thesis unfolding eq by (rule borel_measurable_eq[OF m1 m2])
  qed
  have Ameas: "A n js \<in> sets P" for n js
  proof (induct n arbitrary: js)
    case 0
    have "A 0 js = (if js = [] then space P else {})"
      unfolding A_def by auto
    then show ?case by simp
  next
    case (Suc n)
    show ?case
    proof (cases js)
      case Nil
      have "A (Suc n) [] = {}" unfolding A_def by auto
      with Nil show ?thesis by simp
    next
      case (Cons j js')
      have split: "A (Suc n) (j # js')
          = A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
      proof (intro set_eqI iffI)
        fix x assume "x \<in> A (Suc n) (j # js')"
        then have xP: "x \<in> space P"
          and e: "usc_sel_code M d z (f x) (Suc n) = j # js'"
          unfolding A_def by auto
        from e have c1: "usc_sel_code M d z (f x) n = js'" by simp
        from e have "(LEAST i. usc_sel_good M d z (f x) js' i) # js' = j # js'"
          by (simp only: usc_sel_code_Suc c1)
        then have c2: "(LEAST i. usc_sel_good M d z (f x) js' i) = j" by simp
        show "x \<in> A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
          using xP c1 c2 unfolding A_def by simp
      next
        fix x assume "x \<in> A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
        then have xP: "x \<in> space P" and c1: "usc_sel_code M d z (f x) n = js'"
          and c2: "(LEAST i. usc_sel_good M d z (f x) js' i) = j"
          unfolding A_def by auto
        have "usc_sel_code M d z (f x) (Suc n) = j # js'"
        proof -
          have "usc_sel_code M d z (f x) (Suc n)
              = (LEAST i. usc_sel_good M d z (f x)
                  (usc_sel_code M d z (f x) n) i) # usc_sel_code M d z (f x) n"
            by simp
          also have "\<dots> = (LEAST i. usc_sel_good M d z (f x) js' i) # js'"
            unfolding c1 by (rule refl)
          also have "\<dots> = j # js'" unfolding c2 by (rule refl)
          finally show ?thesis .
        qed
        with xP show "x \<in> A (Suc n) (j # js')"
          unfolding A_def by (simp del: usc_sel_code_Suc)
      qed
      show ?thesis
      proof (cases "usc_sel_set M d z js' = {}")
        case True
        have "A n js' = {}"
        proof -
          have "usc_sel_set M d z (usc_sel_code M d z (f x) n) \<noteq> {}" for x
            by (rule usc_sel_code_set_ne[OF cpt z dns ne])
          with True show ?thesis unfolding A_def by auto
        qed
        with split Cons show ?thesis by simp
      next
        case False
        have exg: "\<exists>i. usc_sel_good M d z (f x) js' i" for x
          by (rule usc_sel_good_ex[OF cpt z dns False])
        have leasteq: "((LEAST i. usc_sel_good M d z (f x) js' i) = j)
            \<longleftrightarrow> (usc_sel_good M d z (f x) js' j
                \<and> (\<forall>i<j. \<not> usc_sel_good M d z (f x) js' i))" for x
          by (rule Least_nat_eq_iff) (rule exg)
        have setD: "{x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}
            = {x \<in> space P. usc_sel_good M d z (f x) js' j}
              - (\<Union>i\<in>{..<j}. {x \<in> space P. usc_sel_good M d z (f x) js' i})"
          using leasteq by auto
        have "(\<Union>i\<in>{..<j}. {x \<in> space P. usc_sel_good M d z (f x) js' i}) \<in> sets P"
          using Gmeas by (intro sets.finite_UN) auto
        then have "{x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}
            \<in> sets P"
          unfolding setD by (rule sets.Diff[OF Gmeas])
        with Suc[of js'] split Cons show ?thesis by simp
      qed
    qed
  qed
  have preim: "s -` U \<inter> space P
      = (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
    if U: "openin mtopology U" for U
  proof (intro set_eqI iffI)
    fix x assume "x \<in> s -` U \<inter> space P"
    then have xP: "x \<in> space P" and xU: "usc_sel M d z (f x) \<in> U"
      unfolding s_def by auto
    from usc_sel_code_set_in_open[OF cpt z dns ne U xU]
    obtain n where n: "usc_sel_set M d z (usc_sel_code M d z (f x) n) \<subseteq> U"
      by blast
    have "x \<in> A (length (usc_sel_code M d z (f x) n))
        (usc_sel_code M d z (f x) n)"
      using xP unfolding A_def by simp
    with n show "x \<in> (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
      by blast
  next
    fix x assume "x \<in> (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
    then obtain js where js: "usc_sel_set M d z js \<subseteq> U" "x \<in> A (length js) js"
      by blast
    from js(2) have xP: "x \<in> space P"
      and c: "usc_sel_code M d z (f x) (length js) = js"
      unfolding A_def by auto
    have inset: "usc_sel M d z (f x)
        \<in> usc_sel_set M d z (usc_sel_code M d z (f x) (length js))"
      by (rule usc_sel_in_code_set[OF cpt z dns ne])
    from inset c have "usc_sel M d z (f x) \<in> usc_sel_set M d z js" by simp
    with js(1) have "s x \<in> U" unfolding s_def by blast
    with xP show "x \<in> s -` U \<inter> space P" by simp
  qed
  have smeas: "s \<in> P \<rightarrow>\<^sub>M borel_of mtopology"
  proof (rule measurable_sigma_sets)
    show "sets (borel_of mtopology)
        = sigma_sets (topspace mtopology) {U. openin mtopology U}"
      by (rule sets_borel_of)
    have "U \<subseteq> topspace mtopology" if "openin mtopology U" for U
      by (rule openin_subset[OF that])
    then show "{U. openin mtopology U} \<subseteq> Pow (topspace mtopology)" by auto
    show "s \<in> space P \<rightarrow> topspace mtopology" using sM by auto
    show "s -` U \<inter> space P \<in> sets P" if "U \<in> {U. openin mtopology U}" for U
    proof -
      have cnt: "countable {js :: nat list. usc_sel_set M d z js \<subseteq> U}"
        by (rule countableI_type)
      have "s -` U \<inter> space P
          = (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
        using that by (intro preim) simp
      also have "\<dots> \<in> sets P"
        by (rule sets.countable_UN''[OF cnt]) (rule Ameas)
      finally show ?thesis .
    qed
  qed
  show ?thesis by (rule that[OF smeas sM sopt])
qed

end

(*<*)
end
(*>*)
