
(*<*)
theory Semicontinuous_Envelopes
  imports "HOL-Analysis.Analysis"
begin

(*>*)

text \<open>
  The semicontinuous envelopes of a general real-valued function: \<open>lsc_env\<close>
  and \<open>usc_env\<close> over all of \<open>real^'n\<close>, and \<open>lsc_envK\<close>/\<open>Kext\<close>, the envelope
  taken relative to a closed set \<open>K\<close> -- the form Definition 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> of the paper
  actually reads, since it takes the liminf over points of \<open>K\<close> only.  Their
  monotonicity, and the fixpoint at points where the underlying function is
  already semicontinuous.
\<close>

definition lsc_env :: "('a::metric_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "lsc_env u x = (SUP e \<in> {0<..}. INF y \<in> ball x e. u y)"

definition usc_env :: "('a::metric_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "usc_env u x = - lsc_env (\<lambda>y. - u y) x"

lemma lsc_env_bdd_below_ball:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "bdd_below (u ` S)"
  by (rule bdd_belowI[of _ B]) (use B in auto)

lemma lsc_env_bdd_above:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "bdd_above ((\<lambda>e. INF y \<in> ball x e. u y) ` {0<..})"
proof (rule bdd_aboveI[of _ "u x"])
  fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
  have "(INF y \<in> ball x e. u y) \<le> u x"
    by (rule cInf_lower[OF _ lsc_env_bdd_below_ball[OF B]]) (use e0 in auto)
  then show "t \<le> u x" unfolding te .
qed

lemma lsc_env_le_self:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "lsc_env u x \<le> u x"
  unfolding lsc_env_def
proof (rule cSup_least)
  show "(\<lambda>e. INF y \<in> ball x e. u y) ` {0<..} \<noteq> {}" by auto
next
  fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
  show "t \<le> u x"
    unfolding te
    by (rule cInf_lower[OF _ lsc_env_bdd_below_ball[OF B]]) (use e0 in auto)
qed

lemma lsc_env_ge:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "B \<le> lsc_env u x"
proof -
  have "B \<le> (INF y \<in> ball x 1. u y)"
    by (rule cInf_greatest) (use B in auto)
  also have "\<dots> \<le> lsc_env u x"
    unfolding lsc_env_def
    by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) auto
  finally show ?thesis .
qed

lemma usc_env_ge_self:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
  shows "u x \<le> usc_env u x"
proof -
  have "lsc_env (\<lambda>y. - u y) x \<le> - u x"
    by (rule lsc_env_le_self[of "- B"]) (use B in auto)
  then show ?thesis unfolding usc_env_def by linarith
qed

lemma usc_env_le:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
  shows "usc_env u x \<le> B"
proof -
  have "- B \<le> lsc_env (\<lambda>y. - u y) x"
    by (rule lsc_env_ge[of "- B"]) (use B in auto)
  then show ?thesis unfolding usc_env_def by linarith
qed

text \<open>The limsup bound that Theorem 4.3 of \<^cite>\<open>LaiShkolnikovSoner\<close>'s \<open>\<iota> \<down> 1\<close> step consumes: a value
  bounded below along a sequence tending to \<open>x\<close> is bounded by the upper
  envelope at \<open>x\<close>.  No continuity anywhere.\<close>

lemma usc_env_limsup_bound:
  fixes u :: "'a::metric_space \<Rightarrow> real" and zs :: "nat \<Rightarrow> 'a"
  assumes B: "\<And>y. u y \<le> B" and lim: "zs \<longlonglongrightarrow> x"
    and lo: "\<And>j. c \<le> u (zs j)"
  shows "c \<le> usc_env u x"
proof (rule ccontr)
  assume "\<not> c \<le> usc_env u x"
  then have lt: "usc_env u x < c" by simp
  have mB: "\<And>y. - B \<le> - u y" using B by simp
  have bdda: "bdd_above ((\<lambda>e. INF y \<in> ball x e. - u y) ` {0<..})"
    by (rule lsc_env_bdd_above[of "- B"]) (use B in auto)
  have neA: "(\<lambda>e. INF y \<in> ball x e. - u y) ` {0<..} \<noteq> {}" by auto
  have "- c < lsc_env (\<lambda>y. - u y) x" using lt unfolding usc_env_def by simp
  then have "- c < (SUP e \<in> {0<..}. INF y \<in> ball x e. - u y)"
    unfolding lsc_env_def .
  then obtain t where tmem: "t \<in> (\<lambda>e. INF y \<in> ball x e. - u y) ` {0<..}"
    and tc: "- c < t"
    using less_cSup_iff[OF neA bdda] by auto
  from tmem obtain e where e0: "0 < e"
    and te: "t = (INF y \<in> ball x e. - u y)" by auto
  obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> dist (zs j) x < e"
    using lim e0 unfolding lim_sequentially by blast
  have zin: "zs N \<in> ball x e" using N[of N] by (simp add: dist_commute)
  have "t \<le> - u (zs N)"
    unfolding te
    by (rule cInf_lower[OF _ lsc_env_bdd_below_ball[OF mB]]) (use zin in auto)
  moreover have "c \<le> u (zs N)" by (rule lo)
  ultimately show False using tc by linarith
qed

lemma lsc_env_mono:
  fixes u v :: "'a::metric_space \<Rightarrow> real"
  assumes le: "\<And>y. u y \<le> v y" and Bu: "\<And>y. B \<le> u y"
  shows "lsc_env u x \<le> lsc_env v x"
proof -
  have Bv: "\<And>y. B \<le> v y" using Bu le order_trans by blast
  show ?thesis
    unfolding lsc_env_def
  proof (rule cSup_least)
    show "(\<lambda>e. INF y \<in> ball x e. u y) ` {0<..} \<noteq> {}" by auto
  next
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
    have "(INF y \<in> ball x e. u y) \<le> (INF y \<in> ball x e. v y)"
      by (rule cInf_mono) (use e0 le lsc_env_bdd_below_ball[OF Bu] in auto)
    also have "\<dots> \<le> (SUP e \<in> {0<..}. INF y \<in> ball x e. v y)"
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF Bv]]) (use e0 in auto)
    finally show "t \<le> (SUP e \<in> {0<..}. INF y \<in> ball x e. v y)" unfolding te .
  qed
qed

lemma lsc_env_lsc:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and lt: "c < lsc_env u z"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < lsc_env u y"
proof -
  have neA: "(\<lambda>e. INF y \<in> ball z e. u y) ` {0<..} \<noteq> {}" by auto
  from lt obtain t where tmem: "t \<in> (\<lambda>e. INF y \<in> ball z e. u y) ` {0<..}"
    and tc: "c < t"
    unfolding lsc_env_def
    using less_cSup_iff[OF neA lsc_env_bdd_above[OF B]] by auto
  from tmem obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball z e. u y)"
    by auto
  have key: "c < lsc_env u y" if dzy: "dist z y < e / 2" for y
  proof -
    have subb: "ball y (e/2) \<subseteq> ball z e"
    proof
      fix q assume "q \<in> ball y (e/2)"
      then have "dist y q < e/2" by simp
      have "dist z q \<le> dist z y + dist y q" by (rule dist_triangle)
      also have "\<dots> < e/2 + e/2" using dzy \<open>dist y q < e/2\<close> by linarith
      finally show "q \<in> ball z e" by simp
    qed
    have "t \<le> (INF q \<in> ball y (e/2). u q)"
      unfolding te
      by (rule cInf_superset_mono[OF _ _ image_mono[OF subb]])
        (use e0 lsc_env_bdd_below_ball[OF B] in auto)
    also have "\<dots> \<le> lsc_env u y"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use e0 in auto)
    finally show ?thesis using tc by linarith
  qed
  show ?thesis by (rule exI[of _ "e/2"]) (use e0 key in auto)
qed

lemma usc_env_mono:
  fixes u v :: "'a::metric_space \<Rightarrow> real"
  assumes le: "\<And>y. u y \<le> v y" and Bv: "\<And>y. v y \<le> B"
  shows "usc_env u x \<le> usc_env v x"
proof -
  have "lsc_env (\<lambda>y. - v y) x \<le> lsc_env (\<lambda>y. - u y) x"
    by (rule lsc_env_mono[of _ _ "- B"]) (use le Bv in auto)
  then show ?thesis unfolding usc_env_def by linarith
qed

lemma usc_env_eq_self:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
    and usc: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
  shows "usc_env u x = u x"
proof (rule antisym)
  show "usc_env u x \<le> u x"
  proof (rule ccontr)
    assume "\<not> usc_env u x \<le> u x"
    then have lt: "u x < usc_env u x" by simp
    define cc where "cc = (u x + usc_env u x) / 2"
    have cc2: "2 * cc = u x + usc_env u x" unfolding cc_def by simp
    have c1: "u x < cc" and c2: "cc < usc_env u x" using lt cc2 by linarith+
    obtain e where e0: "0 < e" and ey: "\<forall>y. dist x y < e \<longrightarrow> u y < cc"
      using usc[OF c1] by blast
    have mB: "\<And>y. - B \<le> - u y" using B by simp
    have "- cc \<le> (INF y \<in> ball x e. - u y)"
      by (rule cInf_greatest) (use e0 ey in auto)
    also have "\<dots> \<le> lsc_env (\<lambda>y. - u y) x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF mB]]) (use e0 in auto)
    finally have "- cc \<le> lsc_env (\<lambda>y. - u y) x" .
    then have "usc_env u x \<le> cc" unfolding usc_env_def by linarith
    then show False using c2 by linarith
  qed
  show "u x \<le> usc_env u x" by (rule usc_env_ge_self[OF B])
qed


text \<open>The property the envelope exists for: arbitrarily near \<open>x\<close> there
  are points where \<open>u\<close> is arbitrarily close to \<open>u\<^sub>*(x)\<close> from above.  This
  is what supplies the approximating sequence along which a construction
  built on the envelope is run.\<close>

lemma lsc_env_approx:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and d0: "0 < \<delta>" and e0: "0 < \<epsilon>"
  obtains y where "dist x y < \<delta>" and "u y < lsc_env u x + \<epsilon>"
proof -
  have bdd: "bdd_below (u ` ball x \<delta>)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have ne: "u ` ball x \<delta> \<noteq> {}" using d0 by auto
  have le: "(INF y \<in> ball x \<delta>. u y) \<le> lsc_env u x"
    unfolding lsc_env_def
    by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use d0 in auto)
  have "(INF y \<in> ball x \<delta>. u y) < lsc_env u x + \<epsilon>"
    using le e0 by linarith
  then obtain z where z: "z \<in> u ` ball x \<delta>" and zlt: "z < lsc_env u x + \<epsilon>"
    using cInf_less_iff[OF ne bdd] by blast
  from z obtain y where y: "y \<in> ball x \<delta>" and uy: "z = u y" by auto
  show ?thesis
  proof (rule that)
    show "dist x y < \<delta>" using y by simp
    show "u y < lsc_env u x + \<epsilon>" using zlt unfolding uy .
  qed
qed

text \<open>At a point of continuity the lower envelope is the function itself.\<close>

lemma lsc_env_eq_self:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and c: "isCont u x"
  shows "lsc_env u x = u x"
proof (rule antisym)
  show "lsc_env u x \<le> u x" by (rule lsc_env_le_self[OF B])
next
  show "u x \<le> lsc_env u x"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    obtain d where d0: "0 < d"
      and dd: "\<And>z. dist z x < d \<Longrightarrow> dist (u z) (u x) < e"
      using c[unfolded continuous_at_eps_delta] e0 by blast
    have bdd: "bdd_below (u ` ball x d)"
      by (rule bdd_belowI[of _ B]) (use B in auto)
    have "u x - e \<le> (INF y \<in> ball x d. u y)"
    proof (rule cInf_greatest)
      show "u ` ball x d \<noteq> {}" using d0 by auto
    next
      fix z assume "z \<in> u ` ball x d"
      then obtain y where y: "y \<in> ball x d" and zy: "z = u y" by auto
      have "dist y x < d" using y by (simp add: dist_commute)
      then have "dist (u y) (u x) < e" by (rule dd)
      then show "u x - e \<le> z" unfolding zy by (simp add: dist_real_def)
    qed
    also have "\<dots> \<le> lsc_env u x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use d0 in auto)
    finally show "u x \<le> lsc_env u x + e" by linarith
  qed
qed
subsection \<open>The envelope taken within \<open>K\<close>\<close>

text \<open>Definition 3.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> of the paper reads its lower envelope \<open>u\<^sub>*\<close> inside \<open>K\<close>:
  the liminf is over points of \<open>K\<close> only.  @{const lsc_env} takes it over balls
  of \<open>'a\<close>, so the two agree at interior points of \<open>K\<close> and can differ on
  \<open>K - interior K\<close>, which is exactly where the boundary gate of Eq. (1.10) is
  read.  \<open>lsc_envK\<close> is the paper's envelope.

  The bridge between them is an extension.  A function on \<open>K\<close> reaches
  \<open>'a\<close> only through one, and the extension has to do two incompatible
  looking things: stay high enough off \<open>K\<close> that it does not lower the
  infimum over a ball (or the two envelopes differ), and stay low enough at
  \<open>K - interior K\<close> that upper semicontinuity survives (or the comparison
  machinery does not apply).  Composing with the nearest-point projection does
  both --- off \<open>K\<close> the value is a value of \<open>u\<close> at a point at most twice as far
  away --- and the upper envelope of that composite repairs semicontinuity at
  the points outside \<open>K\<close> where the projection jumps, without touching \<open>K\<close>.\<close>

definition lsc_envK ::
  "('a::metric_space) set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "lsc_envK K u x = (SUP e \<in> {0<..}. INF y \<in> (ball x e \<inter> K). u y)"

lemma lsc_envK_ge:
  fixes K :: "('a::metric_space) set" and u :: "'a \<Rightarrow> real"
  assumes B: "\<And>y. Bl \<le> u y" and x: "x \<in> K"
  shows "Bl \<le> lsc_envK K u x"
proof -
  have ne1: "ball x 1 \<inter> K \<noteq> {}"
  proof -
    have "x \<in> ball x 1 \<inter> K" using x by simp
    then show ?thesis by blast
  qed
  have "Bl \<le> (INF y \<in> ball x 1 \<inter> K. u y)"
    by (rule cInf_greatest) (use ne1 B in auto)
  also have "\<dots> \<le> lsc_envK K u x"
    unfolding lsc_envK_def
  proof (rule cSup_upper)
    show "(INF y \<in> ball x 1 \<inter> K. u y)
        \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}" by auto
    show "bdd_above ((\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..})"
    proof (rule bdd_aboveI[of _ "u x"])
      fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}"
      then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e \<inter> K. u y)"
        by auto
      show "t \<le> u x" unfolding te
        by (rule cInf_lower) (use e0 x B in \<open>auto intro!: bdd_belowI[of _ Bl]\<close>)
    qed
  qed
  finally show ?thesis .
qed

lemma lsc_env_eq_on_interior:
  fixes K :: "('a::metric_space) set" and u :: "'a \<Rightarrow> real"
  assumes B: "\<And>y. Bl \<le> u y" and x: "x \<in> interior K"
  shows "lsc_env u x = lsc_envK K u x"
proof -
  have xK: "x \<in> K" using x interior_subset by blast
  obtain r where r0: "0 < r" and rK: "ball x r \<subseteq> K"
    using x mem_interior by blast
  have bddb: "bdd_below (u ` S)" for S :: "('a) set"
    by (rule bdd_belowI[of _ Bl]) (use B in auto)
  have neI: "ball x e \<inter> K \<noteq> {}" if e: "0 < e" for e
  proof -
    have "x \<in> ball x e \<inter> K" using xK e by simp
    then show ?thesis by blast
  qed
  have bddA: "bdd_above ((\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..})"
  proof (rule bdd_aboveI[of _ "u x"])
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e \<inter> K. u y)"
      by auto
    show "t \<le> u x" unfolding te
      by (rule cInf_lower[OF _ bddb]) (use e0 xK in auto)
  qed
  have d1: "lsc_env u x \<le> lsc_envK K u x"
    unfolding lsc_env_def
  proof (rule cSup_least)
    show "(\<lambda>e. INF y \<in> ball x e. u y) ` {0<..} \<noteq> {}" by auto
  next
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. u y)" by auto
    have "t \<le> (INF y \<in> ball x e \<inter> K. u y)"
      unfolding te
      by (rule cInf_superset_mono[OF _ bddb]) (use neI[OF e0] in auto)
    also have "\<dots> \<le> lsc_envK K u x"
      unfolding lsc_envK_def by (rule cSup_upper[OF _ bddA]) (use e0 in auto)
    finally show "t \<le> lsc_envK K u x" .
  qed
  have d2: "lsc_envK K u x \<le> lsc_env u x"
    unfolding lsc_envK_def
  proof (rule cSup_least)
    show "(\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..} \<noteq> {}" by auto
  next
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e \<inter> K. u y)"
      by auto
    define d where "d = min e r"
    have d0: "0 < d" unfolding d_def using e0 r0 by simp
    have dsub: "ball x d \<inter> K \<subseteq> ball x e \<inter> K" unfolding d_def by auto
    have deq: "ball x d \<inter> K = ball x d"
      unfolding d_def using rK by auto
    have "t \<le> (INF y \<in> ball x d \<inter> K. u y)"
      unfolding te
      by (rule cInf_superset_mono[OF _ bddb image_mono[OF dsub]])
        (use neI[OF d0] in auto)
    also have "\<dots> = (INF y \<in> ball x d. u y)" unfolding deq by (rule refl)
    also have "\<dots> \<le> lsc_env u x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use d0 in auto)
    finally show "t \<le> lsc_env u x" .
  qed
  show ?thesis by (rule antisym[OF d1 d2])
qed

lemma usc_env_usc:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
    and lt: "usc_env u z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> usc_env u y < c"
proof -
  have mB: "\<And>y. - B \<le> - u y" using B by simp
  have neg: "- c < lsc_env (\<lambda>y. - u y) z" using lt unfolding usc_env_def by simp
  obtain e where e0: "0 < e"
    and ey: "\<forall>y. dist z y < e \<longrightarrow> - c < lsc_env (\<lambda>y. - u y) y"
    using lsc_env_lsc[where u = "\<lambda>y. - u y" and B = "- B" and c = "- c" and z = z,
        OF mB neg] by blast
  show ?thesis
  proof (intro exI[of _ e] conjI e0 allI impI)
    fix y assume "dist z y < e"
    then have "- c < lsc_env (\<lambda>w. - u w) y" using ey by blast
    then show "usc_env u y < c" unfolding usc_env_def by simp
  qed
qed

lemma usc_env_eq_at:
  fixes u :: "'a::metric_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> B"
    and usc: "\<And>c. u x < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> u y < c"
  shows "usc_env u x = u x"
proof (rule antisym)
  show "usc_env u x \<le> u x"
  proof (rule ccontr)
    assume "\<not> usc_env u x \<le> u x"
    then have lt: "u x < usc_env u x" by simp
    define cc where "cc = (u x + usc_env u x) / 2"
    have cc2: "2 * cc = u x + usc_env u x" unfolding cc_def by simp
    have c1: "u x < cc" and c2: "cc < usc_env u x" using lt cc2 by linarith+
    obtain e where e0: "0 < e" and ey: "\<forall>y. dist x y < e \<longrightarrow> u y < cc"
      using usc[OF c1] by blast
    have mB: "\<And>y. - B \<le> - u y" using B by simp
    have "- cc \<le> (INF y \<in> ball x e. - u y)"
      by (rule cInf_greatest) (use e0 ey in auto)
    also have "\<dots> \<le> lsc_env (\<lambda>y. - u y) x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF mB]]) (use e0 in auto)
    finally have "- cc \<le> lsc_env (\<lambda>y. - u y) x" .
    then have "usc_env u x \<le> cc" unfolding usc_env_def by linarith
    then show False using c2 by linarith
  qed
  show "u x \<le> usc_env u x" by (rule usc_env_ge_self[OF B])
qed

definition Kext ::
  "('a::euclidean_space) set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "Kext K u = usc_env (\<lambda>y. u (closest_point K y))"

lemma Kext_proj_bound:
  fixes K :: "('a::euclidean_space) set"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> B"
  shows "u (closest_point K y) \<le> B"
  by (rule B[OF closest_point_in_set[OF Kc neK]])

lemma Kext_proj_near:
  fixes K :: "('a::euclidean_space) set"
  assumes Kc: "closed K" and x: "x \<in> K"
  shows "dist x (closest_point K y) \<le> 2 * dist x y"
proof -
  have "dist y (closest_point K y) \<le> dist y x"
    by (rule closest_point_le[OF Kc x])
  then have "dist x (closest_point K y) \<le> dist x y + dist y x"
    using dist_triangle[of x "closest_point K y" y]
    by (simp add: dist_commute)
  then show ?thesis by (simp add: dist_commute)
qed

lemma Kext_eq_on_K:
  fixes K :: "('a::euclidean_space) set" and u :: "'a \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> B"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and x: "x \<in> K"
  shows "Kext K u x = u x"
proof -
  define f where "f = (\<lambda>y. u (closest_point K y))"
  have fB: "f y \<le> B" for y
    unfolding f_def by (rule Kext_proj_bound[OF Kc neK B])
  have fx: "f x = u x"
    unfolding f_def closest_point_self[OF x] by (rule refl)
  have fusc: "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y < c" if c: "f x < c" for c
  proof -
    have "u x < c" using c fx by simp
    then obtain e where e0: "0 < e"
      and ey: "\<forall>y\<in>K. dist x y < e \<longrightarrow> u y < c"
      using usc[OF x] by blast
    show ?thesis
    proof (intro exI[of _ "e / 2"] conjI allI impI)
      show "0 < e / 2" using e0 by simp
    next
      fix y assume d: "dist x y < e / 2"
      have pK: "closest_point K y \<in> K"
        by (rule closest_point_in_set[OF Kc neK])
      have "dist x (closest_point K y) \<le> 2 * dist x y"
        by (rule Kext_proj_near[OF Kc x])
      also have "\<dots> < e" using d by simp
      finally show "f y < c" unfolding f_def using ey pK by blast
    qed
  qed
  show ?thesis
    unfolding Kext_def f_def[symmetric] fx[symmetric]
    by (rule usc_env_eq_at[OF fB fusc])
qed

lemma Kext_bounded:
  fixes K :: "('a::euclidean_space) set" and u :: "'a \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
  shows "\<bar>Kext K u y\<bar> \<le> Bd"
proof -
  define f where "f = (\<lambda>w. u (closest_point K w))"
  have fB: "f w \<le> Bd" for w
    unfolding f_def by (rule Kext_proj_bound[OF Kc neK]) (use B in \<open>simp add: abs_le_iff\<close>)
  have fL: "- Bd \<le> f w" for w
  proof -
    have m: "closest_point K w \<in> K" by (rule closest_point_in_set[OF Kc neK])
    have "\<bar>u (closest_point K w)\<bar> \<le> Bd" by (rule B[OF m])
    then show ?thesis unfolding f_def by (simp add: abs_le_iff)
  qed
  have "Kext K u y \<le> Bd"
    unfolding Kext_def f_def[symmetric] by (rule usc_env_le[OF fB])
  moreover have "- Bd \<le> Kext K u y"
  proof -
    have "f y \<le> usc_env f y" by (rule usc_env_ge_self[OF fB])
    then show ?thesis unfolding Kext_def f_def[symmetric] using fL[of y] by linarith
  qed
  ultimately show ?thesis by (simp add: abs_le_iff)
qed

lemma Kext_usc:
  fixes K :: "('a::euclidean_space) set" and u :: "'a \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> B"
    and lt: "Kext K u z < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> Kext K u y < c"
proof -
  define f where "f = (\<lambda>w. u (closest_point K w))"
  have fB: "f w \<le> B" for w
    unfolding f_def by (rule Kext_proj_bound[OF Kc neK B])
  have "usc_env f z < c" using lt unfolding Kext_def f_def[symmetric] .
  then show ?thesis
    unfolding Kext_def f_def[symmetric] by (rule usc_env_usc[OF fB])
qed

lemma Kext_ge_proj:
  fixes K :: "('a::euclidean_space) set" and u :: "'a \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> B"
  shows "u (closest_point K y) \<le> Kext K u y"
  unfolding Kext_def
  by (rule usc_env_ge_self[of "\<lambda>w. u (closest_point K w)" B])
    (rule Kext_proj_bound[OF Kc neK B])

lemma lsc_env_Kext:
  fixes K :: "('a::euclidean_space) set" and u :: "'a \<Rightarrow> real"
  assumes Kc: "closed K" and neK: "K \<noteq> {}"
    and B: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
      \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and x: "x \<in> K"
  shows "lsc_env (Kext K u) x = lsc_envK K u x"
proof -
  have Bu: "u y \<le> Bd" if "y \<in> K" for y using B[OF that] by (simp add: abs_le_iff)
  have Bl: "- Bd \<le> u y" if "y \<in> K" for y using B[OF that] by (simp add: abs_le_iff)
  define g where "g = Kext K u"
  have gB: "\<bar>g y\<bar> \<le> Bd" for y
    unfolding g_def by (rule Kext_bounded[OF Kc neK B])
  have gl: "- Bd \<le> g y" for y using gB[of y] by (simp add: abs_le_iff)
  have gK: "g y = u y" if "y \<in> K" for y
    unfolding g_def by (rule Kext_eq_on_K[OF Kc neK Bu usc that])
  have bddK: "bdd_below (u ` (ball x e \<inter> K))" for e
    by (rule bdd_belowI[of _ "- Bd"]) (use Bl in auto)
  have bddg: "bdd_below (g ` ball x e)" for e
    by (rule bdd_belowI[of _ "- Bd"]) (use gl in auto)
  have neK': "ball x e \<inter> K \<noteq> {}" if e: "0 < e" for e
  proof -
    have "x \<in> ball x e \<inter> K" using x e by simp
    then show ?thesis by blast
  qed
  have bddA: "bdd_above ((\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..})"
  proof (rule bdd_aboveI[of _ "u x"])
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e \<inter> K. u y)"
      by auto
    show "t \<le> u x" unfolding te
      by (rule cInf_lower[OF _ bddK]) (use e0 x in auto)
  qed
  \<comment> \<open>the extension can only lower the infimum, so one half is the inclusion\<close>
  have d1: "lsc_env g x \<le> lsc_envK K u x"
    unfolding lsc_env_def
  proof (rule cSup_least)
    show "(\<lambda>e. INF y \<in> ball x e. g y) ` {0<..} \<noteq> {}" by auto
  next
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e. g y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e. g y)" by auto
    have sub: "u ` (ball x e \<inter> K) \<subseteq> g ` ball x e"
    proof
      fix s assume "s \<in> u ` (ball x e \<inter> K)"
      then obtain y where y: "y \<in> ball x e \<inter> K" and s: "s = u y" by blast
      have "s = g y" unfolding s using gK y by auto
      then show "s \<in> g ` ball x e" using y by auto
    qed
    have "t \<le> (INF y \<in> ball x e \<inter> K. u y)"
      unfolding te
      by (rule cInf_superset_mono[OF _ bddg sub]) (use neK'[OF e0] in auto)
    also have "\<dots> \<le> lsc_envK K u x"
      unfolding lsc_envK_def by (rule cSup_upper[OF _ bddA]) (use e0 in auto)
    finally show "t \<le> lsc_envK K u x" .
  qed
  \<comment> \<open>and off \<open>K\<close> the extension is a value of \<open>u\<close> at a point at most twice as far\<close>
  have step2: "(INF y \<in> ball x (e * 2) \<inter> K. u y) \<le> (INF y \<in> ball x e. g y)"
    if e: "0 < e" for e
  proof (rule cInf_greatest)
    show "g ` ball x e \<noteq> {}" using e by auto
  next
    fix t assume "t \<in> g ` ball x e"
    then obtain y where y: "y \<in> ball x e" and t: "t = g y" by blast
    have pK: "closest_point K y \<in> K" by (rule closest_point_in_set[OF Kc neK])
    have "dist x (closest_point K y) \<le> 2 * dist x y"
      by (rule Kext_proj_near[OF Kc x])
    also have "\<dots> < e * 2" using y by simp
    finally have pin: "closest_point K y \<in> ball x (e * 2) \<inter> K"
      using pK by simp
    have "(INF y \<in> ball x (e * 2) \<inter> K. u y) \<le> u (closest_point K y)"
      by (rule cInf_lower[OF _ bddK]) (use pin in auto)
    also have "\<dots> \<le> g y"
      unfolding g_def by (rule Kext_ge_proj[OF Kc neK Bu])
    finally show "(INF y \<in> ball x (e * 2) \<inter> K. u y) \<le> t" unfolding t .
  qed
  have d2: "lsc_envK K u x \<le> lsc_env g x"
    unfolding lsc_envK_def
  proof (rule cSup_least)
    show "(\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..} \<noteq> {}" by auto
  next
    fix t assume "t \<in> (\<lambda>e. INF y \<in> ball x e \<inter> K. u y) ` {0<..}"
    then obtain e where e0: "0 < e" and te: "t = (INF y \<in> ball x e \<inter> K. u y)"
      by auto
    have half: "0 < e / 2" using e0 by simp
    have "t \<le> (INF y \<in> ball x (e / 2). g y)"
      using step2[OF half] unfolding te by simp
    also have "\<dots> \<le> lsc_env g x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF gl]]) (use half in auto)
    finally show "t \<le> lsc_env g x" .
  qed
  show ?thesis unfolding g_def[symmetric] by (rule antisym[OF d1 d2])
qed

(*<*)
end
(*>*)
