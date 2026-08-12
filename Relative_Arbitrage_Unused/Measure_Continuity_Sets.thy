section \<open>Continuity sets of a finite Borel measure\<close>

(*<*)
theory Measure_Continuity_Sets
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>
  First layer of the Skorokhod representation development (open task 25, needed by
  Lemma 2.3 of arXiv:2512.17702). Skorokhod's representation theorem on a Polish
  space is absent from both the Isabelle distribution and the AFP -- the
  distribution's @{text Weak_Convergence.Skorohod} is the one-dimensional version
  proved via the quantile transform, and it does not transfer to a general Polish
  space because the statement is topological rather than merely Borel.

  Its Billingsley-style proof begins by partitioning the space into small Borel
  pieces whose BOUNDARIES are null for the limit measure. That step rests on the
  fact developed here: for a finite Borel measure, only countably many spheres
  about a given centre can carry positive mass, because spheres of distinct radii
  are disjoint and the total mass is finite. Hence every interval of radii
  contains a radius whose sphere is null, and small balls with null boundary can
  always be found.

  Nothing here depends on stochastic integration, so this layer is independent of
  the deferred open task 15.
\<close>
subsection \<open>Spheres: disjointness, closedness, measurability\<close>

lemma sphere_disjoint:
  fixes x :: "'a::metric_space"
  assumes "r \<noteq> s"
  shows "sphere x r \<inter> sphere x s = {}"
  using assms by auto

lemma disjoint_family_on_sphere:
  fixes x :: "'a::metric_space"
  shows "disjoint_family_on (\<lambda>r. sphere x r) R"
  unfolding disjoint_family_on_def using sphere_disjoint by blast

text \<open>
  @{thm [source] closed_sphere} in HOL-Analysis is restricted to
  @{class real_normed_vector} with @{class heine_borel}, so the general metric
  version is proved here from @{term "sphere x r = cball x r - ball x r"}.
\<close>

lemma closed_sphere_metric:
  fixes x :: "'a::metric_space"
  shows "closed (sphere x r)"
proof -
  have "sphere x r = cball x r - ball x r" by auto
  thus ?thesis by (simp add: closed_Diff)
qed

lemma sphere_in_borel:
  fixes x :: "'a::metric_space"
  shows "sphere x r \<in> sets borel"
  by (intro borel_closed closed_sphere_metric)

subsection \<open>Only countably many spheres carry mass\<close>

text \<open>
  These are stated with @{term "finite_measure M"} as a hypothesis rather than
  inside the locale: the locale already fixes @{typ 'a} without a sort, so a
  @{class metric_space} constraint on it is rejected there.
\<close>

lemma finite_heavy_spheres:
  fixes x :: "'a::metric_space"
  assumes M: "finite_measure M" and sets_M: "sets M = borel" and c: "0 < c"
  shows "finite {r. c < measure M (sphere x r)}"
proof (rule ccontr)
  assume inf: "infinite {r. c < measure M (sphere x r)}"
  obtain n :: nat where n: "measure M (space M) < real n * c"
    using c reals_Archimedean3 by auto
  obtain F where F: "F \<subseteq> {r. c < measure M (sphere x r)}"
    and finF: "finite F" and cardF: "card F = n"
    using infinite_arbitrarily_large[OF inf] by blast
  have meas: "sphere x r \<in> sets M" for r
    unfolding sets_M by (rule sphere_in_borel)
  have "real n * c = (\<Sum>r\<in>F. c)" using cardF by simp
  also have "\<dots> \<le> (\<Sum>r\<in>F. measure M (sphere x r))"
    using F by (intro sum_mono) auto
  also have "\<dots> = measure M (\<Union>r\<in>F. sphere x r)"
    using finF meas disjoint_family_on_sphere
    by (intro finite_measure.finite_measure_finite_Union[symmetric, OF M]) auto
  also have "\<dots> \<le> measure M (space M)"
    by (rule finite_measure.bounded_measure[OF M])
  finally show False using n by simp
qed

lemma countable_positive_spheres:
  fixes x :: "'a::metric_space"
  assumes M: "finite_measure M" and sets_M: "sets M = borel"
  shows "countable {r. 0 < measure M (sphere x r)}"
proof -
  have eq: "{r. 0 < measure M (sphere x r)}
            = (\<Union>k. {r. 1 / real (Suc k) < measure M (sphere x r)})"
  proof (intro equalityI subsetI)
    fix r assume "r \<in> {r. 0 < measure M (sphere x r)}"
    then have "0 < measure M (sphere x r)" by simp
    then obtain k where "1 / real (Suc k) < measure M (sphere x r)"
      using nat_approx_posE by blast
    thus "r \<in> (\<Union>k. {r. 1 / real (Suc k) < measure M (sphere x r)})" by blast
  next
    fix r assume "r \<in> (\<Union>k. {r. 1 / real (Suc k) < measure M (sphere x r)})"
    then obtain k where k: "1 / real (Suc k) < measure M (sphere x r)" by blast
    have "(0::real) < 1 / real (Suc k)" by simp
    also note k
    finally have "0 < measure M (sphere x r)" .
    thus "r \<in> {r. 0 < measure M (sphere x r)}" by simp  qed
  have "countable (\<Union>k. {r. 1 / real (Suc k) < measure M (sphere x r)})"
  proof (intro countable_UN countableI_type countable_finite)
    fix k :: nat
    show "finite {r. 1 / real (Suc k) < measure M (sphere x r)}"
      by (rule finite_heavy_spheres[OF M sets_M]) simp
  qed
  with eq show ?thesis by simp
qed

subsection \<open>Radii with a null sphere are dense\<close>

lemma exists_null_sphere:
  fixes x :: "'a::metric_space"
  assumes M: "finite_measure M" and sets_M: "sets M = borel" and ab: "a < b"
  shows "\<exists>r\<in>{a<..<b}. measure M (sphere x r) = 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have sub: "{a<..<b} \<subseteq> {r. 0 < measure M (sphere x r)}"
    using measure_nonneg by (force simp: less_le)
  have "uncountable {a<..<b}" using ab by (simp add: uncountable_open_interval)
  moreover have "countable {a<..<b}"
    using sub countable_positive_spheres[OF M sets_M] by (rule countable_subset)
  ultimately show False by simp
qed

subsection \<open>Small balls whose boundary is null\<close>

text \<open>
  The form in which the Skorokhod construction uses the above: about any point
  there are arbitrarily small balls that are CONTINUITY SETS of @{term M}, i.e.
  whose frontier is @{term M}-null. Weak convergence gives convergence of
  measures on exactly such sets, which is what makes the partition step of the
  construction work.
\<close>

lemma frontier_ball_subset_sphere:
  fixes x :: "'a::metric_space"
  shows "frontier (ball x r) \<subseteq> sphere x r"
proof -
  have "closure (ball x r) \<subseteq> cball x r"
    by (rule closure_minimal) auto
  moreover have "interior (ball x r) = ball x r" by simp
  ultimately show ?thesis unfolding frontier_def by auto
qed

lemma null_frontier_ball_of_null_sphere:
  fixes x :: "'a::metric_space"
  assumes M: "finite_measure M" and sets_M: "sets M = borel"
    and null: "measure M (sphere x r) = 0"
  shows "measure M (frontier (ball x r)) = 0"
proof -
  have "measure M (frontier (ball x r)) \<le> measure M (sphere x r)"
    using frontier_ball_subset_sphere[of x r]
    by (intro finite_measure.finite_measure_mono[OF M])
       (auto simp: sets_M sphere_in_borel)
  then have "measure M (frontier (ball x r)) \<le> 0" using null by simp
  moreover have "0 \<le> measure M (frontier (ball x r))" by (rule measure_nonneg)
  ultimately show ?thesis by simp
qed

lemma exists_small_null_boundary_ball:
  fixes x :: "'a::metric_space"
  assumes M: "finite_measure M" and sets_M: "sets M = borel" and e: "0 < e"
  obtains r where "0 < r" "r < e" "measure M (frontier (ball x r)) = 0"
proof -
  have half: "e / 2 < e" using e by simp
  obtain r where r: "r \<in> {e/2<..<e}" and null: "measure M (sphere x r) = 0"
    using exists_null_sphere[OF M sets_M half, of x] by blast
  have r0: "0 < r" using r e by auto
  have re: "r < e" using r by auto
  have nf: "measure M (frontier (ball x r)) = 0"
    by (rule null_frontier_ball_of_null_sphere[OF M sets_M null])
  show thesis by (rule that[OF r0 re nf])
qed
subsection \<open>A countable cover by small null-boundary balls\<close>

text \<open>
  Layer 2 of the construction. Separability turns the pointwise statement above
  into a single countable family covering the whole space, all of whose members
  are small and have null boundary. Disjointifying such a family needs the
  frontier of a set difference, so that is recorded first.
\<close>

lemma frontier_diff_subset: "frontier (S - T) \<subseteq> frontier S \<union> frontier T"
proof -
  have "S - T = S \<inter> (- T)" by auto
  hence "frontier (S - T) = frontier (S \<inter> (- T))" by simp
  also have "\<dots> \<subseteq> frontier S \<union> frontier (- T)" by (rule frontier_Int_subset)
  finally show ?thesis by simp
qed

lemma exists_small_null_boundary_cover:
  fixes M :: "'a::{metric_space, second_countable_topology} measure"
  assumes M: "finite_measure M" and sets_M: "sets M = borel" and e: "0 < e"
  obtains B :: "nat \<Rightarrow> 'a set" where
    "\<And>k. open (B k)"
    "\<And>k y z. y \<in> B k \<Longrightarrow> z \<in> B k \<Longrightarrow> dist y z < e"
    "\<And>k. measure M (frontier (B k)) = 0"
    "(\<Union>k. B k) = UNIV"
proof -
  obtain D :: "'a set" where cD: "countable D"
    and dense: "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d\<in>D. d \<in> X"
    by (rule countable_dense_setE) blast
  have Dne: "D \<noteq> {}" using dense[of UNIV] by auto
  define x where "x = from_nat_into D"
  have xD: "x k \<in> D" for k
    unfolding x_def using Dne by (rule from_nat_into)
  have quart: "e/4 < e/2" using e by simp
  have "\<exists>r. e/4 < r \<and> r < e/2
             \<and> measure M (frontier (ball (x k) r)) = 0" for k
  proof -
    obtain r where r: "r \<in> {e/4<..<e/2}"
      and null: "measure M (sphere (x k) r) = 0"
      using exists_null_sphere[OF M sets_M quart, of "x k"] by blast
    have "measure M (frontier (ball (x k) r)) = 0"
      by (rule null_frontier_ball_of_null_sphere[OF M sets_M null])
    with r show ?thesis by auto
  qed
  then obtain r where rlo: "\<And>k. e/4 < r k" and rhi: "\<And>k. r k < e/2"
    and rnull: "\<And>k. measure M (frontier (ball (x k) (r k))) = 0"
    by metis
  define B where "B = (\<lambda>k. ball (x k) (r k))"
  show thesis
  proof (rule that)
    show "open (B k)" for k unfolding B_def by simp
    show "measure M (frontier (B k)) = 0" for k
      unfolding B_def by (rule rnull)
    show "dist y z < e" if "y \<in> B k" "z \<in> B k" for k y z
    proof -
      have "dist y z \<le> dist y (x k) + dist (x k) z" by (rule dist_triangle)
      also have "\<dots> < r k + r k"
        using that unfolding B_def by (simp add: dist_commute)
      also have "\<dots> < e" using rhi[of k] by simp
      finally show ?thesis .
    qed
    show "(\<Union>k. B k) = UNIV"
    proof (intro equalityI subsetI UNIV_I)
      fix y :: 'a
      have "ball y (e/4) \<noteq> {}" using e by auto
      then obtain d where dD: "d \<in> D" and dy: "d \<in> ball y (e/4)"
        using dense[of "ball y (e/4)"] by auto
      have "x (to_nat_on D d) = d"
        unfolding x_def using cD dD by (rule from_nat_into_to_nat_on)
      moreover have "dist y d < e/4" using dy by (simp add: dist_commute)
      ultimately have "dist y (x (to_nat_on D d)) < r (to_nat_on D d)"
        using rlo[of "to_nat_on D d"] by simp
      hence "y \<in> B (to_nat_on D d)"
        unfolding B_def by (simp add: dist_commute)      thus "y \<in> (\<Union>k. B k)" by blast
    qed
  qed
qed
subsection \<open>Disjointifying: a small null-boundary PARTITION\<close>

text \<open>
  Layer 3. Turning the cover of the previous subsection into a partition uses
  the library's @{const disjointed}, so disjointness and the preservation of the
  union come for free (@{thm [source] disjoint_family_disjointed},
  @{thm [source] UN_disjointed_eq}). What has to be checked is that the null
  boundaries survive, and that needs the frontier of a FINITE union.
\<close>

lemma frontier_UN_finite_subset:
  assumes "finite F"
  shows "frontier (\<Union>i\<in>F. S i) \<subseteq> (\<Union>i\<in>F. frontier (S i))"
  using assms
proof (induction F)
  case empty
  thus ?case by simp
next
  case (insert a F)
  have "frontier (\<Union>i\<in>insert a F. S i) = frontier (S a \<union> (\<Union>i\<in>F. S i))" by simp
  also have "\<dots> \<subseteq> frontier (S a) \<union> frontier (\<Union>i\<in>F. S i)"
    by (rule frontier_Un_subset)
  also have "\<dots> \<subseteq> frontier (S a) \<union> (\<Union>i\<in>F. frontier (S i))"
    using insert.IH by blast
  finally show ?case by auto
qed

lemma null_measure_UN_finite:
  assumes M: "finite_measure M" and F: "finite F"
    and sets: "\<And>i. i \<in> F \<Longrightarrow> T i \<in> sets M"
    and null: "\<And>i. i \<in> F \<Longrightarrow> measure M (T i) = 0"
  shows "measure M (\<Union>i\<in>F. T i) = 0"
proof -
  have "measure M (\<Union>i\<in>F. T i) \<le> (\<Sum>i\<in>F. measure M (T i))"
    using F sets
    by (intro finite_measure.finite_measure_subadditive_finite[OF M]) auto
  also have "\<dots> = 0" using null by simp
  finally have le: "measure M (\<Union>i\<in>F. T i) \<le> 0" .
  with measure_nonneg[of M "\<Union>i\<in>F. T i"] show ?thesis by linarith
qed

lemma frontier_disjointed_subset:
  "frontier (disjointed B k) \<subseteq> (\<Union>i\<in>{..k}. frontier (B i))"
proof -
  have "frontier (disjointed B k)
        \<subseteq> frontier (B k) \<union> frontier (\<Union>i\<in>{0..<k}. B i)"
    unfolding disjointed_def by (rule frontier_diff_subset)
  also have "\<dots> \<subseteq> frontier (B k) \<union> (\<Union>i\<in>{0..<k}. frontier (B i))"
    using frontier_UN_finite_subset[of "{0..<k}" B] by blast
  finally have "frontier (disjointed B k)
                \<subseteq> frontier (B k) \<union> (\<Union>i\<in>{0..<k}. frontier (B i))" .
  moreover have "frontier (B k) \<union> (\<Union>i\<in>{0..<k}. frontier (B i))
                 \<subseteq> (\<Union>i\<in>{..k}. frontier (B i))"
  proof -
    have "\<And>i. i \<in> {0..<k} \<Longrightarrow> i \<in> {..k}" by auto
    moreover have "k \<in> {..k}" by simp
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

theorem exists_small_null_boundary_partition:
  fixes M :: "'a::{metric_space, second_countable_topology} measure"
  assumes M: "finite_measure M" and sets_M: "sets M = borel" and e: "0 < e"
  obtains A :: "nat \<Rightarrow> 'a set" where
    "\<And>k. A k \<in> sets M"
    "\<And>k y z. y \<in> A k \<Longrightarrow> z \<in> A k \<Longrightarrow> dist y z < e"
    "\<And>k. measure M (frontier (A k)) = 0"
    "disjoint_family A"
    "(\<Union>k. A k) = UNIV"
proof -
  obtain B :: "nat \<Rightarrow> 'a set" where Bopen: "\<And>k. open (B k)"
    and Bdiam: "\<And>k y z. y \<in> B k \<Longrightarrow> z \<in> B k \<Longrightarrow> dist y z < e"
    and Bnull: "\<And>k. measure M (frontier (B k)) = 0"
    and Bcover: "(\<Union>k. B k) = UNIV"
    by (rule exists_small_null_boundary_cover[OF M sets_M e]) blast
  define A where "A = disjointed B"
  have Asub: "A k \<subseteq> B k" for k
    unfolding A_def by (rule disjointed_subset)
  have Asets: "A k \<in> sets M" for k
  proof -
    have o1: "open (B k)" by (rule Bopen)
    have o2: "open (\<Union>i\<in>{0..<k}. B i)" using Bopen by blast
    have "B k - (\<Union>i\<in>{0..<k}. B i) \<in> sets borel"
      by (intro sets.Diff borel_open o1 o2)
    thus ?thesis unfolding A_def disjointed_def by (simp add: sets_M)
  qed  have Afront: "measure M (frontier (A k)) = 0" for k
  proof -
    have fsets: "frontier (B i) \<in> sets M" for i
      using sets_M by (simp add: borel_closed)
    have "measure M (frontier (A k)) \<le> measure M (\<Union>i\<in>{..k}. frontier (B i))"
      using frontier_disjointed_subset[of B k] fsets
      unfolding A_def
      by (intro finite_measure.finite_measure_mono[OF M]) auto
    also have "measure M (\<Union>i\<in>{..k}. frontier (B i)) = 0"
      using fsets Bnull by (intro null_measure_UN_finite[OF M]) auto
    finally have "measure M (frontier (A k)) \<le> 0" .
    moreover have "0 \<le> measure M (frontier (A k))" by (rule measure_nonneg)
    ultimately show ?thesis by simp
  qed
  show thesis
  proof (rule that)
    show "A k \<in> sets M" for k by (rule Asets)
    show "measure M (frontier (A k)) = 0" for k by (rule Afront)
    show "disjoint_family A"
      unfolding A_def by (rule disjoint_family_disjointed)
    show "dist y z < e" if "y \<in> A k" "z \<in> A k" for k y z
      using that Asub by (blast intro: Bdiam)
    show "(\<Union>k. A k) = UNIV"
      unfolding A_def using Bcover by (simp add: UN_disjointed_eq)
  qed
qed


(*<*)
end
(*>*)
