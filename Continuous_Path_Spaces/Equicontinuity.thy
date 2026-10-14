section \<open>The Arzela--Ascoli step for martingale laws\<close>

(*<*)
theory Equicontinuity
  imports
    "Kolmogorov_Chentsov.Holder_Continuous"
    "Semicontinuous_Analysis.Berge"
begin

(*>*)

text \<open>
  Relative compactness of the laws of continuous martingales with covariation
  rates in a bounded set @{text S} follows the chain:

  \<^item> Ito's formula and the Burkholder-Davis-Gundy inequality give a fourth
    moment bound @{text "E |X t - X s| ^ 4 \<le> K (t - s)\<^sup>2"};
  \<^item> Kolmogorov's continuity criterion gives locally Holder paths;
  \<^item> the Arzela-Ascoli theorem gives compact sets of paths;
  \<^item> Prokhorov's theorem converts tightness into relative compactness.

  The last three are available in the AFP or the Isabelle distribution:

  \<^item> Kolmogorov's criterion is @{text Kolmogorov_Chentsov.Kolmogorov_Chentsov},
    whose hypothesis is literally that moment bound with
    @{text "a = 4"}, @{text "b = 1"}, @{text "C = K"}, and whose
    conclusion is a modification with all paths @{text "local_holder_on \<gamma>"} for
    @{text "\<gamma> < 1/4"};
  \<^item> @{text Kolmogorov_Chentsov.local_holder_compact_imp_holder} upgrades that to
    a genuine Holder bound on each compact @{text "{0..T}"};
  \<^item> Arzela-Ascoli is @{text Arzela_Ascoli} of
    @{text "HOL-Complex_Analysis.Great_Picard"}, copied below;
  \<^item> Prokhorov's theorem is @{text Levy_Prokhorov_Metric.Prokhorov_theorem_LP}.

  This theory supplies the Arzela-Ascoli step in the form the rest of the chain
  needs it: a Holder bound with a constant @{text c} common to the whole
  family, since @{text "\<gamma>-holder_on"} quantifies its constant existentially per
  function, and Arzela-Ascoli genuinely requires a common one. Producing that
  uniform constant from the moment bound is the remaining probabilistic
  content of the compactness theorem.
\<close>
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

subsection \<open>The Arzela--Ascoli theorem\<close>

text \<open>
  The Arzela--Ascoli theorem and the two lemmas it rests on are copied verbatim
  from @{text "HOL-Complex_Analysis.Great_Picard"}, where L. C. Paulson ported
  them from HOL Light (@{text "cauchy.ml"}) in 2017. That theory is their only
  home in the distribution, and importing it would make this session depend on
  the whole of complex analysis for one theorem.
\<close>

lemma subsequence_diagonalization_lemma:
  fixes P :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes sub: "\<And>i r. \<exists>k. strict_mono (k :: nat \<Rightarrow> nat) \<and> P i (r \<circ> k)"
      and P_P:  "\<And>i r::nat \<Rightarrow> 'a. \<And>k1 k2 N.
                   \<lbrakk>P i (r \<circ> k1); \<And>j. N \<le> j \<Longrightarrow> \<exists>j'. j \<le> j' \<and> k2 j = k1 j'\<rbrakk> \<Longrightarrow> P i (r \<circ> k2)"
   obtains k where "strict_mono (k :: nat \<Rightarrow> nat)" "\<And>i. P i (r \<circ> k)"
proof -
  obtain kk where "\<And>i r. strict_mono (kk i r :: nat \<Rightarrow> nat) \<and> P i (r \<circ> (kk i r))"
    using sub by metis
  then have sub_kk: "\<And>i r. strict_mono (kk i r)" and P_kk: "\<And>i r. P i (r \<circ> (kk i r))"
    by auto
  define rr where "rr \<equiv> rec_nat (kk 0 r) (\<lambda>n x. x \<circ> kk (Suc n) (r \<circ> x))"
  then have [simp]: "rr 0 = kk 0 r" "\<And>n. rr(Suc n) = rr n \<circ> kk (Suc n) (r \<circ> rr n)"
    by auto
  show thesis
  proof
    have sub_rr: "strict_mono (rr i)" for i
      using sub_kk  by (induction i) (auto simp: strict_mono_def o_def)
    have P_rr: "P i (r \<circ> rr i)" for i
      using P_kk  by (induction i) (auto simp: o_def)
    have "i \<le> i+d \<Longrightarrow> rr i n \<le> rr (i+d) n" for d i n
    proof (induction d)
      case 0 then show ?case
        by simp
    next
      case (Suc d) then show ?case
        using seq_suble [OF sub_kk] strict_mono_less_eq [OF sub_rr]
        by (simp add: order_subst1)
    qed
    then have "\<And>i j n. i \<le> j \<Longrightarrow> rr i n \<le> rr j n"
      by (metis le_iff_add)
    show "strict_mono (\<lambda>n. rr n n)"
      unfolding strict_mono_Suc_iff
      by (simp add: Suc_le_lessD strict_monoD strict_mono_imp_increasing sub_kk sub_rr)
    have "\<exists>j. i \<le> j \<and> rr (n+d) i = rr n j" for d n i
    proof (induction d arbitrary: i)
      case (Suc d)
      then show ?case
        using seq_suble [OF sub_kk] by simp (meson order_trans)
    qed auto
    then have "\<And>m n i. n \<le> m \<Longrightarrow> \<exists>j. i \<le> j \<and> rr m i = rr n j"
      by (metis le_iff_add)
    then show "P i (r \<circ> (\<lambda>n. rr n n))" for i
      by (meson P_rr P_P)
  qed
qed

lemma function_convergent_subsequence:
  fixes f :: "[nat,'a] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "countable S" and M: "\<And>n::nat. \<And>x. x \<in> S \<Longrightarrow> norm(f n x) \<le> M"
   obtains k where "strict_mono (k::nat\<Rightarrow>nat)" "\<And>x. x \<in> S \<Longrightarrow> \<exists>l. (\<lambda>n. f (k n) x) \<longlonglongrightarrow> l"
proof (cases "S = {}")
  case True
  then show ?thesis
    using strict_mono_id that by fastforce
next
  case False
  with \<open>countable S\<close> obtain \<sigma> :: "nat \<Rightarrow> 'a" where \<sigma>: "S = range \<sigma>"
    using uncountable_def by blast
  obtain k where "strict_mono k" and k: "\<And>i. \<exists>l. (\<lambda>n. (f \<circ> k) n (\<sigma> i)) \<longlonglongrightarrow> l"
  proof (rule subsequence_diagonalization_lemma
      [of "\<lambda>i r. \<exists>l. ((\<lambda>n. (f \<circ> r) n (\<sigma> i)) \<longlongrightarrow> l) sequentially" id])
    show "\<exists>k::nat\<Rightarrow>nat. strict_mono k \<and> (\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k)) n (\<sigma> i)) \<longlonglongrightarrow> l)" for i r
    proof -
      have "f (r n) (\<sigma> i) \<in> cball 0 M" for n
        by (simp add: \<sigma> M)
      then show ?thesis
        using compact_def [of "cball (0::'b) M"] by (force simp: o_def)
    qed
    show "\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k2)) n (\<sigma> i)) \<longlonglongrightarrow> l"
      if "\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k1)) n (\<sigma> i)) \<longlonglongrightarrow> l" "\<And>j. N \<le> j \<Longrightarrow> \<exists>j'\<ge>j. k2 j = k1 j'"
      for i N and r k1 k2 :: "nat\<Rightarrow>nat"
      using that
      by (simp add: lim_sequentially) (metis (no_types, opaque_lifting) le_cases order_trans)
  qed auto
  with \<sigma> that show ?thesis
    by force
qed

theorem Arzela_Ascoli:
  fixes \<F> :: "[nat,'a::euclidean_space] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "compact S"
      and M: "\<And>n x. x \<in> S \<Longrightarrow> norm(\<F> n x) \<le> M"
      and equicont:
          "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>n y. y \<in> S \<and> norm(x - y) < d \<longrightarrow> norm(\<F> n x - \<F> n y) < e)"
  obtains g k where "continuous_on S g" "strict_mono (k :: nat \<Rightarrow> nat)"
                    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<and> x \<in> S \<longrightarrow> norm(\<F>(k n) x - g x) < e"
proof -
  have UEQ: "\<And>e. 0 < e \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>n. \<forall>x \<in> S. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (\<F> n x') (\<F> n x) < e)"
    apply (rule compact_uniformly_equicontinuous [OF \<open>compact S\<close>, of "range \<F>"])
    using equicont by (force simp: dist_commute dist_norm)+
  have "continuous_on S g"
       if "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<and> x \<in> S \<longrightarrow> norm(\<F>(r n) x - g x) < e"
       for g:: "'a \<Rightarrow> 'b" and r :: "nat \<Rightarrow> nat"
  proof (rule uniform_limit_theorem [of _ "\<F> \<circ> r"])
    have "continuous_on S (\<F> (r n))" for n
      using UEQ by (force simp: continuous_on_iff)
    then show "\<forall>\<^sub>F n in sequentially. continuous_on S ((\<F> \<circ> r) n)"
      by (simp add: eventually_sequentially)
    show "uniform_limit S (\<F> \<circ> r) g sequentially"
      using that by (metis (mono_tags, opaque_lifting) comp_apply dist_norm uniform_limit_sequentially_iff)
  qed auto
  moreover
  obtain R where "countable R" "R \<subseteq> S" and SR: "S \<subseteq> closure R"
    by (metis separable that)
  obtain k where "strict_mono k" and k: "\<And>x. x \<in> R \<Longrightarrow> \<exists>l. (\<lambda>n. \<F> (k n) x) \<longlonglongrightarrow> l"
    using \<open>R \<subseteq> S\<close> by (force intro: function_convergent_subsequence [OF \<open>countable R\<close> M])
  then have Cauchy: "Cauchy ((\<lambda>n. \<F> (k n) x))" if "x \<in> R" for x
    using convergent_eq_Cauchy that by blast
  have "\<exists>N. \<forall>m n x. N \<le> m \<and> N \<le> n \<and> x \<in> S \<longrightarrow> dist ((\<F> \<circ> k) m x) ((\<F> \<circ> k) n x) < e"
    if "0 < e" for e
  proof -
    obtain d where "0 < d"
      and d: "\<And>n. \<forall>x \<in> S. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (\<F> n x') (\<F> n x) < e/3"
      by (metis UEQ \<open>0 < e\<close> divide_pos_pos zero_less_numeral)
    obtain T where "T \<subseteq> R" and "finite T" and T: "S \<subseteq> (\<Union>c\<in>T. ball c d)"
    proof (rule compactE_image [OF  \<open>compact S\<close>, of R "(\<lambda>x. ball x d)"])
      have "closure R \<subseteq> (\<Union>c\<in>R. ball c d)"
        using \<open>0 < d\<close> by (auto simp: closure_approachable)
      with SR show "S \<subseteq> (\<Union>c\<in>R. ball c d)"
        by auto
    qed auto
    have "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (\<F> (k m) x) (\<F> (k n) x) < e/3" if "x \<in> R" for x
      using Cauchy \<open>0 < e\<close> that unfolding Cauchy_def
      by (metis less_divide_eq_numeral1(1) mult_zero_left)
    then obtain MF where MF: "\<And>x m n. \<lbrakk>x \<in> R; m \<ge> MF x; n \<ge> MF x\<rbrakk> \<Longrightarrow> norm (\<F> (k m) x - \<F> (k n) x) < e/3"
      using dist_norm by metis
    have "dist ((\<F> \<circ> k) m x) ((\<F> \<circ> k) n x) < e"
         if m: "Max (MF ` T) \<le> m" and n: "Max (MF ` T) \<le> n" "x \<in> S" for m n x
    proof -
      obtain t where "t \<in> T" and t: "x \<in> ball t d"
        using \<open>x \<in> S\<close> T by auto
      have "norm(\<F> (k m) t - \<F> (k m) x) < e / 3"
        by (metis \<open>R \<subseteq> S\<close> \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> d dist_norm mem_ball subset_iff t \<open>x \<in> S\<close>)
      moreover
      have "norm(\<F> (k n) t - \<F> (k n) x) < e / 3"
        by (metis \<open>R \<subseteq> S\<close> \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> subsetD d dist_norm mem_ball t \<open>x \<in> S\<close>)
      moreover
      have "norm(\<F> (k m) t - \<F> (k n) t) < e / 3"
      proof (rule MF)
        show "t \<in> R"
          using \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> by blast
        show "MF t \<le> m" "MF t \<le> n"
          by (meson Max_ge \<open>finite T\<close> \<open>t \<in> T\<close> finite_imageI imageI le_trans m n)+
      qed
      ultimately
      show ?thesis
        unfolding dist_norm [symmetric] o_def
          by (metis dist_triangle_third dist_commute)
    qed
    then show ?thesis
      by force
  qed
  then obtain g where "\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> x \<in> S \<longrightarrow> norm ((\<F> \<circ> k) n x - g x) < e"
    using uniformly_convergent_eq_cauchy [of "\<lambda>x. x \<in> S" "\<F> \<circ> k"] by (auto simp add: dist_norm)
  ultimately show thesis
    by (metis \<open>strict_mono k\<close> comp_apply that)
qed

subsection \<open>The Arzela-Ascoli step\<close>

text \<open>
  A family of paths on @{term "{0..T}"} sharing an initial value and a Holder
  constant has a uniformly convergent subsequence, and the limit is a path with
  the same initial value and the same Holder bound. This is the form in which
  the compactness of martingale laws uses the Arzela-Ascoli theorem.
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

(*<*)
end
(*>*)
