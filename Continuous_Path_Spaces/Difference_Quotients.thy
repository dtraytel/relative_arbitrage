section \<open>Difference quotients of a continuous path, tested at rationals\<close>

(*<*)
theory Difference_Quotients
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>The weak limit gives the constraint only for the countably many
  rational pairs \<open>s < t\<close> (one closed set each, all of full mass,
  intersected). Path continuity and closedness upgrade this to all real
  \<open>s < t\<close>: squeeze rationals \<open>p\<^sub>n \<down> s\<close>, \<open>q\<^sub>n \<up> t\<close> strictly inside
  \<open>(s,t)\<close> and pass to the limit.  A lower guard \<open>r \<le> p\<close> on the rational
  pairs costs nothing: the rationals picked satisfy \<open>p\<^sub>n > s \<ge> r\<close>, which
  is why the grid can stay in the original time scale even though the
  interval starts at the random \<open>\<theta> p'\<close>.\<close>

lemma diffquot_all_of_rational_ge:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes S: "closed S"
    and cont: "continuous_on {0..T} Y"
    and rat: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> r \<le> p \<Longrightarrow> (1 / (q - p)) *\<^sub>R (Y q - Y p) \<in> S"
    and rs: "r \<le> s" and st: "0 \<le> s" "s < t" "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
proof -
  define d where "d = (t - s) / 3"
  have d0: "0 < d" using st unfolding d_def by simp
  define e where "e = (\<lambda>n :: nat. min d (1 / real (Suc n)))"
  have e0: "0 < e n" for n using d0 unfolding e_def by simp
  have ed: "e n \<le> d" for n unfolding e_def by simp
  have elim: "e \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>n. 0" e sequentially
      "\<lambda>n. 1 / real (Suc n)"])
    show "\<forall>\<^sub>F n in sequentially. 0 \<le> e n"
      using e0 by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. e n \<le> 1 / real (Suc n)"
      by (simp add: e_def)
    show "(\<lambda>n :: nat. 0 :: real) \<longlonglongrightarrow> 0" by simp
    show "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
  qed
  have exp: "\<exists>z. z \<in> \<rat> \<and> s < z \<and> z < s + e n" for n
  proof -
    have "s < s + e n" using e0 by simp
    from Rats_dense_in_real[OF this] show ?thesis by blast
  qed
  have exq: "\<exists>z. z \<in> \<rat> \<and> t - e n < z \<and> z < t" for n
  proof -
    have "t - e n < t" using e0 by simp
    from Rats_dense_in_real[OF this] show ?thesis by blast
  qed
  obtain p where p: "\<And>n. p n \<in> \<rat>" "\<And>n. s < p n" "\<And>n. p n < s + e n"
    using exp by metis
  obtain q where q: "\<And>n. q n \<in> \<rat>" "\<And>n. t - e n < q n" "\<And>n. q n < t"
    using exq by metis
  have mid: "s + d < t - d" unfolding d_def using st by argo
  have pq: "p n < q n" for n
  proof -
    have "p n < s + d" using p(3)[of n] ed[of n] by simp
    also have "\<dots> < t - d" by (rule mid)
    also have "\<dots> \<le> t - e n" using ed[of n] by simp
    also have "\<dots> < q n" by (rule q(2))
    finally show ?thesis .
  qed
  have pmem: "p n \<in> {0..T}" for n
    using p(2)[of n] pq[of n] q(3)[of n] st by auto
  have qmem: "q n \<in> {0..T}" for n
    using q(3)[of n] p(2)[of n] pq[of n] st by auto
  have inS: "(1 / (q n - p n)) *\<^sub>R (Y (q n) - Y (p n)) \<in> S" for n
  proof (rule rat)
    show "p n \<in> \<rat>" by (rule p(1))
    show "q n \<in> \<rat>" by (rule q(1))
    show "0 \<le> p n" using pmem[of n] by simp
    show "p n < q n" by (rule pq)
    show "q n \<le> T" using qmem[of n] by simp
    show "r \<le> p n" using rs p(2)[of n] by simp
  qed
  have pl: "p \<longlonglongrightarrow> s"
  proof (rule tendsto_sandwich[of "\<lambda>n. s" p sequentially "\<lambda>n. s + e n"])
    show "\<forall>\<^sub>F n in sequentially. s \<le> p n" using p(2) by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. p n \<le> s + e n"
      using p(3) by (simp add: less_imp_le)
    show "(\<lambda>n. s) \<longlonglongrightarrow> s" by simp
    show "(\<lambda>n. s + e n) \<longlonglongrightarrow> s"
      using tendsto_add[OF tendsto_const elim] by simp
  qed
  have ql: "q \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of "\<lambda>n. t - e n" q sequentially "\<lambda>n. t"])
    show "\<forall>\<^sub>F n in sequentially. t - e n \<le> q n"
      using q(2) by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. q n \<le> t" using q(3) by (simp add: less_imp_le)
    show "(\<lambda>n. t - e n) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const elim] by simp
    show "(\<lambda>n. t) \<longlonglongrightarrow> t" by simp
  qed
  have Yp: "(\<lambda>n. Y (p n)) \<longlonglongrightarrow> Y s"
    using st pmem by (intro continuous_on_tendsto_compose[OF cont pl]) auto
  have Yq: "(\<lambda>n. Y (q n)) \<longlonglongrightarrow> Y t"
    using st qmem by (intro continuous_on_tendsto_compose[OF cont ql]) auto
  have "(\<lambda>n. (1 / (q n - p n)) *\<^sub>R (Y (q n) - Y (p n)))
      \<longlonglongrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s)"
    using st by (intro tendsto_intros Yp Yq ql pl) auto
  then show ?thesis by (rule closed_sequentially[OF S inS])
qed

text \<open>The unguarded form is the case \<open>r = 0\<close>.\<close>

lemma diffquot_all_of_rational:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes S: "closed S"
    and cont: "continuous_on {0..T} Y"
    and rat: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (Y q - Y p) \<in> S"
    and st: "0 \<le> s" "s < t" "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
  by (rule diffquot_all_of_rational_ge[where r = 0, OF S cont rat st(1) st]) auto

text \<open>On continuous paths the constraint on the difference quotients over all
  real pairs is the constraint over the rational pairs, a countable condition;
  so it is a measurable event as soon as the evaluations are measurable.\<close>

lemma diffquot_all_iff_rat:
  fixes Y :: "real \<Rightarrow> 'b::real_normed_vector" and S :: "'b set"
  assumes S: "closed S" and cont: "continuous_on {0..} Y"
  shows "(\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S)
     \<longleftrightarrow> (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
          (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R (Y (real_of_rat q) - Y (real_of_rat p)) \<in> S)"
    (is "?R \<longleftrightarrow> ?Q")
proof
  assume ?R then show ?Q by (auto simp: of_rat_less)
next
  assume Q: ?Q
  show ?R
  proof (intro allI impI)
    fix s t :: real assume st: "0 \<le> s" "s < t"
    show "(1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
    proof (rule diffquot_all_of_rational[OF S continuous_on_subset[OF cont] _ st order_refl])
      fix p q :: real assume "p \<in> \<rat>" "q \<in> \<rat>" "0 \<le> p" "p < q"
      then show "(1 / (q - p)) *\<^sub>R (Y q - Y p) \<in> S"
        using Q by (auto elim!: Rats_cases simp: of_rat_less)
    qed auto
  qed
qed

lemma diffquot_all_pred:
  fixes Y :: "'w \<Rightarrow> real \<Rightarrow> 'b::euclidean_space" and S :: "'b set"
  assumes S: "closed S"
    and cont: "\<And>w. w \<in> space N \<Longrightarrow> continuous_on {0..} (Y w)"
    and meas: "\<And>t. 0 \<le> t \<Longrightarrow> (\<lambda>w. Y w t) \<in> borel_measurable N"
  shows "Measurable.pred N
    (\<lambda>w. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (Y w t - Y w s) \<in> S)"
proof -
  have "Measurable.pred N (\<lambda>w. \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
      (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R (Y w (real_of_rat q) - Y w (real_of_rat p)) \<in> S)"
  proof (intro pred_intros_countable pred_intros_imp')
    fix p q :: rat assume "0 \<le> p" "p < q"
    then have "(0::real) \<le> real_of_rat p" "(0::real) \<le> real_of_rat q"
      by (auto simp: of_rat_less)
    then show "Measurable.pred N (\<lambda>w. (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
        (Y w (real_of_rat q) - Y w (real_of_rat p)) \<in> S)"
      by (intro pred_sets2[OF borel_closed[OF S]] borel_measurable_scaleR
          borel_measurable_const borel_measurable_diff meas)
  qed
  moreover have "{w \<in> space N. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (Y w t - Y w s) \<in> S}
      = {w \<in> space N. \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R (Y w (real_of_rat q) - Y w (real_of_rat p)) \<in> S}"
    using diffquot_all_iff_rat[OF S cont] by blast
  ultimately show ?thesis unfolding pred_def by simp
qed

text \<open>Once the constraint holds for all \<open>s < t\<close>, boundedness of the
  constraint set makes \<open>Y\<close> Lipschitz, and closedness carries through to
  the derivative wherever it exists: \<open>dY/dt \<in> S\<close> a.e., the density
  statement of Eq. (1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close>.\<close>

lemma diffquot_lipschitz:
  fixes Y :: "real \<Rightarrow> 'b :: real_normed_vector" and S :: "'b set"
  assumes B0: "0 \<le> B" and B: "\<And>a. a \<in> S \<Longrightarrow> norm a \<le> B"
    and dq: "\<And>s t. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> t \<le> T
        \<Longrightarrow> (1 / (t - s)) *\<^sub>R (Y t - Y s) \<in> S"
  shows "B-lipschitz_on {0..T} Y"
proof (rule lipschitz_onI[OF _ B0])
  fix u v :: real
  assume uv: "u \<in> {0..T}" "v \<in> {0..T}"
  have key: "dist (Y a) (Y b) \<le> B * dist a b"
    if ab: "a \<in> {0..T}" "b \<in> {0..T}" "a < b" for a b
  proof -
    have ba: "0 < b - a" using ab by simp
    have "(1 / (b - a)) *\<^sub>R (Y b - Y a) \<in> S"
      using ab by (intro dq) auto
    then have "norm ((1 / (b - a)) *\<^sub>R (Y b - Y a)) \<le> B" by (rule B)
    then have "(1 / (b - a)) * norm (Y b - Y a) \<le> B"
      using ba by simp
    then have "norm (Y b - Y a) \<le> B * (b - a)"
      using ba by (simp add: field_simps)
    then show ?thesis
      using ba by (simp add: dist_norm norm_minus_commute)
  qed
  show "dist (Y u) (Y v) \<le> B * dist u v"
  proof (cases "u = v")
    case True
    then show ?thesis using B0 by simp
  next
    case ne: False
    show ?thesis
    proof (cases "u < v")
      case True
      show ?thesis by (rule key[OF uv True])
    next
      case False
      with ne have vu: "v < u" by simp
      have "dist (Y v) (Y u) \<le> B * dist v u"
        by (rule key[OF uv(2) uv(1) vu])
      then show ?thesis by (simp add: dist_commute)
    qed
  qed
qed

text \<open>The \<open>\<forall>\<close>-form of the freezing, which the additive glue's \<open>Kfr\<close> hypothesis
  consumes.  The measurability of the frozen set is the only real content:
  a continuous path vanishing at every rational point of \<open>[0,d]\<close> vanishes
  there, so the set is a countable intersection of evaluation conditions.\<close>

lemma vanishes_of_rational:
  fixes w :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes d0: "0 \<le> d" and cont: "continuous_on {0..d} w"
    and rat: "\<And>q. q \<in> (\<rat> :: real set) \<Longrightarrow> q \<in> {0..d} \<Longrightarrow> w q = 0"
    and u: "u \<in> {0..d}"
  shows "w u = 0"
proof (cases "d = 0")
  case True
  then show ?thesis using u rat[of 0] by simp
next
  case False
  then have cl: "closure ({0..d} \<inter> \<rat>) = {0..d}"
    using d0 by (subst closure_convex_Int_superset) (auto simp: Rats_closure_real)
  show ?thesis
    by (rule continuous_constant_on_closure[of "{0..d} \<inter> \<rat>" w]) (use cont rat u cl in auto)
qed

(*<*)
end
(*>*)
