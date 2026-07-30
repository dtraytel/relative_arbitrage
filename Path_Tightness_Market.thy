section \<open>Lemma 2.2, market form: subsequence extraction from the martingale package\<close>

text \<open>
  The adapter between the stochastic layer (Stopped\_Localization) and the
  topological layer (Path\_Tightness): the moment hypotheses of
  \<open>path_laws_convergent_subsequence_vec\<close> are discharged per coordinate by
  \<open>fourth_moment_L2_integrable\<close> / \<open>fourth_moment_L2_bochner\<close>, so the
  subsequence extraction of Lemma 2.2 holds for any sequence of laws carrying,
  per coordinate, an \<open>L\<^sup>2\<close> martingale with a compensated square whose adapted
  compensator grows at rate at most \<open>C\<close> — the formal content of the paper's
  admissibility conditions Eqs. (1.7)-(1.8).

  NOTE on imports: this theory imports Path\_Tightness and
  Stopped\_Localization, which share the DRAFT ancestor Increment\_Moments, so
  it forms the diamond that PIDE cannot load (STATUS.md, environment traps);
  it is verified by the batch build only.
\<close>

theory Path_Tightness_Market
  imports Path_Tightness Stopped_Localization
begin

corollary path_laws_convergent_subsequence_market:
  fixes MM :: "nat \<Rightarrow> 'a measure" and FF :: "nat \<Rightarrow> real \<Rightarrow> 'a measure"
    and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and AA :: "nat \<Rightarrow> 'm \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and T C \<gamma> :: real and x :: "real^'m"
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4" and C0: "0 \<le> C"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and mgX: "\<And>i l. martingale (MM i) (FF i) 0 (\<lambda>s \<omega>. XX i s \<omega> $ l)"
    and sqX: "\<And>i l s. 0 \<le> s \<Longrightarrow> integrable (MM i) (\<lambda>\<omega>. (XX i s \<omega> $ l)\<^sup>2)"
    and contX: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..} (\<lambda>s. XX i s \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and mgZ: "\<And>i l. martingale (MM i) (FF i) 0
        (\<lambda>t \<omega>. (XX i t \<omega> $ l)\<^sup>2 - AA i l t \<omega>)"
    and Aad: "\<And>i l. adapted_process (MM i) (FF i) 0 (AA i l)"
    and A0: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> AA i l 0 \<omega> = 0"
    and A_rate: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> AA i l v \<omega> - AA i l u \<omega> \<and> AA i l v \<omega> - AA i l u \<omega> \<le> C * (v - u)"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof (rule path_laws_convergent_subsequence_vec[where C = C and x = x, OF T0 g0 g2])
  show "\<And>i. prob_space (MM i)" by (rule P)
  show "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)" by (rule Xm)
  show "continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    if w: "\<omega> \<in> space (MM i)" for i \<omega>
    by (rule continuous_on_subset[OF contX[OF w]]) auto
  show "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x" by (rule start)
  show "integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    if u0: "0 \<le> u" and uv: "u \<le> v" and vT: "v \<le> T" for i l u v
  proof -
    have contl: "continuous_on {0..} (\<lambda>s. XX i s \<omega> $ l)"
      if w: "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_component[OF contX[OF w]])
    have startl: "XX i 0 \<omega> $ l = x $ l" if w: "\<omega> \<in> space (MM i)" for \<omega>
      using start[OF w] by simp
    show ?thesis
      by (rule fourth_moment_L2_integrable[OF P mgX sqX contl startl mgZ Aad A0
            A_rate C0 u0 uv])
  qed
  show "(\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    if u0: "0 \<le> u" and uv: "u \<le> v" and vT: "v \<le> T" for i l u v
  proof -
    have contl: "continuous_on {0..} (\<lambda>s. XX i s \<omega> $ l)"
      if w: "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_component[OF contX[OF w]])
    have startl: "XX i 0 \<omega> $ l = x $ l" if w: "\<omega> \<in> space (MM i)" for \<omega>
      using start[OF w] by simp
    show ?thesis
      by (rule fourth_moment_L2_bochner[OF P mgX sqX contl startl mgZ Aad A0
            A_rate C0 u0 uv])
  qed
qed

end
