
(*<*)
theory Martingale_Algebra
  imports "Martingales.Martingale"
begin

(*>*)

text \<open>
  Elementary closure properties the AFP's \<open>Martingales\<close> entry does not
  record: sums, differences, constant shifts, congruence up to an almost-sure
  or eventual equality, time changes, coarser filtrations, images under a
  bounded linear map (hence componentwise vector and matrix martingales),
  multiplying by an initial-time-measurable factor, subtracting the start,
  and stopping at a deterministic time.
\<close>

section \<open>Sums, differences and constant shifts\<close>

lemma martingale_add:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes mX: "martingale M F t0 X" and mY: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>u \<omega>. X u \<omega> + Y u \<omega>)"
proof -
  interpret MX: martingale M F t0 X by (rule mX)
  interpret MY: martingale M F t0 Y by (rule mY)
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F t0 (\<lambda>u \<omega>. X u \<omega> + Y u \<omega>)"
    proof (unfold_locales)
      fix i :: real assume i: "t0 \<le> i"
      show "(\<lambda>\<omega>. X i \<omega> + Y i \<omega>) \<in> borel_measurable (F i)"
        using MX.adapted[OF i] MY.adapted[OF i] by simp
    qed
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> + Y i \<omega>)"
      by (intro Bochner_Integration.integrable_add MX.integrable MY.integrable)
    fix A and i j :: real
    assume A: "A \<in> F i" and ij: "t0 \<le> i" "i \<le> j"
    have j: "t0 \<le> j" using ij by simp
    have Ai: "A \<in> sets M"
      using A MX.subalgebras[OF ij(1)] by (auto simp: subalgebra_def)
    have siX: "set_integrable M A (X w)" if w: "t0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai MX.integrable[OF w]])
    have siY: "set_integrable M A (Y w)" if w: "t0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai MY.integrable[OF w]])
    have split: "set_lebesgue_integral M A (\<lambda>\<omega>. X w \<omega> + Y w \<omega>)
        = set_lebesgue_integral M A (X w) + set_lebesgue_integral M A (Y w)"
      if w: "t0 \<le> w" for w
      by (rule set_integral_add(2)[OF siX[OF w] siY[OF w]])
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X i \<omega> + Y i \<omega>)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X j \<omega> + Y j \<omega>)"
      unfolding split[OF ij(1)] split[OF j]
      using MX.set_integral_eq[OF A ij] MY.set_integral_eq[OF A ij] by simp
  qed
qed

lemma martingale_add_const:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes ffm: "finite_filtered_measure M F t0" and mg: "martingale M F t0 X"
  shows "martingale M F t0 (\<lambda>u \<omega>. c + X u \<omega>)"
proof -
  interpret FM: finite_filtered_measure M F t0 by (rule ffm)
  have "martingale M F t0 (\<lambda>_ _. c)" by (rule FM.martingale_const)
  from martingale_add[OF this mg] show ?thesis .
qed

text \<open>The AFP entry does not record the difference; both integrability side
  conditions of \<open>cond_exp_diff\<close> come straight from the two locales.\<close>

lemma martingale_diff:
  fixes X Y :: "'b :: {second_countable_topology, order_topology, t2_space}
    \<Rightarrow> 'a \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes MX: "martingale M F t0 X" and MY: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>i \<omega>. X i \<omega> - Y i \<omega>)"
proof -
  interpret MX: martingale M F t0 X by (rule MX)
  interpret MY: martingale M F t0 Y by (rule MY)
  show ?thesis
  proof (unfold_locales)
    show "\<And>i. t0 \<le> i \<Longrightarrow> (\<lambda>\<omega>. X i \<omega> - Y i \<omega>) \<in> borel_measurable (F i)"
      using MX.adapted MY.adapted by simp
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> - Y i \<omega>)"
      using MX.integrable MY.integrable by simp
    fix i j assume ij: "t0 \<le> i" "i \<le> j"
    then have j: "t0 \<le> j" by simp
    have "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. X j \<omega> - Y j \<omega>) \<omega>
        = cond_exp M (F i) (X j) \<omega> - cond_exp M (F i) (Y j) \<omega>"
      by (rule sigma_finite_subalgebra.cond_exp_diff
            [OF MX.sigma_finite_subalgebra_F[OF ij(1)]
                MX.integrable[OF j] MY.integrable[OF j]])
    then show "AE \<omega> in M. X i \<omega> - Y i \<omega>
        = cond_exp M (F i) (\<lambda>\<omega>. X j \<omega> - Y j \<omega>) \<omega>"
      using MX.martingale_property[OF ij] MY.martingale_property[OF ij] by force
  qed
qed

text \<open>The subtractive companion to \<open>martingale_add\<close>, but with the summand
  frozen at the start.\<close>

lemma martingale_sub_initial:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
  shows "martingale M F 0 (\<lambda>u \<omega>. X u \<omega> - X 0 \<omega>)"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have c: "martingale M F 0 (\<lambda>_ \<omega>. - X 0 \<omega>)"
  proof (rule MG.martingale_const_fun)
    show "integrable M (\<lambda>\<omega>. - X 0 \<omega>)" using MG.integrable[of 0] by simp
    show "(\<lambda>\<omega>. - X 0 \<omega>) \<in> borel_measurable (F 0)" using MG.adapted[of 0] by simp
  qed
  have "martingale M F 0 (\<lambda>u \<omega>. X u \<omega> + (- X 0 \<omega>))"
    by (rule martingale_add[OF mg c])
  then show ?thesis by simp
qed

section \<open>Congruence\<close>

text \<open>The processes below differ at negative times --- the shifted
  evaluation is \<open>undefined\<close> there, the shifted value is not --- and the
  martingale locale never looks at those, so a congruence above \<open>t\<^sub>0\<close> is
  what is needed.\<close>

lemma martingale_cong_ge:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes mg: "martingale M F t0 X"
    and eq: "\<And>u. t0 \<le> u \<Longrightarrow> X u = Y u"
  shows "martingale M F t0 Y"
proof -
  interpret MX: martingale M F t0 X by (rule mg)
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F t0 Y"
    proof (unfold_locales)
      fix i :: real assume i: "t0 \<le> i"
      show "Y i \<in> borel_measurable (F i)"
        using MX.adapted[OF i] eq[OF i] by simp
    qed
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (Y i)"
      using MX.integrable eq by simp
    fix A and i j :: real
    assume A: "A \<in> F i" and ij: "t0 \<le> i" "i \<le> j"
    have j: "t0 \<le> j" using ij by simp
    show "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)"
      using MX.set_integral_eq[OF A ij] eq[OF ij(1)] eq[OF j] by simp
  qed
qed

text \<open>Passing to an a.e. equal, still adapted, process.\<close>

lemma martingale_cong_AE:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
    and adap: "adapted_process M F (0::real) Y"
    and eq: "\<And>i. 0 \<le> i \<Longrightarrow> AE \<omega> in M. X i \<omega> = Y i \<omega>"
  shows "martingale M F 0 Y"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  interpret AY: adapted_process M F "0::real" Y by (rule adap)
  have Xm: "X i \<in> borel_measurable M" if i: "0 \<le> i" for i
    by (rule measurable_from_subalg[OF MG.subalgebras[OF i] MG.adapted[OF i]])
  have Ym: "Y i \<in> borel_measurable M" if i: "0 \<le> i" for i
    by (rule measurable_from_subalg[OF MG.subalgebras[OF i] AY.adapted[OF i]])
  have iY: "integrable M (Y i)" if i: "0 \<le> i" for i
    using MG.integrable[OF i] integrable_cong_AE[OF Xm[OF i] Ym[OF i] eq[OF i]]
    by simp
  show ?thesis
  proof (rule MG.martingale_of_set_integral_eq[OF adap iY])
    fix A and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and A: "A \<in> sets (F i)"
    then have j: "0 \<le> j" by simp
    have AM: "A \<in> sets M" using A MG.sets_F_subset[OF ij(1)] by auto
    have "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (X i)"
      using eq[OF ij(1)]
      by (intro set_lebesgue_integral_cong_AE[OF AM Ym[OF ij(1)] Xm[OF ij(1)]])
        auto
    also have "\<dots> = set_lebesgue_integral M A (X j)"
      by (rule MG.set_integral_eq[OF A ij])
    also have "\<dots> = set_lebesgue_integral M A (Y j)"
      using eq[OF j]
      by (intro set_lebesgue_integral_cong_AE[OF AM Xm[OF j] Ym[OF j]]) auto
    finally show "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)" .
  qed
qed

section \<open>Time changes and coarser filtrations\<close>

lemma martingale_time_change:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
    and s0: "\<And>u :: real. 0 \<le> u \<Longrightarrow> 0 \<le> s u"
    and smono: "\<And>u v :: real. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> s u \<le> s v"
  shows "martingale M (\<lambda>u. F (s u)) 0 (\<lambda>u. X (s u))"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have FMs: "filtered_measure M (\<lambda>u. F (s u)) (0::real)"
  proof (unfold_locales)
    show "subalgebra M (F (s i))" if "0 \<le> i" for i :: real
      by (rule MG.subalgebras[OF s0[OF that]])
    show "sets (F (s i)) \<le> sets (F (s j))" if "0 \<le> i" "i \<le> j" for i j :: real
      by (rule MG.sets_F_mono[OF s0[OF that(1)] smono[OF that]])
  qed
  interpret SF: sigma_finite_filtered_measure M "\<lambda>u. F (s u)" "0::real"
    unfolding sigma_finite_filtered_measure_def
      sigma_finite_filtered_measure_axioms_def
    using FMs MG.sigma_finite_subalgebra_F[OF s0[OF order_refl]] by blast
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process M (\<lambda>u. F (s u)) 0 (\<lambda>u. X (s u))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FMs MG.adapted[OF s0] by blast
    show "integrable M (X (s i))" if "0 \<le> i" for i :: real
      by (rule MG.integrable[OF s0[OF that]])
    show "set_lebesgue_integral M A (X (s i))
        = set_lebesgue_integral M A (X (s j))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F (s i))" for A and i j :: real
      by (rule MG.set_integral_eq[OF that(3) s0[OF that(1)] smono[OF that(1,2)]])
  qed
qed

text \<open>The congruence and the time change fused, for a process only defined
  through its relation to the base.\<close>

lemma martingale_time_change_cong:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
    and s0: "\<And>u :: real. 0 \<le> u \<Longrightarrow> 0 \<le> \<sigma> u"
    and smono: "\<And>u v :: real. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> \<sigma> u \<le> \<sigma> v"
    and eq: "\<And>u :: real. 0 \<le> u \<Longrightarrow> Y u = X (\<sigma> u)"
  shows "martingale M (\<lambda>u. F (\<sigma> u)) 0 Y"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have FMs: "filtered_measure M (\<lambda>u. F (\<sigma> u)) (0::real)"
  proof (unfold_locales)
    show "subalgebra M (F (\<sigma> i))" if "0 \<le> i" for i :: real
      by (rule MG.subalgebras[OF s0[OF that]])
    show "sets (F (\<sigma> i)) \<le> sets (F (\<sigma> j))" if "0 \<le> i" "i \<le> j" for i j :: real
      by (rule MG.sets_F_mono[OF s0[OF that(1)] smono[OF that]])
  qed
  interpret SF: sigma_finite_filtered_measure M "\<lambda>u. F (\<sigma> u)" "0::real"
    unfolding sigma_finite_filtered_measure_def
      sigma_finite_filtered_measure_axioms_def
    using FMs MG.sigma_finite_subalgebra_F[OF s0[OF order_refl]] by blast
  have adY: "Y i \<in> borel_measurable (F (\<sigma> i))" if i: "0 \<le> i" for i :: real
    unfolding eq[OF i] by (rule MG.adapted[OF s0[OF i]])
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process M (\<lambda>u. F (\<sigma> u)) 0 Y"
      unfolding adapted_process_def adapted_process_axioms_def
      using FMs adY by blast
    show "integrable M (Y i)" if i: "0 \<le> i" for i :: real
      unfolding eq[OF i] by (rule MG.integrable[OF s0[OF i]])
    show "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)"
      if ij: "0 \<le> i" "i \<le> j" and A: "A \<in> sets (F (\<sigma> i))" for A and i j :: real
    proof -
      have j0: "0 \<le> j" using ij by simp
      show ?thesis
        unfolding eq[OF ij(1)] eq[OF j0]
        by (rule MG.set_integral_eq[OF A s0[OF ij(1)] smono[OF ij]])
    qed
  qed
qed

text \<open>A martingale stays one along any coarser filtration it is still
  adapted to.\<close>

lemma martingale_coarser_filtration:
  fixes X :: "'b :: {second_countable_topology, order_topology, t2_space} \<Rightarrow> 'a \<Rightarrow>
    'c :: {second_countable_topology, banach}"
  assumes M: "martingale M F t0 X"
    and ffm: "finite_filtered_measure M G t0"
    and GF: "\<And>i. t0 \<le> i \<Longrightarrow> subalgebra (F i) (G i)"
    and adapt: "\<And>i. t0 \<le> i \<Longrightarrow> X i \<in> borel_measurable (G i)"
  shows "martingale M G t0 X"
proof -
  interpret MF: martingale M F t0 X by (rule M)
  interpret GG: finite_filtered_measure M G t0 by (rule ffm)
  show ?thesis
  proof (unfold_locales)
    show "\<And>i. t0 \<le> i \<Longrightarrow> X i \<in> borel_measurable (G i)" by (rule adapt)
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (X i)" by (rule MF.integrable)
    fix i j assume ij: "t0 \<le> i" "i \<le> j"
    then have j: "t0 \<le> j" by simp
    have sfsG: "sigma_finite_subalgebra M (G i)"
      by (rule GG.sigma_finite_subalgebra_F[OF ij(1)])
    have t1: "AE \<xi> in M. cond_exp M (G i) (X j) \<xi>
        = cond_exp M (G i) (cond_exp M (F i) (X j)) \<xi>"
      by (rule sigma_finite_subalgebra.cond_exp_nested_subalg
            [OF sfsG MF.integrable[OF j] MF.subalgebras[OF ij(1)] GF[OF ij(1)]])
    have t2: "AE \<xi> in M. cond_exp M (G i) (cond_exp M (F i) (X j)) \<xi>
        = cond_exp M (G i) (X i) \<xi>"
      by (rule sigma_finite_subalgebra.cond_exp_cong_AE
            [OF sfsG integrable_cond_exp MF.integrable[OF ij(1)]
                MF.martingale_property[OF ij, THEN AE_symmetric]])
    have t3: "AE \<xi> in M. cond_exp M (G i) (X i) \<xi> = X i \<xi>"
      by (rule sigma_finite_subalgebra.cond_exp_F_meas
            [OF sfsG MF.integrable[OF ij(1)] adapt[OF ij(1)]])
    from t1 t2 t3 show "AE \<xi> in M. X i \<xi> = cond_exp M (G i) (X j) \<xi>" by force
  qed
qed

section \<open>Images under a bounded linear map\<close>

lemma integral_of_bounded_linear:
  fixes T :: "'b::{second_countable_topology,banach}
      \<Rightarrow> 'c::{second_countable_topology,banach}"
  assumes T: "bounded_linear T" and f: "integrable M f"
  shows "(\<integral>\<omega>. T (f \<omega>) \<partial>M) = T (\<integral>\<omega>. f \<omega> \<partial>M)"
  by (rule has_bochner_integral_integral_eq
      [OF has_bochner_integral_bounded_linear
        [OF T has_bochner_integral_integrable[OF f]]])

text \<open>A bounded linear map commutes with the Bochner integral, hence with
  set integrals, hence maps martingales to martingales;
  \<open>martingale_of_set_integral_eq\<close> is the right interface, avoiding any
  move of conditional expectations.\<close>

lemma set_integral_of_bounded_linear:
  fixes T :: "'b::{second_countable_topology,banach}
      \<Rightarrow> 'c::{second_countable_topology,banach}"
  assumes T: "bounded_linear T" and f: "set_integrable M A f"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. T (f \<omega>))
      = T (set_lebesgue_integral M A f)"
proof -
  have fe: "(\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R T (f \<omega>))
      = (\<lambda>\<omega>. T (indicat_real A \<omega> *\<^sub>R f \<omega>))"
    by (rule ext) (simp add: T linear_simps)
  have "set_lebesgue_integral M A (\<lambda>\<omega>. T (f \<omega>))
      = (\<integral>\<omega>. T (indicat_real A \<omega> *\<^sub>R f \<omega>) \<partial>M)"
    unfolding set_lebesgue_integral_def by (simp only: fe)
  also have "\<dots> = T (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R f \<omega> \<partial>M)"
    using f by (intro integral_of_bounded_linear[OF T])
      (simp add: set_integrable_def)
  finally show ?thesis unfolding set_lebesgue_integral_def .
qed

lemma martingale_bounded_linear_image:
  fixes T :: "'b::{second_countable_topology,banach}
      \<Rightarrow> 'c::{second_countable_topology,banach}"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes T: "bounded_linear T" and mg: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>u \<omega>. T (Y u \<omega>))"
proof -
  interpret MY: martingale M F t0 Y by (rule mg)
  have Tm: "T \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF T])
  show ?thesis
  proof (rule MY.martingale_of_set_integral_eq)
    show "adapted_process M F t0 (\<lambda>u \<omega>. T (Y u \<omega>))"
    proof (unfold_locales)
      fix i :: real assume i: "t0 \<le> i"
      show "(\<lambda>\<omega>. T (Y i \<omega>)) \<in> borel_measurable (F i)"
        by (rule measurable_compose[OF MY.adapted[OF i] Tm])
    qed
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. T (Y i \<omega>))"
      by (rule integrable_bounded_linear[OF T MY.integrable])
    fix A and i j :: real
    assume A: "A \<in> F i" and ij: "t0 \<le> i" "i \<le> j"
    have Ai: "A \<in> sets M"
      using A MY.subalgebras[OF ij(1)] by (auto simp: subalgebra_def)
    have si: "set_integrable M A (Y i)"
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai MY.integrable[OF ij(1)]])
    have sj: "set_integrable M A (Y j)"
      unfolding set_integrable_def
      using ij by (intro integrable_mult_indicator[OF Ai] MY.integrable) simp
    have base: "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)"
      by (rule MY.set_integral_eq[OF A ij])
    show "set_lebesgue_integral M A (\<lambda>\<omega>. T (Y i \<omega>))
        = set_lebesgue_integral M A (\<lambda>\<omega>. T (Y j \<omega>))"
      using set_integral_of_bounded_linear[OF T si]
        set_integral_of_bounded_linear[OF T sj] base
      by simp
  qed
qed

corollary martingale_vec_nth:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> (real^'n::finite)"
  assumes mg: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>u \<omega>. Y u \<omega> $ i)"
  by (rule martingale_bounded_linear_image[OF bounded_linear_vec_nth mg])

corollary martingale_mat_nth:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> (real^'n::finite^'n)"
  assumes mg: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>u \<omega>. Y u \<omega> $ i $ j)"
  by (rule martingale_vec_nth
      [OF martingale_bounded_linear_image[OF bounded_linear_vec_nth mg]])

section \<open>Vector and matrix martingales, componentwise\<close>

text \<open>Optional stopping is available for real-valued martingales only, so
  the vector-valued state process has to be stopped componentwise and
  reassembled.  Both directions are proved through the set-integral
  characterisation of martingales rather than by pushing conditional
  expectations through the components.\<close>

lemma set_integral_vec_component:
  fixes X :: "'a \<Rightarrow> real^'n::finite"
  assumes A: "A \<in> sets M" and int: "integrable M X"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ k)
    = set_lebesgue_integral M A X $ k"
proof -
  have si: "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega>)"
    by (intro integrable_mult_indicator A int)
  have "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ k)
      = (\<integral>\<omega>. (indicat_real A \<omega> *\<^sub>R X \<omega>) $ k \<partial>M)"
    unfolding set_lebesgue_integral_def by simp
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega> \<partial>M) $ k"
    by (rule integral_bounded_linear[OF bounded_linear_vec_nth si])
  finally show ?thesis
    unfolding set_lebesgue_integral_def .
qed

lemma martingale_vec_component:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  assumes mg: "martingale M F 0 X"
  shows "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ k)"
proof -
  interpret Mg: martingale M F 0 X
    by (rule mg)
  have A_M: "A \<in> sets M" if i: "0 \<le> i" and A: "A \<in> sets (F i)" for A i
  proof -
    have "sets (F i) \<subseteq> sets M"
      using Mg.subalgebras[OF i] by (simp add: subalgebra_def)
    then show ?thesis using A by blast
  qed
  have compmeas: "(\<lambda>\<omega>. X i \<omega> $ k) \<in> borel_measurable (F i)"
    if i: "0 \<le> i" for i
  proof -
    have "(\<lambda>\<omega>. X i \<omega> \<bullet> (axis k 1 :: real^'n))
        \<in> borel_measurable (F i)"
      by (intro borel_measurable_inner borel_measurable_const Mg.adapted[OF i])
    then show ?thesis
      by (simp add: inner_axis)
  qed
  have compint: "integrable M (\<lambda>\<omega>. X i \<omega> $ k)" if i: "0 \<le> i" for i
    by (intro integrable_bounded_linear[OF bounded_linear_vec_nth]
        Mg.integrable i)
  show ?thesis
  proof (rule Mg.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>t \<omega>. X t \<omega> $ k)"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure M F 0"
        by unfold_locales
      show "\<And>i. 0 \<le> i \<Longrightarrow> (\<lambda>\<omega>. X i \<omega> $ k) \<in> borel_measurable (F i)"
        by (rule compmeas)
    qed
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> $ k)"
      by (rule compint)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (F i)"
    have j: "0 \<le> j" using i ij by simp
    have AM: "A \<in> sets M" by (rule A_M[OF i A])
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X i \<omega> $ k)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X j \<omega> $ k)"
      unfolding set_integral_vec_component[OF AM Mg.integrable[OF i]]
        set_integral_vec_component[OF AM Mg.integrable[OF j]]
      using Mg.set_integral_eq[OF A i ij] by simp
  qed
qed

lemma measurable_vec_components [measurable]:
  fixes f :: "'i::finite \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. (\<lambda>x. f i x) \<in> borel_measurable M"
  shows "(\<lambda>x. (\<chi> i. f i x) :: real^'i) \<in> borel_measurable M"
proof (subst borel_measurable_euclidean_space, safe)
  fix b :: "real^'i" assume "b \<in> Basis"
  then obtain i where b: "b = axis i 1"
    by (auto simp: Basis_vec_def)
  show "(\<lambda>x. ((\<chi> i. f i x) :: real^'i) \<bullet> b) \<in> borel_measurable M"
    unfolding b by (simp add: inner_axis assms)
qed

lemma integrable_vec_components:
  fixes f :: "'i::finite \<Rightarrow> 'a \<Rightarrow> real"
  assumes f: "\<And>i. integrable M (f i)"
  shows "integrable M (\<lambda>x. (\<chi> i. f i x) :: real^'i)"
proof -
  have comp: "(\<Sum>k\<in>(UNIV :: 'i set). f k x * axis k 1 $ j) = f j x"
    for x j
  proof -
    have "(\<Sum>k\<in>(UNIV :: 'i set). f k x * axis k 1 $ j)
        = (\<Sum>k\<in>(UNIV :: 'i set). if k = j then f k x else 0)"
      by (intro sum.cong refl) (simp add: axis_def)
    also have "\<dots> = f j x"
      by simp
    finally show ?thesis .
  qed
  have eq: "(\<lambda>x. (\<chi> i. f i x) :: real^'i)
      = (\<lambda>x. \<Sum>i\<in>UNIV. f i x *\<^sub>R axis i 1)"
    by (simp add: fun_eq_iff vec_eq_iff comp)
  show ?thesis
    unfolding eq
    by (intro Bochner_Integration.integrable_sum integrable_scaleR_left f)
qed

lemma martingale_vecI:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  assumes comp: "\<And>k. martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ k)"
  shows "martingale M F 0 X"
proof -
  interpret M0: martingale M F 0 "\<lambda>t \<omega>. X t \<omega> $ (undefined :: 'n)"
    by (rule comp)
  have A_M: "A \<in> sets M" if i: "0 \<le> i" and A: "A \<in> sets (F i)" for A i
  proof -
    have "sets (F i) \<subseteq> sets M"
      using M0.subalgebras[OF i] by (simp add: subalgebra_def)
    then show ?thesis using A by blast
  qed
  have vint: "integrable M (X i)" if i: "0 \<le> i" for i
  proof -
    have "integrable M (\<lambda>\<omega>. (\<chi> k. X i \<omega> $ k) :: real^'n)"
      by (intro integrable_vec_components) (rule martingale.integrable[OF comp i])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule M0.martingale_of_set_integral_eq)
    show "adapted_process M F 0 X"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure M F 0"
        by unfold_locales
      fix i :: real assume i: "0 \<le> i"
      have compmeas: "(\<lambda>\<omega>. X i \<omega> $ k) \<in> borel_measurable (F i)"
        for k
      proof -
        interpret Mk: martingale M F 0 "\<lambda>t \<omega>. X t \<omega> $ k"
          by (rule comp)
        show ?thesis
          by (rule Mk.adapted[OF i])
      qed
      have "(\<lambda>\<omega>. (\<chi> k. X i \<omega> $ k) :: real^'n)
          \<in> borel_measurable (F i)"
        by (intro measurable_vec_components compmeas)
      then show "X i \<in> borel_measurable (F i)"
        by simp
    qed
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (X i)"
      by (rule vint)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (F i)"
    have j: "0 \<le> j" using i ij by simp
    have AM: "A \<in> sets M" by (rule A_M[OF i A])
    have "set_lebesgue_integral M A (X i) $ k
        = set_lebesgue_integral M A (X j) $ k" for k
    proof -
      have "set_lebesgue_integral M A (X i) $ k
          = set_lebesgue_integral M A (\<lambda>\<omega>. X i \<omega> $ k)"
        by (rule set_integral_vec_component[OF AM vint[OF i], symmetric])
      also have "\<dots> = set_lebesgue_integral M A (\<lambda>\<omega>. X j \<omega> $ k)"
        by (rule martingale.set_integral_eq[OF comp A i ij])
      also have "\<dots> = set_lebesgue_integral M A (X j) $ k"
        by (rule set_integral_vec_component[OF AM vint[OF j]])
      finally show ?thesis .
    qed
    then show "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)"
      by (simp add: vec_eq_iff)
  qed
qed

text \<open>\<open>Ito_Market.martingale_vecI\<close> is stated for \<open>real^'n\<close>, and its three
  helpers are all specific to real entries, so it does not iterate to
  \<open>real^'n^'n\<close>.  The three matrix analogues are proved here directly from
  the euclidean structure: \<open>Basis\<close> of a matrix consists of the
  \<open>axis i (axis j 1)\<close>, and \<open>A \<bullet> axis i (axis j 1) = A $ i $ j\<close>.\<close>

lemma mat_inner_axis:
  fixes A :: "real^'n::finite^'n"
  shows "A \<bullet> axis i (axis j 1) = A $ i $ j"
  by (simp add: inner_axis)

lemma mat_Basis_cases:
  fixes b :: "real^'n::finite^'n"
  assumes "b \<in> Basis"
  obtains i j where "b = axis i (axis j 1)"
  using assms by (auto simp: Basis_vec_def)

lemma measurable_mat_entries:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes ent: "\<And>i j. (\<lambda>\<omega>. X \<omega> $ i $ j) \<in> borel_measurable M"
  shows "X \<in> borel_measurable M"
proof (subst borel_measurable_euclidean_space, safe)
  fix b :: "real^'n^'n" assume "b \<in> Basis"
  then obtain i j where b: "b = axis i (axis j 1)" by (rule mat_Basis_cases)
  show "(\<lambda>\<omega>. X \<omega> \<bullet> b) \<in> borel_measurable M"
    unfolding b by (simp add: mat_inner_axis ent)
qed

lemma integrable_mat_entries:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes m: "X \<in> borel_measurable M"
    and ent: "\<And>i j. integrable M (\<lambda>\<omega>. X \<omega> $ i $ j)"
  shows "integrable M X"
proof (rule Bochner_Integration.integrable_bound
    [where f = "\<lambda>\<omega>. (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"])
  show "integrable M (\<lambda>\<omega>. (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>))"
  proof (intro Bochner_Integration.integrable_sum integrable_abs)
    fix b :: "real^'n^'n" assume "b \<in> Basis"
    then obtain i j where b: "b = axis i (axis j 1)" by (rule mat_Basis_cases)
    show "integrable M (\<lambda>\<omega>. X \<omega> \<bullet> b)"
      unfolding b by (simp add: mat_inner_axis ent)
  qed
  show "X \<in> borel_measurable M" by (rule m)
  show "AE \<omega> in M. norm (X \<omega>)
      \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
  proof (intro always_eventually allI)
    fix \<omega> :: 'a
    have "norm (X \<omega>) \<le> (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
      by (rule norm_le_l1)
    also have "\<dots> \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
      by simp
    finally show "norm (X \<omega>)
        \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)" .
  qed
qed

lemma set_integral_mat_component:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes A: "A \<in> sets M" and int: "integrable M X"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ i $ j)
      = set_lebesgue_integral M A X $ i $ j"
proof -
  have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ j)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  have si: "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega>)"
    by (intro integrable_mult_indicator A int)
  have "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ i $ j)
      = (\<integral>\<omega>. (indicat_real A \<omega> *\<^sub>R X \<omega>) $ i $ j \<partial>M)"
    unfolding set_lebesgue_integral_def by simp
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega> \<partial>M) $ i $ j"
    by (rule has_bochner_integral_integral_eq
        [OF has_bochner_integral_bounded_linear
          [OF bl has_bochner_integral_integrable[OF si]]])
  finally show ?thesis
    unfolding set_lebesgue_integral_def .
qed

lemma martingale_matI:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite^'n"
  assumes comp: "\<And>i j. martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ i $ j)"
  shows "martingale M F 0 X"
proof -
  interpret M0: martingale M F 0
      "\<lambda>t \<omega>. X t \<omega> $ (undefined :: 'n) $ (undefined :: 'n)"
    by (rule comp)
  have A_M: "A \<in> sets M" if u: "0 \<le> u" and A: "A \<in> sets (F u)" for A u
  proof -
    have "sets (F u) \<subseteq> sets M"
      using M0.subalgebras[OF u] by (simp add: subalgebra_def)
    then show ?thesis using A by blast
  qed
  have entmeas: "(\<lambda>\<omega>. X u \<omega> $ i $ j) \<in> borel_measurable (F u)"
    if u: "0 \<le> u" for u i j
  proof -
    interpret Mij: martingale M F 0 "\<lambda>t \<omega>. X t \<omega> $ i $ j" by (rule comp)
    show ?thesis by (rule Mij.adapted[OF u])
  qed
  have entint: "integrable M (\<lambda>\<omega>. X u \<omega> $ i $ j)" if u: "0 \<le> u" for u i j
    by (rule martingale.integrable[OF comp u])
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_mat_entries)
      (rule borel_measurable_integrable[OF entint[OF u]])
  have vint: "integrable M (X u)" if u: "0 \<le> u" for u
    by (rule integrable_mat_entries[OF Xm[OF u]]) (rule entint[OF u])
  show ?thesis
  proof (rule M0.martingale_of_set_integral_eq)
    show "adapted_process M F 0 X"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure M F 0" by unfold_locales
      fix u :: real assume u: "0 \<le> u"
      show "X u \<in> borel_measurable (F u)"
        by (rule measurable_mat_entries) (rule entmeas[OF u])
    qed
    show "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (X u)" by (rule vint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u)"
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets M" by (rule A_M[OF u A])
    have "set_lebesgue_integral M A (X u) $ i $ j
        = set_lebesgue_integral M A (X v) $ i $ j" for i j
    proof -
      have "set_lebesgue_integral M A (X u) $ i $ j
          = set_lebesgue_integral M A (\<lambda>\<omega>. X u \<omega> $ i $ j)"
        by (rule set_integral_mat_component[OF AM vint[OF u], symmetric])
      also have "\<dots> = set_lebesgue_integral M A (\<lambda>\<omega>. X v \<omega> $ i $ j)"
        by (rule martingale.set_integral_eq[OF comp A u uv])
      also have "\<dots> = set_lebesgue_integral M A (X v) $ i $ j"
        by (rule set_integral_mat_component[OF AM vint[OF v]])
      finally show ?thesis .
    qed
    then show "set_lebesgue_integral M A (X u) = set_lebesgue_integral M A (X v)"
      by (simp add: vec_eq_iff)
  qed
qed

text \<open>The matrix-entry analogue of \<open>martingale_vec_component\<close>, which is
  typed for real entries and so does not reach a matrix-valued process;
  this just assembles the three ingredients above.\<close>

lemma martingale_mat_component:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite^'n"
  assumes mg: "martingale M F 0 X"
  shows "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ c $ d)"
proof -
  interpret Mg: martingale M F 0 X by (rule mg)
  have A_M: "A \<in> sets M" if i: "0 \<le> i" and A: "A \<in> sets (F i)" for A i
  proof -
    have "sets (F i) \<subseteq> sets M"
      using Mg.subalgebras[OF i] by (simp add: subalgebra_def)
    then show ?thesis using A by blast
  qed
  have bl: "bounded_linear (\<lambda>Z :: real^'n^'n. Z $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
  have compmeas: "(\<lambda>\<omega>. X i \<omega> $ c $ d) \<in> borel_measurable (F i)"
    if i: "0 \<le> i" for i
  proof -
    have "(\<lambda>\<omega>. X i \<omega> \<bullet> (axis c (axis d 1) :: real^'n^'n))
        \<in> borel_measurable (F i)"
      by (intro borel_measurable_inner borel_measurable_const Mg.adapted[OF i])
    then show ?thesis by (simp add: inner_axis)
  qed
  have compint: "integrable M (\<lambda>\<omega>. X i \<omega> $ c $ d)" if i: "0 \<le> i" for i
    by (rule integrable_bounded_linear[OF bl Mg.integrable[OF i]])
  show ?thesis  proof (rule Mg.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>t \<omega>. X t \<omega> $ c $ d)"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure M F 0" by unfold_locales
      show "\<And>i. 0 \<le> i \<Longrightarrow> (\<lambda>\<omega>. X i \<omega> $ c $ d) \<in> borel_measurable (F i)"
        by (rule compmeas)
    qed
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> $ c $ d)" by (rule compint)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (F i)"
    have j: "0 \<le> j" using i ij by simp
    have AM: "A \<in> sets M" by (rule A_M[OF i A])
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X i \<omega> $ c $ d)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X j \<omega> $ c $ d)"
      unfolding set_integral_mat_component[OF AM Mg.integrable[OF i]]
        set_integral_mat_component[OF AM Mg.integrable[OF j]]
      using Mg.set_integral_eq[OF A i ij] by simp
  qed
qed

section \<open>Multiplying by an initial-time-measurable factor\<close>

text \<open>"Pulling out what is known": the AFP's conditional-expectation lemma
  \<open>cond_exp_measurable_mult\<close> does the work.  The factor must be measurable
  for the filtration at the initial time, not merely somewhere along it, or
  it is not adapted.\<close>

lemma martingale_mult_measurable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and v :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F (0::real) X"
    and vm: "v \<in> borel_measurable (F 0)"
    and int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. v \<omega> * X u \<omega>)"
  shows "martingale M F 0 (\<lambda>u \<omega>. v \<omega> * X u \<omega>)"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have FM: "filtered_measure M F (0::real)" by unfold_locales
  have vFu: "v \<in> borel_measurable (F u)" if u: "0 \<le> u" for u
  proof -
    have "subalgebra (F u) (F 0)"
      using MG.subalgebras[OF u] MG.subalgebras[OF order_refl]
        MG.sets_F_mono[OF order_refl u]
      by (simp add: subalgebra_def)
    then show ?thesis by (rule measurable_from_subalg[OF _ vm])
  qed
  have pm: "(\<lambda>\<omega>. v \<omega> * X u \<omega>) \<in> borel_measurable (F u)" if u: "0 \<le> u" for u
    using vFu[OF u] MG.adapted[OF u] by simp
  show ?thesis
  proof (rule MG.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>u \<omega>. v \<omega> * X u \<omega>)"
      unfolding adapted_process_def adapted_process_axioms_def
      using FM pm by blast
    show "integrable M (\<lambda>\<omega>. v \<omega> * X i \<omega>)" if "0 \<le> i" for i by (rule int[OF that])
    fix C and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and C: "C \<in> sets (F i)"
    have j0: "0 \<le> j" using ij by simp
    interpret SF: sigma_finite_subalgebra M "F i" using ij(1) by blast
    have CM: "C \<in> sets M" using C MG.sets_F_subset[OF ij(1)] by blast
    have ae1: "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega>
        = v \<omega> * cond_exp M (F i) (X j) \<omega>"
      by (rule SF.cond_exp_measurable_mult(2)
          [OF int[OF j0] MG.integrable[OF j0] vFu[OF ij(1)]])
    have ae2: "AE \<omega> in M. X i \<omega> = cond_exp M (F i) (X j) \<omega>"
      by (rule MG.martingale_property[OF ij(1) ij(2)])
    have ae: "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega> = v \<omega> * X i \<omega>"
      using ae1 ae2 by eventually_elim simp
    have aeC: "AE \<omega>\<in>C in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega> = v \<omega> * X i \<omega>"
      using ae by (auto elim: eventually_mono)
    have m1: "cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<in> borel_measurable M"
      by (rule SF.borel_measurable_cond_exp')
    have m2: "(\<lambda>\<omega>. v \<omega> * X i \<omega>) \<in> borel_measurable M"
      using int[OF ij(1)] by simp
    have "set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X j \<omega>)
        = set_lebesgue_integral M C (cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>))"
      by (rule SF.cond_exp_set_integral[OF int[OF j0] C])
    also have "\<dots> = set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X i \<omega>)"
      by (rule set_lebesgue_integral_cong_AE[OF CM m1 m2 aeC])
    finally show "set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X i \<omega>)
        = set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X j \<omega>)" ..
  qed
qed

text \<open>The matrix-valued cross term \<open>X \<otimes> v + v \<otimes> X\<close> is a martingale, entry
  by entry, as a sum of two applications of \<open>martingale_mult_measurable\<close>.\<close>

lemma martingale_cross_measurable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" and v :: "'a \<Rightarrow> real^'n"
  assumes mg: "\<And>i. martingale M F (0::real) (\<lambda>t \<omega>. X t \<omega> $ i)"
    and vm: "\<And>j. (\<lambda>\<omega>. v \<omega> $ j) \<in> borel_measurable (F 0)"
    and int: "\<And>u i j. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. v \<omega> $ j * X u \<omega> $ i)"
  shows "martingale M F 0
      (\<lambda>t \<omega>. (\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j))"
proof (rule martingale_matI)
  fix p q :: 'n
  have mgp: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ p)" by (rule mg)
  have mgq: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ q)" by (rule mg)
  have vmp: "(\<lambda>\<omega>. v \<omega> $ p) \<in> borel_measurable (F 0)" by (rule vm)
  have vmq: "(\<lambda>\<omega>. v \<omega> $ q) \<in> borel_measurable (F 0)" by (rule vm)
  have intqp: "integrable M (\<lambda>\<omega>. v \<omega> $ q * X u \<omega> $ p)" if "0 \<le> u" for u
    by (rule int[OF that])
  have intpq: "integrable M (\<lambda>\<omega>. v \<omega> $ p * X u \<omega> $ q)" if "0 \<le> u" for u
    by (rule int[OF that])
  have m1: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p)"
    by (rule martingale_mult_measurable[OF mgp vmq intqp])
  have m2: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ p * X t \<omega> $ q)"
    by (rule martingale_mult_measurable[OF mgq vmp intpq])
  have m: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q)"
    by (rule martingale_add[OF m1 m2])
  have eq: "(\<lambda>t \<omega>. ((\<chi> i j. X t \<omega> $ i * v \<omega> $ j)
        + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q)
      = (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q)"
  proof (intro ext)
    fix t :: real and \<omega>
    show "((\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q
        = v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q"
      by (simp add: mult.commute)
  qed
  show "martingale M F 0 (\<lambda>t \<omega>.
      ((\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q)"
    unfolding eq by (rule m)
qed

section \<open>Stopping at a deterministic time\<close>

lemma martingale_stopped_const:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes T: "0 \<le> T" and mg: "martingale M F 0 X"
  shows "martingale M F 0 (\<lambda>u \<omega>. X (min u T) \<omega>)"
proof -
  interpret MX: martingale M F 0 X by (rule mg)
  have mu: "0 \<le> min u T" if "0 \<le> u" for u using that T by simp
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>u \<omega>. X (min u T) \<omega>)"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      have "X (min u T) \<in> borel_measurable (F (min u T))"
        by (rule MX.adapted[OF mu[OF u]])
      moreover have "borel_measurable (F (min u T)) \<subseteq> borel_measurable (F u)"
        by (rule MX.borel_measurable_mono[OF mu[OF u]]) simp
      ultimately show "X (min u T) \<in> borel_measurable (F u)" by blast
    qed
    show "integrable M (\<lambda>\<omega>. X (min u T) \<omega>)" if u: "0 \<le> u" for u
      using MX.integrable[OF mu[OF u]] by simp
    fix A and u v :: real
    assume A: "A \<in> F u" and uv: "0 \<le> u" "u \<le> v"
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X (min u T) \<omega>)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X (min v T) \<omega>)"
    proof (cases "u \<le> T")
      case True
      then have mu': "min u T = u" by simp
      show ?thesis
      proof (cases "v \<le> T")
        case True
        then have mv': "min v T = v" by simp
        show ?thesis unfolding mu' mv'
          using MX.set_integral_eq[OF A uv] by simp
      next
        case False
        then have mv': "min v T = T" by simp
        show ?thesis unfolding mu' mv'
          using MX.set_integral_eq[OF A uv(1) True] by simp
      qed
    next
      case False
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    qed
  qed
qed

section \<open>Mean, from a zero start\<close>

text \<open>A martingale that starts at \<open>0\<close> has mean \<open>0\<close> at every later time; the
  set-integral identity over the whole space is the case \<open>i = 0\<close> of the
  martingale property.\<close>

lemma martingale_mean_zero_of_start:
  fixes M :: "'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) Z"
    and z0: "AE \<omega> in M. Z 0 \<omega> = 0" and u: "0 \<le> u"
  shows "(\<integral>\<omega>. Z u \<omega> \<partial>M) = 0"
proof -
  interpret MG: martingale M F "0::real" Z by (rule mg)
  have sub: "subalgebra M (F 0)" by (rule MG.subalgebras[OF order.refl])
  have spF: "space (F 0) = space M" using sub by (simp add: subalgebra_def)
  have top: "space M \<in> sets (F 0)" using sets.top[of "F 0"] spF by simp
  have i0: "integrable M (Z 0)" by (rule MG.integrable[OF order.refl])
  have iu: "integrable M (Z u)" by (rule MG.integrable[OF u])
  have m0: "Z 0 \<in> borel_measurable M"
    using i0 by (simp add: borel_measurable_integrable)
  have "(\<integral>\<omega>. Z u \<omega> \<partial>M) = set_lebesgue_integral M (space M) (Z u)"
    by (rule set_integral_space[OF iu, symmetric])
  also have "\<dots> = set_lebesgue_integral M (space M) (Z 0)"
    by (rule MG.set_integral_eq[OF top order.refl u, symmetric])
  also have "\<dots> = (\<integral>\<omega>. Z 0 \<omega> \<partial>M)" by (rule set_integral_space[OF i0])
  also have "\<dots> = (\<integral>\<omega>. 0 \<partial>M)"
    by (rule integral_cong_AE[OF m0 borel_measurable_const z0])
  finally show ?thesis by simp
qed

section \<open>A boundedness test for a martingale contracted against a factor\<close>

lemma martingale_bounded_test:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and Z :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F (0::real) Y"
    and st: "0 \<le> s" and ts: "s \<le> t"
    and Zm: "Z \<in> borel_measurable (F s)"
    and int_t: "integrable M (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)"
    and int_s: "integrable M (\<lambda>\<omega>. Z \<omega> * Y s \<omega>)"
  shows "(\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M) = (\<integral>\<omega>. Z \<omega> * Y s \<omega> \<partial>M)"
proof -
  interpret MY: martingale M F 0 Y by (rule mg)
  have t0: "0 \<le> t" using st ts by linarith
  interpret sfs: sigma_finite_subalgebra M "F s"
    by (rule MY.sigma_finite_subalgebra_F[OF st])
  have sp: "space M \<in> sets (F s)"
    using sets.top[of "F s"] MY.space_F[OF st] by simp
  have mp: "AE \<omega> in M. Y s \<omega> = cond_exp M (F s) (Y t) \<omega>"
    by (rule MY.martingale_property[OF st ts])
  have ZM: "Z \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st] Zm])
  have cM: "cond_exp M (F s) (Y t) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st]
        borel_measurable_cond_exp])
  have cPM: "cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st]
        borel_measurable_cond_exp])
  have m1: "(\<lambda>\<omega>. Z \<omega> * Y s \<omega>) \<in> borel_measurable M"
    by (rule borel_measurable_integrable[OF int_s])
  have m2: "(\<lambda>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_times ZM cM)
  have e1: "(\<integral>\<omega>. Z \<omega> * Y s \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega> \<partial>M)"
    using mp by (intro integral_cong_AE m1 m2) auto
  have mult: "AE \<omega> in M. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega>
      = Z \<omega> * cond_exp M (F s) (Y t) \<omega>"
    by (rule sfs.cond_exp_measurable_mult(2)[OF int_t MY.integrable[OF t0] Zm])
  have e2: "(\<integral>\<omega>. Z \<omega> * cond_exp M (F s) (Y t) \<omega> \<partial>M)
      = (\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)"
    using mult by (intro integral_cong_AE m2 cPM) auto
  have e3: "(\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)
      = (\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M)"
  proof -
    have s1: "set_lebesgue_integral M (space M)
        (cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>))
        = set_lebesgue_integral M (space M) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)"
      using sfs.cond_exp_set_integral[OF int_t sp] by simp
    have s2: "set_lebesgue_integral M (space M)
        (cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>))
        = (\<integral>\<omega>. cond_exp M (F s) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>) \<omega> \<partial>M)"
      by (rule set_integral_space[OF integrable_cond_exp])
    have s3: "set_lebesgue_integral M (space M) (\<lambda>\<omega>. Z \<omega> * Y t \<omega>)
        = (\<integral>\<omega>. Z \<omega> * Y t \<omega> \<partial>M)"
      by (rule set_integral_space[OF int_t])
    show ?thesis using s1 s2 s3 by simp
  qed
  from e1 e2 e3 show ?thesis by simp
qed

(*<*)
end
(*>*)
