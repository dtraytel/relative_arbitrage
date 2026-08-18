section \<open>Clause (2): the value function is a viscosity solution\<close>

(*<*)
theory Value_Function_Assembly
  imports Value_Function_Tangential_Field
begin

(*>*)

section \<open>Clause (2): the value function is a viscosity solution\<close>

text \<open>\<open>enn2real \<circ> exit_val k L T K\<close> is a viscosity solution of Eq. (1.9) on
  \<open>interior K\<close>: an ordinary subsolution (@{thm [source] exit_val_visc_subsol})
  and, in the enveloped sense of Definition 3.1(b), a supersolution
  (@{thm [source] exit_val_supersol_lsc}), where the lower semicontinuous
  envelope replaces \<open>v\<close> because the plain supersolution property fails
  wherever \<open>v\<close> has an interior local minimum.  Both proofs are pathwise,
  built by Euler pasting of endpoint-frozen Gaussian kernels rather than
  stochastic integrals or SDE well-posedness.  The supersolution assumes
  the horizon does not bind on the interior, \<open>v\<^sub>*(x) < T/2\<close>, which for a
  bounded \<open>K\<close> holds automatically once \<open>T\<close> is large enough
  (@{thm [source] exit_val_le_ball_bound}).\<close>

subsection \<open>The sharp ball lower bound at rate \<open>m - 1\<close>\<close>

text \<open>@{thm [source] radial_sq_upto} transports the growth identity to the
  endpoint of a half-open confinement interval.  Nothing in its proof is
  specific to \<open>\<lambda>w. (norm (w - y\<^sub>0))\<^sup>2\<close> --- any continuous functional of the
  position does --- and the sharp bound below needs it for the projected
  square as well.\<close>

lemma radial_sq_upto_gen:
  fixes \<omega> :: "'n::finite pairpath" and TT e c0 cn :: real
    and RO :: "(real^'n) set" and F :: "real^'n \<Rightarrow> real"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ('n pairpath) metric)"
    and Fc: "continuous_on UNIV F"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow> F (fst (\<omega> t)) = c0 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "F (fst (\<omega> e)) = c0 + e * cn"
proof -
  define g where "g = (\<lambda>s. F (fst (\<omega> s)))"
  have gc: "continuous_on {0..TT} g"
  proof -
    have wc: "continuous_on {0..TT} \<omega>"
      by (rule mspace_path_metricD[OF wm])
    have fc: "continuous_on {0..TT} (\<lambda>s. fst (\<omega> s))"
      by (rule continuous_on_fst[OF wc])
    show ?thesis
      unfolding g_def by (rule continuous_on_compose2[OF Fc fc]) auto
  qed
  define tj where "tj = (\<lambda>j. e - e / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "e / (2 * real (Suc j)) \<le> e / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> e" using e0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using e0 by linarith
  qed
  have tju: "tj j < e" for j
  proof -
    have "0 < e / (2 * real (Suc j))" using e0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjT: "tj j \<le> TT" for j using tju[of j] eT by linarith
  have glow: "g (tj j) = c0 + tj j * cn" for j
    unfolding g_def
  proof (rule grow)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> TT" by (rule tjT)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < e" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inside)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> e"
  proof -
    have eq: "(\<lambda>j. (e / 2) * inverse (real (Suc j)))
        = (\<lambda>j. e / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (e / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (e / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. e / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. e - e / (2 * real (Suc j))) \<longlonglongrightarrow> e - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g e"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..TT}"
      using tjl tjT by (auto intro: less_imp_le)
    have eS: "e \<in> {0..TT}" using e0 eT by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g e"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS eS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have vlim: "(\<lambda>j. c0 + tj j * cn) \<longlonglongrightarrow> c0 + e * cn"
    by (intro tendsto_add tendsto_const tendsto_mult tjlim)
  have "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> c0 + e * cn"
    using vlim unfolding glow by simp
  then have "g e = c0 + e * cn"
    using gcomp LIMSEQ_unique by blast
  then show ?thesis unfolding g_def .
qed

text \<open>The subspace-tangential member confines the path to
  \<open>cball 0 rB \<subseteq> K\<close> for any deterministic time \<open>cc\<close> strictly below
  \<open>\<delta> = (rB\<^sup>2 - |x|\<^sup>2)/(m-1)\<close>.  The inner barrier is unreachable because the
  projected square only grows, and the outer sphere pins the time exactly
  because the full square grows at the same rate --- that is what the
  upgraded @{thm [source] subspace_tangential_exact_growth} delivers.
  Feeding the constant-time DPP gives \<open>cc \<le> v(x)\<close>, and \<open>cc\<close> is a free
  parameter, so no factor \<open>2\<close> and no \<open>T/2\<close> cap survive: letting
  \<open>cc \<longrightarrow> min T \<delta>\<close> is the corollary below.\<close>
theorem exit_val_ball_lower_subspace:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T cc :: real
  assumes T0: "0 < T" and L1: "1 \<le> L"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and mk: "CARD('n) - k \<le> m - 1" and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
    and cc0: "0 < cc" and ccT: "cc < T"
    and ccdf: "cc < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  shows "ennreal cc \<le> exit_val k L T K x"
proof -
  define \<rho>\<^sub>0 where "\<rho>\<^sub>0 = norm x"
  define \<rho> where "\<rho> = \<rho>\<^sub>0 / 2"
  define cn where "cn = real m - 1"
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2) / cn"
  let ?RO = "{w :: real^'n. \<rho> < norm (projmat b m *v w)} \<inter> ball 0 rB"
  have r00: "0 < \<rho>\<^sub>0" unfolding \<rho>\<^sub>0_def using xnz by simp
  have rho0: "0 < \<rho>" unfolding \<rho>_def using r00 by simp
  have cn1: "1 \<le> cn"
  proof -
    have "(2::real) \<le> real m"
      using m2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis unfolding cn_def by linarith
  qed
  have cn0: "0 < cn" using cn1 by linarith
  have rr: "\<rho>\<^sub>0 < rB" using xin unfolding \<rho>\<^sub>0_def .
  have rB0: "0 < rB" using r00 rr by linarith
  have sq_lt: "\<rho>\<^sub>0\<^sup>2 < rB\<^sup>2"
    using r00 rr by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have ccdf': "cc < \<delta>f" using ccdf unfolding \<delta>f_def cn_def \<rho>\<^sub>0_def .
  have cc0': "0 \<le> cc" using cc0 by linarith
  have Psym: "transpose (projmat b m) = projmat b m" by (rule projmat_sym)
  have Pidem: "projmat b m ** projmat b m = projmat b m"
    by (rule projmat_idem[OF orth])
  have mvc: "continuous_on UNIV (\<lambda>w :: real^'n. projmat b m *v w)"
    by (simp add: linear_continuous_on
        linear_linear)
  have Fpc: "continuous_on UNIV (\<lambda>w :: real^'n. (norm (projmat b m *v w))\<^sup>2)"
    by (intro continuous_intros mvc)
  have Fnc: "continuous_on UNIV (\<lambda>w :: real^'n. (norm w)\<^sup>2)"
    by (intro continuous_intros)
  obtain P where P: "P \<in> exit_class k L T x"
    and AEg: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<longrightarrow>
      (norm (projmat b m *v fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)
        \<and> (norm (fst (\<omega> t)))\<^sup>2 = (norm x)\<^sup>2 + t * (real m - 1)"
    using subspace_tangential_exact_growth[OF T0 L1 rho0 orth mk xfix,
        where rB = rB]
    by blast
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF P])
  have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have start: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule exit_class_start[OF P])
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  have AEfun: "AE \<omega> in P. ennreal cc
      \<le> ennreal (pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))"
    using AEg start sp
  proof (eventually_elim)
    case (elim \<omega>)
    have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using elim(3) by (simp add: spaceP)
    have x0: "fst (\<omega> 0) = x" using elim(2) by blast
    have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      by (rule path_sets_fst_continuous[OF setsP])
        (use elim(3) in simp)
    have growp: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (projmat b m *v fst (\<omega> t)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + t * cn"
      unfolding cn_def \<rho>\<^sub>0_def using elim(1) by blast
    have grown: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (fst (\<omega> t)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + t * cn"
      unfolding cn_def \<rho>\<^sub>0_def using elim(1) by blast
    have xRO: "x \<in> ?RO"
    proof -
      have "norm (projmat b m *v x) = \<rho>\<^sub>0" unfolding xfix \<rho>\<^sub>0_def by (rule refl)
      then show ?thesis
        using rho0 rr r00 unfolding \<rho>_def \<rho>\<^sub>0_def
        by (auto simp: dist_norm)
    qed
    have ROopen: "open ?RO"
    proof -
      have pc: "continuous_on UNIV (\<lambda>w :: real^'n. norm (projmat b m *v w))"
        using mvc by (rule continuous_on_norm)
      have "open {w :: real^'n. \<rho> < norm (projmat b m *v w)}"
        by (rule open_Collect_less[OF continuous_on_const pc])
      then show ?thesis by (intro open_Int open_ball)
    qed
    have contc: "continuous_on {0..cc} (\<lambda>t. fst (\<omega> t))"
      by (rule continuous_on_subset[OF cont]) (use ccT in auto)
    \<comment> \<open>the path stays in the annulus strictly before \<open>cc\<close>\<close>
    have IN: "fst (\<omega> s) \<in> ?RO" if s0: "0 \<le> s" and sc: "s < cc" for s
    proof -
      define e where "e = pexit cc ?RO (\<lambda>t. fst (\<omega> t))"
      have eup: "e \<le> cc" unfolding e_def by (rule pexit_le_T[OF cc0'])
      have before: "fst (\<omega> u) \<in> ?RO"
        if u0: "0 \<le> u" and ue: "u < e" for u
      proof (rule ccontr)
        assume nb: "fst (\<omega> u) \<notin> ?RO"
        have uc: "u \<le> cc" using ue eup by linarith
        have "pexit cc ?RO (\<lambda>t. fst (\<omega> t)) \<le> u"
          by (rule pexit_le_of_mem[OF cc0' u0 uc]) (use nb in simp)
        then show False using ue unfolding e_def by linarith
      qed
      have ecc: "e = cc"
      proof (rule ccontr)
        assume "e \<noteq> cc"
        then have elt: "e < cc" using eup by linarith
        have Xe: "fst (\<omega> e) \<notin> ?RO"
          using pexit_mem_of_less_T[OF cc0' ROopen contc]
          using elt unfolding e_def by simp
        have e0': "0 < e"
        proof (rule ccontr)
          assume "\<not> 0 < e"
          moreover have "0 \<le> e"
            unfolding e_def by (rule pexit_nonneg[OF cc0'])
          ultimately have "e = 0" by linarith
          then show False using Xe x0 xRO by simp
        qed
        have eT': "e \<le> T" using elt ccT by linarith
        have esqp: "(norm (projmat b m *v fst (\<omega> e)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + e * cn"
          by (rule radial_sq_upto_gen[OF wm Fpc growp e0' eT' before])
        have esqn: "(norm (fst (\<omega> e)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + e * cn"
          by (rule radial_sq_upto_gen[OF wm Fnc grown e0' eT' before])
        have dichot: "norm (projmat b m *v fst (\<omega> e)) \<le> \<rho>
            \<or> rB \<le> norm (fst (\<omega> e))"
          using Xe by (auto simp: dist_norm)
        show False
        proof (cases rule: disjE[OF dichot])
          case 1
          have "(norm (projmat b m *v fst (\<omega> e)))\<^sup>2 \<le> \<rho>\<^sup>2"
            using 1 rho0 by (intro power_mono) simp_all
          moreover have "\<rho>\<^sup>2 < \<rho>\<^sub>0\<^sup>2"
            unfolding \<rho>_def using r00 by (simp add: power_divide)
          moreover have "\<rho>\<^sub>0\<^sup>2 \<le> (norm (projmat b m *v fst (\<omega> e)))\<^sup>2"
            unfolding esqp using e0' cn0 by simp
          ultimately show False by linarith
        next
          case 2
          have "rB\<^sup>2 \<le> (norm (fst (\<omega> e)))\<^sup>2"
            using 2 rB0 by (intro power_mono) simp_all
          then have "rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2 \<le> e * cn" unfolding esqn by linarith
          then have "\<delta>f \<le> e"
            unfolding \<delta>f_def using cn0 by (simp add: pos_divide_le_eq)
          then show False using elt ccdf' by linarith
        qed
      qed
      show ?thesis using before[OF s0] sc unfolding ecc by simp
    qed
    \<comment> \<open>hence in \<open>K\<close> through \<open>cc\<close>, including the endpoint\<close>
    have inB: "fst (\<omega> s) \<in> ball (0 :: real^'n) rB"
      if s0: "0 \<le> s" and sc: "s \<le> cc" for s
    proof (cases "s < cc")
      case True
      show ?thesis using IN[OF s0 True] by blast
    next
      case False
      then have seq: "s = cc" using sc by linarith
      have csq: "(norm (fst (\<omega> cc)))\<^sup>2 = \<rho>\<^sub>0\<^sup>2 + cc * cn"
      proof (rule radial_sq_upto_gen[OF wm Fnc grown cc0])
        show "cc \<le> T" using ccT by linarith
        show "\<And>s. 0 \<le> s \<Longrightarrow> s < cc \<Longrightarrow> fst (\<omega> s) \<in> ?RO" by (rule IN)
      qed
      have "(norm (fst (\<omega> cc)))\<^sup>2 < rB\<^sup>2"
      proof -
        have "cc * cn < \<delta>f * cn"
          using ccdf' cn0 by (intro mult_strict_right_mono)
        also have "\<delta>f * cn = rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2"
          unfolding \<delta>f_def using cn0 by simp
        finally show ?thesis unfolding csq by linarith
      qed
      then have "norm (fst (\<omega> cc)) < rB"
        using rB0 by (metis power2_le_imp_le
            linorder_not_less nless_le)
      then have "fst (\<omega> cc) \<in> ball (0 :: real^'n) rB"
        by (simp add: dist_norm)
      then show ?thesis unfolding seq .
    qed
    have inK: "fst (\<omega> s) \<in> K" if s0: "0 \<le> s" and sc: "s \<le> cc" for s
      using inB[OF s0 sc] sub ball_subset_cball by blast
    have pex: "pexit cc K (\<lambda>t. fst (\<omega> t)) = cc"
      by (rule pexit_eq_of_stays[OF cc0']) (use inK in simp)
    have XccK: "fst (\<omega> cc) \<in> K" using inK[of cc] cc0 by simp
    have fn: "pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0)
        = cc + enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))"
      using pex XccK by simp
    have "cc \<le> cc + enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))" by simp
    then show ?case unfolding fn by (intro ennreal_leI) simp
  qed
  have essge: "ennreal cc \<le> ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))"
    unfolding ess_inf_time_def
    by (rule Sup_upper) (use AEfun in blast)
  have esle: "ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))
      \<le> exit_val k L T K x"
  proof -
    have "ess_inf_time P
        (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
          + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
             then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc))) else 0))
        \<le> (SUP P' \<in> exit_class k L T x. ess_inf_time P'
          (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
            + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
               then enn2real (exit_val k L (T - cc) K (fst (\<omega> cc)))
               else 0)))"
      by (rule SUP_upper[OF P])
    also have "\<dots> \<le> exit_val k L T K x"
      by (rule exit_val_dpp_sup_ge[OF cc0' ccT L1 Kc])
    finally show ?thesis .
  qed
  show ?thesis by (rule order_trans[OF essge esle])
qed

text \<open>Letting \<open>cc \<longrightarrow> min T \<delta>\<close> removes the last slack.  This is the sharp
  interior lower bound Example 3.1 asks for: at rate \<open>m - 1\<close>, with no factor
  \<open>2\<close> and no \<open>T/2\<close> cap.\<close>

corollary exit_val_ball_lower_sharp:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and b :: "nat \<Rightarrow> real^'n" and rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L"
    and Kc: "closed K" and sub: "cball 0 rB \<subseteq> K"
    and xnz: "x \<noteq> 0" and xin: "norm x < rB"
    and orth: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> b i \<bullet> b j = (if i = j then 1 else 0)"
    and mk: "CARD('n) - k \<le> m - 1" and m2: "2 \<le> m"
    and xfix: "projmat b m *v x = x"
  shows "ennreal (min T ((rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)))
      \<le> exit_val k L T K x"
proof -
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
  define c0 where "c0 = min T \<delta>f"
  have r00: "0 < norm x" using xnz by simp
  have rB0: "0 < rB" using r00 xin by linarith
  have cn0: "0 < real m - 1"
  proof -
    have "(2::real) \<le> real m"
      using m2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis by linarith
  qed
  have sq_lt: "(norm x)\<^sup>2 < rB\<^sup>2"
    using r00 xin by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have c00: "0 < c0" unfolding c0_def using T0 df0 by simp
  define ccs where "ccs = (\<lambda>j :: nat. c0 - c0 / (2 * real (Suc j)))"
  have ccl: "0 < ccs j" for j
  proof -
    have "c0 / (2 * real (Suc j)) \<le> c0 / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> c0" using c00 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding ccs_def using c00 by linarith
  qed
  have ccu: "ccs j < c0" for j
  proof -
    have "0 < c0 / (2 * real (Suc j))" using c00 by simp
    then show ?thesis unfolding ccs_def by linarith
  qed
  have lim: "ccs \<longlonglongrightarrow> c0"
  proof -
    have eq: "(\<lambda>j. (c0 / 2) * inverse (real (Suc j)))
        = (\<lambda>j. c0 / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (c0 / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (c0 / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. c0 / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. c0 - c0 / (2 * real (Suc j))) \<longlonglongrightarrow> c0 - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding ccs_def by simp
  qed
  have le: "ennreal (ccs j) \<le> exit_val k L T K x" for j
  proof (rule exit_val_ball_lower_subspace[OF T0 L1 Kc sub xnz xin orth
        mk m2 xfix])
    show "0 < ccs j" by (rule ccl)
    show "ccs j < T" using ccu[of j] unfolding c0_def by simp
    show "ccs j < (rB\<^sup>2 - (norm x)\<^sup>2) / (real m - 1)"
      using ccu[of j] unfolding c0_def \<delta>f_def[symmetric] by simp
  qed
  have "(\<lambda>j. ennreal (ccs j)) \<longlonglongrightarrow> ennreal c0"
    by (rule tendsto_ennrealI[OF lim])
  then have "ennreal c0 \<le> exit_val k L T K x"
    by (rule tendsto_upperbound) (use le in auto)
  then show ?thesis unfolding c0_def \<delta>f_def .
qed


(*<*)
end
(*>*)
