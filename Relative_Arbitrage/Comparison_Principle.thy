section \<open>The instantiation: Theorem 4.2(a) from the doubling data alone\<close>

(*<*)
theory Comparison_Principle
  imports Comparison_Localisation
begin

(*>*)


text \<open>\<open>penalty_gradient_nearby_upper\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

theorem comparison_supconv_doubling_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi> :: "(real^'n) \<times> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi>
        \<Longrightarrow> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
              - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> m"
    and gapm: "m < supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
              - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2"
    and subu: "\<And>x. dist x (fst \<xi>) \<le> \<rho> \<Longrightarrow>
        cball x (sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) + 1) \<subseteq> \<Omega>"
    and subw: "\<And>x. dist x (snd \<xi>) \<le> \<rho> \<Longrightarrow>
        cball x (sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) + 1) \<subseteq> \<Omega>"
    and glb: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    and rsmall: "2 * \<bar>\<alpha>\<bar> * \<rho> < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  define D where "D = (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
              - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2 - m) / (2*r)"
  have D0: "0 < D"
    unfolding D_def by (rule jensen_tilt_threshold_pos[OF gapm r0])
  have ddpos: "0 < D / (2 + real i)" for i
    by (rule tilt_sequence_pos[OF D0])
  have ddlt: "D / (2 + real i) < D" for i
    by (rule tilt_sequence_lt[OF D0])
  have dd0: "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
  have ddlt': "D / (2 + real i)
      < (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
          - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2 - m) / (2*r)" for i
    using ddlt[of i] by (simp only: D_def)
  have small: "2 * (D / (2 + real i)) * r
      < (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
          - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2) - m" for i
    by (rule jensen_tilt_small_enough[OF r0 ddlt'])
  define P where "P = (\<lambda>i zh p q W.
      dist zh \<xi> < \<rho> \<and> norm p \<le> D / (2 + real i)
      \<and> (\<forall>y \<in> cball \<xi> r.
          (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
          \<le> (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst zh) + supconv (- w) \<epsilon> (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>k. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) * (norm k)\<^sup>2) \<le> k \<bullet> W k)
      \<and> ((\<lambda>hk. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zh + hk))
              + supconv (- w) \<epsilon> (snd (zh + hk))
              - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
            - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst zh) + supconv (- w) \<epsilon> (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
            - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
  have H: "\<exists>zh p q W. P i zh p q W" for i
    unfolding P_def
    by (rule doubled_supconv_jet_exists
        [OF Bu Bw e a rho(1) rho(2) bnd ddpos small])
  obtain zf pf qf Wf where famP: "\<forall>i. P i (zf i) (pf i) (qf i) (Wf i)"
    using choice4[where P = P, OF H] by blast
  note fam = famP[unfolded P_def]
  have dz: "dist (zf i) \<xi> < \<rho>" for i using fam by blast  have dzle: "dist (zf i) \<xi> \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi> < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D / (2 + real i)" for i using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
      (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
      \<le> (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i)) + supconv (- w) \<epsilon> (snd (zf i))
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) * (norm hk)\<^sup>2) \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
            + supconv (- w) \<epsilon> (snd (zf i + hk))
            - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
          - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              + supconv (- w) \<epsilon> (snd (zf i))
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive
        [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdi: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))" for i
    by (rule tilted_doubled_psd_ordering
        [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW symW dzr mxf expf])
  have psdi0: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
          + (0::real) *\<^sub>R mat 1)" for i
    using psdi[of i] by simp
  have cszero: "(\<lambda>_::nat. 0::real) \<longlonglongrightarrow> 0"
    by simp
  have symX: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)" for i
    by (rule transpose_matrix_block_fst[OF blW symW])
  have symY: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))" for i
    by (rule transpose_matrix_block_snd[OF blW symW])
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) + \<bar>\<alpha>\<bar>)"
    for i
    by (rule norm_block_matrices_bounded(1)[OF blW symW loW hiW])
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) + \<bar>\<alpha>\<bar>)"
    for i
    by (rule norm_block_matrices_bounded(2)[OF blW symW loW hiW])
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using tilted_doubled_jet_slices(2)
      [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
         and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
         and q = "qf i" and W = "Wf i",
       OF blW dzr mxf expf]
    unfolding block_fst_matrix_apply[OF blW] .
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> ((- matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using tilted_doubled_jet_slices(3)
      [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
         and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
         and q = "qf i" and W = "Wf i",
       OF blW dzr mxf expf]
    unfolding block_snd_matrix_apply[OF blW] .
  have dfst: "dist (fst (zf i)) (fst \<xi>) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>] dzle[of i] by linarith
  obtain ysu where ysu: "\<forall>i. ysu i \<in> \<Omega>
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)" and \<Omega> = \<Omega>
         and Bu = Bu and \<epsilon> = \<epsilon>,
       OF Bu e cu subu[OF dfst]]
    by blast
  obtain ysw where ysw: "\<forall>i. ysw i \<in> \<Omega>
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)" and \<Omega> = \<Omega>
         and Bu = Bw and \<epsilon> = \<epsilon>,
       OF Bw e cw subw[OF dsnd]]
    by blast
  have bG: "norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) + 2 * \<bar>\<alpha>\<bar> * \<rho>" for i
    by (rule penalty_gradient_nearby_upper[OF dzle])
  have gG: "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound[OF glb dzle])
  have cG: "0 < c - 2 * \<bar>\<alpha>\<bar> * \<rho>" using rsmall by linarith
  have pt0: "pf \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF np dd0])
  have au: "(\<lambda>i. (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
    using tendsto_minus[OF tendsto_fst[OF pt0]] by (simp add: zero_prod_def)
  have aw: "(\<lambda>i. (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
    using tendsto_snd[OF pt0] by (simp add: zero_prod_def)
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega> and \<Omega>\<^sub>w = \<Omega>
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))"
           and G = "\<lambda>i. \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pw = "\<lambda>i. snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>_. 0"
           and c = "c - 2 * \<bar>\<alpha>\<bar> * \<rho>",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symX symY psdi0 cszero jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

subsection \<open>Assembly 1 complete: the contradiction from the maximiser alone\<close>

text \<open>The completion: from a plain maximiser of the doubled sup-convolution
  functional at \<open>\<xi>\<^sub>0\<close> - no strict gap - plus the gradient lower bound
  there and the attainment balls, this derives \<open>False\<close>.  The strict gap
  is manufactured by the \<open>-\<delta>\<^sub>i\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> perturbation with
  \<open>\<delta>\<^sub>i=D\<^sub>0/(2+i) \<rightarrow> 0\<close> (\<open>shifted_jensen_family\<close>).  The three \<open>O(\<delta>\<^sub>i)\<close>
  costs - gradient shift \<open>2\<delta>\<^sub>i(\<cdot>-\<xi>\<^sub>0)\<close>, Hessian shift \<open>\<plusminus>2\<delta>\<^sub>iI\<close> with
  ordering defect \<open>4\<delta>\<^sub>i\<close>, and Hessian norm shift \<open>2D\<^sub>0\<parallel>I\<parallel>\<close> - land
  exactly where the generalised interfaces expect them.\<close>

theorem comparison_supconv_maximiser_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
          - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2"
    and radu: "\<And>x. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) < R\<^sub>u"
    and radw: "\<And>x. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) < R\<^sub>w"
    and subu: "\<And>x. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow> cball x R\<^sub>u \<subseteq> \<Omega>"
    and subw: "\<And>x. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow> cball x R\<^sub>w \<subseteq> \<Omega>"
    and glb: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "2 * \<bar>\<alpha>\<bar> * \<rho> < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  obtain zf pf qf Wf where fam: "\<forall>i.
      dist (zf i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
          \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i))
      \<and> bounded_linear (Wf i) \<and> (\<forall>v z. v \<bullet> Wf i z = z \<bullet> Wf i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> Wf i hk)
      \<and> ((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
          - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using shifted_jensen_family[OF Bu Bw e a rho(1) rho(2) D0 mxK] by blast
  have dz: "dist (zf i) \<xi>\<^sub>0 < \<rho>" for i using fam by blast
  have dzle: "dist (zf i) \<xi>\<^sub>0 \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi>\<^sub>0 < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
      ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
          - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd y)
          - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
      \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
      \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
      - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
      - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i by (rule tilt_sequence_pos[OF D0])
  have dlt: "D\<^sub>0/(2 + real i) < D\<^sub>0" for i by (rule tilt_sequence_lt[OF D0])
  have dfst: "dist (fst (zf i)) (fst \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdU: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))" for i
    by (rule tilted_doubled_psd_ordering
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW symW dzr mxf expf])
  have psdS: "psd ((matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        - (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
            + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        + (2*(2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1)" for i
    using psdU[of i] unfolding shift_cancel_matrix .
  have cs0: "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 2*(2*(0::real))"
      by (intro tendsto_mult tendsto_const tilt_sequence_tendsto)
    then show ?thesis by simp
  qed
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
           + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
        - (h \<bullet> ((matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
                + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceA: "((\<lambda>h. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) + h - fst \<xi>\<^sub>0))\<^sup>2)
        - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices(2)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
    have transA: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "fst \<xi>\<^sub>0" and xh = "fst (zf i)"
             and p = "- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
             and X = "\<lambda>h. fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h",
           OF sliceA])
    show ?thesis
      using transA
      unfolding matrix_shift_apply block_fst_matrix_apply[OF blW] .
  qed
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))) \<bullet> h
        - (h \<bullet> ((- (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
                - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceB: "((\<lambda>h. ((supconv (- w) \<epsilon> (snd (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) + h - snd \<xi>\<^sub>0))\<^sup>2)
        - (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> (snd (Wf i (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices(3)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
    have transB: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
          - supconv (- w) \<epsilon> (snd (zf i))
          - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (snd (Wf i (0, h)) + \<alpha> *\<^sub>R h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (- w) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "snd \<xi>\<^sub>0" and xh = "snd (zf i)"
             and p = "- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))"
             and X = "\<lambda>h. snd (Wf i (0, h)) + \<alpha> *\<^sub>R h",
           OF sliceB])
    have negPw: "- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = - (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have negY: "- (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        = (- matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
          + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      using transB
      unfolding negPw negY matrix_shift_apply block_snd_matrix_apply[OF blW] .
  qed
  have symXs: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
    by (rule transpose_shifted_block
        [OF transpose_matrix_block_fst[OF blW symW]])
  have symYs: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      unfolding eqm
      by (rule transpose_shifted_block
          [OF transpose_matrix_block_snd[OF blW symW]])
  qed
  have bXun: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)" for i
    by (rule norm_block_matrices_bounded(1)[OF blW symW loW hiW])
  have bYun: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)" for i
    by (rule norm_block_matrices_bounded(2)[OF blW symW loW hiW])
  have Cuni: "real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)
      \<le> real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)" for i
  proof -
    have "(1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>
        \<le> (1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>"
      using dlt[of i] by linarith
    then show ?thesis by (rule mult_left_mono) simp
  qed
  have habs: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)
      \<le> 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have e1: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> = 2*(D\<^sub>0/(2 + real i))"
      using D0 by simp
    have e2: "2*(D\<^sub>0/(2 + real i)) \<le> 2*D\<^sub>0"
      using dlt[of i] by linarith
    show ?thesis
      unfolding e1 by (rule mult_right_mono[OF e2]) simp
  qed
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
    using norm_shifted_block
        [where M = "matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)"
           and c = "2*(D\<^sub>0/(2 + real i))"]
      bXun[of i] Cuni[of i] habs[of i]
    by linarith
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    have h2: "\<bar>- (2*(D\<^sub>0/(2 + real i)))\<bar> * norm (mat 1 :: real^'n^'n)
        = \<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)"
      by simp
    show ?thesis
      unfolding eqm
      using norm_shifted_block
          [where M = "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))"
             and c = "- (2*(D\<^sub>0/(2 + real i)))"]
        h2 bYun[of i] Cuni[of i] habs[of i]
      by linarith
  qed
  obtain ysu where ysu: "\<forall>i. ysu i \<in> \<Omega>
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in_rad
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)" and \<Omega> = \<Omega>
         and Bu = Bu and \<epsilon> = \<epsilon> and R = R\<^sub>u,
       OF Bu e cu radu[OF dfst] subu[OF dfst]]
    by blast
  obtain ysw where ysw: "\<forall>i. ysw i \<in> \<Omega>
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in_rad
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)" and \<Omega> = \<Omega>
         and Bu = Bw and \<epsilon> = \<epsilon> and R = R\<^sub>w,
       OF Bw e cw radw[OF dsnd] subw[OF dsnd]]
    by blast
  have nfst: "norm (fst (pf i)) \<le> norm (pf i)" for i
    using norm_fst_le[of "fst (pf i)" "snd (pf i)"] by simp
  have nsnd: "norm (snd (pf i)) \<le> norm (pf i)" for i
    using norm_snd_le[where x = "fst (pf i)" and y = "snd (pf i)"] by simp
  have nshiftA: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (fst (zf i)) (fst \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dfst p2])
    finally show ?thesis .
  qed
  have nshiftB: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (snd (zf i)) (snd \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dsnd p2])
    finally show ?thesis .
  qed
  have Elim: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)
      + 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
  proof -
    have l1: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)) \<longlonglongrightarrow> 0"
      by (rule shifted_family_parameters(5)[OF D0 rho(1) r0])
    have l2: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
    proof -
      have h: "(\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i))) \<longlonglongrightarrow> (2*\<rho>) * 0"
        by (rule tendsto_mult[OF tendsto_const tilt_sequence_tendsto])
      have eq: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>)
          = (\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i)))"
        by (rule ext) (simp add: mult_ac)
      show ?thesis unfolding eq using h by simp
    qed
    from tendsto_add[OF l1 l2] show ?thesis by simp
  qed
  have au: "(\<lambda>i. (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        = (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0) - fst (pf i)"
      by simp
    have tri: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)
          - fst (pf i))
        \<le> norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
          + norm (fst (pf i))"
      by (rule norm_triangle_ineq4)
    show "norm ((- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftA[of i] nfst[of i] np[of i] by linarith
  qed
  have aw: "(\<lambda>i. (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        = snd (pf i) - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have tri: "norm (snd (pf i)
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        \<le> norm (snd (pf i))
          + norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))"
      by (rule norm_triangle_ineq4)
    show "norm ((snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftB[of i] nsnd[of i] np[of i] by linarith
  qed
  have bG: "norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) + 2 * \<bar>\<alpha>\<bar> * \<rho>" for i
    by (rule penalty_gradient_nearby_upper[OF dzle])
  have gG: "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound[OF glb dzle])
  have cG: "0 < c - 2 * \<bar>\<alpha>\<bar> * \<rho>" using rsmall by linarith
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega> and \<Omega>\<^sub>w = \<Omega>
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
              + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
              - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and G = "\<lambda>i. \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)"
           and Pw = "\<lambda>i. snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))"
           and c = "c - 2 * \<bar>\<alpha>\<bar> * \<rho>",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symXs symYs psdS cs0 jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

text \<open>\<open>block_fst_matrix_apply_gen\<close>, \<open>block_snd_matrix_apply_gen\<close>, \<open>transpose_matrix_block_fst_gen\<close>, \<open>transpose_matrix_block_snd_gen\<close>, \<open>diff_displacement_bound\<close>, \<open>penalty_gradient_nearby_upper_gen\<close>, \<open>penalty_gradient_nearby_bound_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>\<open>comparison_supconv_maximiser_complete\<close> generalised: the quadratic
  penalty \<open>(\<alpha>/2)(norm d)\<^sup>2\<close> becomes an arbitrary \<open>Pn\<close> that is
  \<open>\<kappa>\<close>-semiconcave with gradient field \<open>Gf\<close> and Hessian field \<open>Zf\<close>,
  evaluated at the displacement \<open>d\<close> of the \<open>i\<close>-th maximiser.  Jensen's
  tilt is genuinely quadratic and not part of the penalty, so
  \<open>jet_transfer_quadratic\<close> still applies; the consumer
  \<open>comparison_supconv_bounded_family\<close> is penalty-agnostic and reused
  verbatim.\<close>

theorem comparison_supconv_maximiser_complete_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
    and Pn :: "real^'n \<Rightarrow> real"
    and Gf :: "real^'n \<Rightarrow> real^'n" and Zf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - Pn d)"
    and Pjet: "\<And>d. ((\<lambda>h. (Pn (d + h) - Pn d - Gf d \<bullet> h
          - (h \<bullet> (Zf d *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and symZ: "\<And>d. transpose (Zf d) = Zf d"
    and bZ: "\<And>d z. \<bar>z \<bullet> (Zf d *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
    and lipG: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KGnn: "0 \<le> KG"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
          - Pn (fst y - snd y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and atu: "\<And>x z. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)
        \<Longrightarrow> z \<in> \<Omega>\<^sub>u"
    and atw: "\<And>x z. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        supconv (- w) \<epsilon> x = (- w) z - (dist x z)\<^sup>2 / (2*\<epsilon>)
        \<Longrightarrow> z \<in> \<Omega>\<^sub>w"
    and glb: "c \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "KG * (2*\<rho>) < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  obtain zf pf qf Wf where fam: "\<forall>i.
      dist (zf i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst y - snd y)) + pf i \<bullet> y
          \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i) - snd (zf i))) + pf i \<bullet> (zf i))
      \<and> bounded_linear (Wf i) \<and> (\<forall>v z. v \<bullet> Wf i z = z \<bullet> Wf i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> Wf i hk)
      \<and> ((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i + hk) - snd (zf i + hk)))
          - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i) - snd (zf i)))
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using shifted_jensen_family_gen[OF Bu Bw e kap sc rho(1) rho(2) D0 mxK]
    by blast
  have dz: "dist (zf i) \<xi>\<^sub>0 < \<rho>" for i using fam by blast
  have dzle: "dist (zf i) \<xi>\<^sub>0 \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi>\<^sub>0 < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
      ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
          - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd y)
          - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)) + pf i \<bullet> y
      \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i) - snd (zf i))) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
      \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i + hk) - snd (zf i + hk)))
      - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i) - snd (zf i)))
      - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i by (rule tilt_sequence_pos[OF D0])
  have dlt: "D\<^sub>0/(2 + real i) < D\<^sub>0" for i by (rule tilt_sequence_lt[OF D0])
  have dfst: "dist (fst (zf i)) (fst \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive_gen
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdU: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
          - matrix (\<lambda>v. fst (Wf i (v, 0))
            + Zf (fst (zf i) - snd (zf i)) *v v))" for i
    by (rule tilted_doubled_psd_ordering_gen
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and Pn = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW symW symZ dzr mxf expf Pjet])
  have psdS: "psd ((matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        - (matrix (\<lambda>v. fst (Wf i (v, 0))
              + Zf (fst (zf i) - snd (zf i)) *v v)
            + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        + (2*(2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1)" for i
    using psdU[of i] unfolding shift_cancel_matrix .
  have cs0: "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 2*(2*(0::real))"
      by (intro tendsto_mult tendsto_const tilt_sequence_tendsto)
    then show ?thesis by simp
  qed
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
           + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
        - (h \<bullet> ((matrix (\<lambda>v. fst (Wf i (v, 0))
                    + Zf (fst (zf i) - snd (zf i)) *v v)
                + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceA: "((\<lambda>h. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) + h - fst \<xi>\<^sub>0))\<^sup>2)
        - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (fst (Wf i (h, 0))
              + Zf (fst (zf i) - snd (zf i)) *v h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices_gen(2)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW dzr mxf expf Pjet])
    have transA: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (fst (Wf i (h, 0)) + Zf (fst (zf i) - snd (zf i)) *v h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "fst \<xi>\<^sub>0" and xh = "fst (zf i)"
             and p = "- fst (pf i) + Gf (fst (zf i) - snd (zf i))"
             and X = "\<lambda>h. fst (Wf i (h, 0))
                + Zf (fst (zf i) - snd (zf i)) *v h",
           OF sliceA])
    show ?thesis
      using transA
      unfolding matrix_shift_apply block_fst_matrix_apply_gen[OF blW] .
  qed
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))) \<bullet> h
        - (h \<bullet> ((- (matrix (\<lambda>v. - (snd (Wf i (0, v))
                      + Zf (fst (zf i) - snd (zf i)) *v v))
                - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceB: "((\<lambda>h. ((supconv (- w) \<epsilon> (snd (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) + h - snd \<xi>\<^sub>0))\<^sup>2)
        - (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> (snd (Wf i (0, h))
              + Zf (fst (zf i) - snd (zf i)) *v h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices_gen(3)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW dzr mxf expf Pjet])
    have transB: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
          - supconv (- w) \<epsilon> (snd (zf i))
          - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (snd (Wf i (0, h)) + Zf (fst (zf i) - snd (zf i)) *v h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (- w) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "snd \<xi>\<^sub>0" and xh = "snd (zf i)"
             and p = "- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))"
             and X = "\<lambda>h. snd (Wf i (0, h))
                + Zf (fst (zf i) - snd (zf i)) *v h",
           OF sliceB])
    have negPw: "- (snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = - (snd (pf i) + Gf (fst (zf i) - snd (zf i)))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have negY: "- (matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        = (- matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v)))
          + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      using transB
      unfolding negPw negY matrix_shift_apply
        block_snd_matrix_apply_gen[OF blW] .
  qed
  have symXs: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0))
          + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
    by (rule transpose_shifted_block
        [OF transpose_matrix_block_fst_gen[OF blW symW symZ]])
  have symYs: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      unfolding eqm
      by (rule transpose_shifted_block
          [OF transpose_matrix_block_snd_gen[OF blW symW symZ]])
  qed
  have bXun: "norm (matrix (\<lambda>v. fst (Wf i (v, 0))
        + Zf (fst (zf i) - snd (zf i)) *v v))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)" for i
    by (rule norm_block_matrices_bounded_gen(1)[OF blW symW symZ loW hiW bZ])
  have bYun: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v))
        + Zf (fst (zf i) - snd (zf i)) *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)" for i
    by (rule norm_block_matrices_bounded_gen(2)[OF blW symW symZ loW hiW bZ])
  have Cuni: "real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)
      \<le> real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)" for i
  proof -
    have "(1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ
        \<le> (1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ"
      using dlt[of i] by linarith
    then show ?thesis by (rule mult_left_mono) simp
  qed
  have habs: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)
      \<le> 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have e1: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> = 2*(D\<^sub>0/(2 + real i))"
      using D0 by simp
    have e2: "2*(D\<^sub>0/(2 + real i)) \<le> 2*D\<^sub>0"
      using dlt[of i] by linarith
    show ?thesis
      unfolding e1 by (rule mult_right_mono[OF e2]) simp
  qed
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0))
          + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
    using norm_shifted_block
        [where M = "matrix (\<lambda>v. fst (Wf i (v, 0))
            + Zf (fst (zf i) - snd (zf i)) *v v)"
           and c = "2*(D\<^sub>0/(2 + real i))"]
      bXun[of i] Cuni[of i] habs[of i]
    by linarith
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v))
          + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    have h2: "\<bar>- (2*(D\<^sub>0/(2 + real i)))\<bar> * norm (mat 1 :: real^'n^'n)
        = \<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)"
      by simp
    show ?thesis
      unfolding eqm
      using norm_shifted_block
          [where M = "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))"
             and c = "- (2*(D\<^sub>0/(2 + real i)))"]
        h2 bYun[of i] Cuni[of i] habs[of i]
      by linarith
  qed
  obtain ysu0 where ysu0: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu0 i) - (dist (fst (zf i)) (ysu0 i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_family
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)"
         and Bu = Bu and \<epsilon> = \<epsilon>, OF Bu e uu]
    by blast
  define ysu where "ysu = ysu0"
  have ysu: "\<forall>i. ysu i \<in> \<Omega>\<^sub>u
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    unfolding ysu_def using ysu0 atu[OF dfst] by blast
  obtain ysw0 where ysw0: "\<And>i. supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw0 i) - (dist (snd (zf i)) (ysw0 i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_family
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)"
         and Bu = Bw and \<epsilon> = \<epsilon>, OF Bw e uw]
    by blast
  define ysw where "ysw = ysw0"
  have ysw: "\<forall>i. ysw i \<in> \<Omega>\<^sub>w
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    unfolding ysw_def using ysw0 atw[OF dsnd] by blast
  have nfst: "norm (fst (pf i)) \<le> norm (pf i)" for i
    using norm_fst_le[of "fst (pf i)" "snd (pf i)"] by simp
  have nsnd: "norm (snd (pf i)) \<le> norm (pf i)" for i
    using norm_snd_le[where x = "fst (pf i)" and y = "snd (pf i)"] by simp
  have nshiftA: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (fst (zf i)) (fst \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dfst p2])
    finally show ?thesis .
  qed
  have nshiftB: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (snd (zf i)) (snd \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dsnd p2])
    finally show ?thesis .
  qed
  have Elim: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)
      + 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
  proof -
    have l1: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)) \<longlonglongrightarrow> 0"
      by (rule shifted_family_parameters(5)[OF D0 rho(1) r0])
    have l2: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
    proof -
      have h: "(\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i))) \<longlonglongrightarrow> (2*\<rho>) * 0"
        by (rule tendsto_mult[OF tendsto_const tilt_sequence_tendsto])
      have eq: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>)
          = (\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i)))"
        by (rule ext) (simp add: mult_ac)
      show ?thesis unfolding eq using h by simp
    qed
    from tendsto_add[OF l1 l2] show ?thesis by simp
  qed
  have au: "(\<lambda>i. (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
        + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      - Gf (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(- fst (pf i) + Gf (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i))
        = (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0) - fst (pf i)"
      by simp
    have tri: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)
          - fst (pf i))
        \<le> norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
          + norm (fst (pf i))"
      by (rule norm_triangle_ineq4)
    show "norm ((- fst (pf i) + Gf (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftA[of i] nfst[of i] np[of i] by linarith
  qed
  have aw: "(\<lambda>i. (snd (pf i) + Gf (fst (zf i) - snd (zf i))
        - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      - Gf (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i))
        = snd (pf i) - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have tri: "norm (snd (pf i)
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        \<le> norm (snd (pf i))
          + norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))"
      by (rule norm_triangle_ineq4)
    show "norm ((snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftB[of i] nsnd[of i] np[of i] by linarith
  qed
  have bG: "norm (Gf (fst (zf i) - snd (zf i)))
      \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) + KG * (2*\<rho>)" for i
    by (rule penalty_gradient_nearby_upper_gen[OF dzle lipG KGnn])
  have gG: "c - KG * (2*\<rho>) \<le> norm (Gf (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound_gen[OF glb dzle lipG KGnn])
  have cG: "0 < c - KG * (2*\<rho>)" using rsmall by linarith
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega>\<^sub>u and \<Omega>\<^sub>w = \<Omega>\<^sub>w
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0))
                + Zf (fst (zf i) - snd (zf i)) *v v)
              + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v))
                + Zf (fst (zf i) - snd (zf i)) *v v))
              - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and G = "\<lambda>i. Gf (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + Gf (fst (zf i) - snd (zf i))
              + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)"
           and Pw = "\<lambda>i. snd (pf i) + Gf (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))"
           and c = "c - KG * (2*\<rho>)",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symXs symYs psdS cs0 jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

section \<open>The \<open>max_principle_boundary\<close> interface needs continuity: the raw version is refutable\<close>

text \<open>\<open>max_principle_boundary k L K\<close> (@{theory Relative_Arbitrage.Operator_Envelope_Continuity}) as originally
  stated, quantifying over all \<open>u\<close>, \<open>w\<close> satisfying \<open>visc_subsol\<close>/
  \<open>supersol_jet\<close> on \<open>interior K\<close> with no semicontinuity or boundedness,
  is false: those local conditions say nothing about the boundary values
  of \<open>u\<close> and \<open>w\<close>, which can be moved to destroy any boundary maximum of
  \<open>u - w\<close> (\<open>visc_supersol_cong_on\<close>, \<open>max_principle_boundary_counterexample\<close>).
  The paper's Theorem 4.2(a) needs \<open>u\<close> upper semicontinuous and \<open>w\<close>
  lower semicontinuous on \<open>K\<close>, which is also what makes \<open>u-w\<close> attain a
  maximum on compact \<open>K\<close> at all.\<close>

lemma visc_subsol_cong_on:
  fixes u u' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_subsol k L \<Omega> u" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> u' y = u y"
  shows "visc_subsol k L \<Omega> u'"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. u' y - \<phi> y \<le> u' x - \<phi> x"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> u' y - \<phi> y \<le> u' x - \<phi> x" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "u y - \<phi> y = u' y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    also have "\<dots> \<le> u' x - \<phi> x" by (rule le[OF ye])
    also have "\<dots> = u x - \<phi> x" using eq[OF x] by simp
    finally show "u y - \<phi> y \<le> u x - \<phi> x" .
  qed
  from s x tf loc' show "ell_op k L (g x) H \<le> 1"
    unfolding visc_subsol_def by blast
qed

lemma visc_supersol_cong_on:
  fixes w w' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_supersol k L \<Omega> w" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> w' y = w y"
  shows "visc_supersol k L \<Omega> w'"
  unfolding visc_supersol_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. w' x - \<phi> x \<le> w' y - \<phi> y"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> w' x - \<phi> x \<le> w' y - \<phi> y" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "w x - \<phi> x = w' x - \<phi> x" using eq[OF x] by simp
    also have "\<dots> \<le> w' y - \<phi> y" by (rule le[OF ye])
    also have "\<dots> = w y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    finally show "w x - \<phi> x \<le> w y - \<phi> y" .
  qed
  from s x tf loc' show "1 \<le> ell_op k L (g x) H"
    unfolding visc_supersol_def by blast
qed

lemma supersol_jet_cong_on:
  fixes w w' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "supersol_jet k L \<Omega> w" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> w' y = w y"
  shows "supersol_jet k L \<Omega> w'"
  unfolding supersol_jet_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. w' x - \<phi> x \<le> w' y - \<phi> y"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> w' x - \<phi> x \<le> w' y - \<phi> y" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "w x - \<phi> x = w' x - \<phi> x" using eq[OF x] by simp
    also have "\<dots> \<le> w' y - \<phi> y" by (rule le[OF ye])
    also have "\<dots> = w y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    finally show "w x - \<phi> x \<le> w y - \<phi> y" .
  qed
  from s x tf loc' show "1 \<le> ell_op_usc k L (g x) H"
    unfolding supersol_jet_def by blast
qed

text \<open>The refutation: given any sub/supersolution pair and nonempty interior,
  the supersolution's boundary values can be raised uniformly enough to
  make every boundary point lose to a fixed interior point, independent
  of the operator, dimension or geometry of \<open>K\<close>.\<close>

theorem max_principle_boundary_counterexample:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "visc_supersol k L (interior K) w"
    and ne: "interior K \<noteq> {}"
  shows "\<not> max_principle_boundary_raw k L K"
proof
  assume mp: "max_principle_boundary_raw k L K"
  from ne obtain y0 where y0: "y0 \<in> interior K" by blast
  define w' where "w' = (\<lambda>y. if y \<in> interior K then w y
      else u y - (u y0 - w y0) + 1)"
  have sup': "visc_supersol k L (interior K) w'"
    by (rule visc_supersol_cong_on[OF sup open_interior]) (simp add: w'_def)
  obtain x where x: "x \<in> K - interior K"
    and mx: "\<And>y. y \<in> K \<Longrightarrow> u y - w' y \<le> u x - w' x"
    using mp sub sup' unfolding max_principle_boundary_raw_def by blast
  have xb: "x \<notin> interior K" using x by simp
  have vx: "u x - w' x = (u y0 - w y0) - 1"
    unfolding w'_def using xb by simp
  have vy: "u y0 - w' y0 = u y0 - w y0"
    unfolding w'_def using y0 by simp
  have "y0 \<in> K" using y0 interior_subset by blast
  from mx[OF this] vx vy show False by simp
qed

text \<open>The repair lives in @{theory Relative_Arbitrage.Operator_Envelope_Continuity}: the corrected
  \<open>max_principle_boundary\<close> carries \<open>continuous_on K u\<close> and
  \<open>continuous_on K w\<close>, \<open>sup_diff_attained_on_compact\<close> (from
  @{theory Semicontinuous_Analysis.Semicontinuity}) records that
  \<open>u-w\<close> then attains its maximum on compact \<open>K\<close>, and \<open>max_principle_le\<close>,
  \<open>comparison_from_max_principle\<close>, \<open>uniqueness_from_max_principle\<close>
  thread the two continuity hypotheses through.  Everything downstream -
  4.2(b), Theorem 4.3, Proposition 4.1 - is unchanged except for carrying
  this continuity.\<close>

section \<open>Reduction to globally bounded, globally continuous data\<close>

text \<open>\<open>continuous_extension_bounded\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

lemma visc_subsol_extend:
  fixes u v :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_subsol k L (interior K) u"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> v y = u y"
  shows "visc_subsol k L (interior K) v"
proof (rule visc_subsol_cong_on[OF s open_interior])
  fix y assume "y \<in> interior K"
  then have "y \<in> K" using interior_subset by blast
  then show "v y = u y" by (rule eq)
qed

lemma supersol_jet_extend:
  fixes w v :: "real^'n::finite \<Rightarrow> real"
  assumes s: "supersol_jet k L (interior K) w"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> v y = w y"
  shows "supersol_jet k L (interior K) v"
proof (rule supersol_jet_cong_on[OF s open_interior])
  fix y assume "y \<in> interior K"
  then have "y \<in> K" using interior_subset by blast
  then show "v y = w y" by (rule eq)
qed

text \<open>\<open>bounded_on_compact\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Distance to the boundary controls the balls\<close>

text \<open>\<open>cball_subset_interior_of_far_from_boundary\<close>, \<open>cball_prod_subset_of_far_from_boundary\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>From a localised maximiser straight to the contradiction\<close>

text \<open>The bridge between the localisation and the assembly: given the
  doubling maximiser \<open>\<xi>\<^sub>0\<close> over \<open>K \<times> K\<close> with both components further
  than \<open>\<kappa>\<close> from \<open>K - interior K\<close>, every geometric hypothesis of
  \<open>comparison_supconv_maximiser_complete\<close> is derivable via
  \<open>cball_subset_interior_of_far_from_boundary\<close> and
  \<open>supconv_radius_uniform\<close>.  The remaining quantitative inputs are the
  inequalities \<open>r \<le> \<kappa>\<close>, \<open>\<rho>+R\<^sub>u \<le> \<kappa>\<close>, \<open>\<rho>+R\<^sub>w \<le> \<kappa>\<close>, \<open>2\<bar>\<alpha>\<bar>\<rho> < c\<close> and two
  smallness conditions on \<open>\<epsilon>\<close>.\<close>

text \<open>Under a general penalty every geometric derivation is untouched, since
  the penalty only carries along unchanged from \<open>mxKK\<close> to \<open>mxK\<close>; only
  the gradient conditions \<open>glb\<close> and \<open>rsmall\<close> refer to it, through \<open>Gf\<close>
  and its Lipschitz constant \<open>KG\<close>.\<close>

theorem comparison_from_localised_maximiser_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and K :: "(real^'n) set"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
    and Pn :: "real^'n \<Rightarrow> real"
    and Gf :: "real^'n \<Rightarrow> real^'n" and Zf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>\<^sub>P"
    and scP: "convex_on UNIV (\<lambda>d. (\<kappa>\<^sub>P/2) * (norm d)\<^sup>2 - Pn d)"
    and Pjet: "\<And>d. ((\<lambda>h. (Pn (d + h) - Pn d - Gf d \<bullet> h
          - (h \<bullet> (Zf d *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and symZ: "\<And>d. transpose (Zf d) = Zf d"
    and bZ: "\<And>d z. \<bar>z \<bullet> (Zf d *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
    and lipG: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KGnn: "0 \<le> KG"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - Pn (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and xK: "fst \<xi>\<^sub>0 \<in> K" and yK: "snd \<xi>\<^sub>0 \<in> K"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (fst \<xi>\<^sub>0) b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (snd \<xi>\<^sub>0) b"
    and rho: "0 < \<rho>" "\<rho> < r" and rk: "r \<le> \<kappa>"
    and Rup: "0 < R\<^sub>u" and Rwp: "0 < R\<^sub>w"
    and smallu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    and fitu: "\<rho> + R\<^sub>u \<le> \<kappa>" and fitw: "\<rho> + R\<^sub>w \<le> \<kappa>"
    and D0: "0 < D\<^sub>0"
    and glb: "c \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "KG * (2*\<rho>) < c"
  shows False
proof -
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have k0: "0 \<le> \<kappa>" using rho rk by linarith
  have coll: "(fst \<xi>\<^sub>0, snd \<xi>\<^sub>0) = \<xi>\<^sub>0" by simp
  have insx: "cball (fst \<xi>\<^sub>0) \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK xK k0 farx])
  have insy: "cball (snd \<xi>\<^sub>0) \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK yK k0 fary])
  have mxK: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst z) + supconv (- w) \<epsilon> (snd z)
        - Pn (fst z - snd z)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
        - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    if z: "z \<in> cball \<xi>\<^sub>0 r" for z
  proof -
    have dz: "dist z (fst \<xi>\<^sub>0, snd \<xi>\<^sub>0) \<le> \<kappa>"
      unfolding coll using z rk by (simp add: dist_commute)
    have "fst z \<in> K \<and> snd z \<in> K"
      by (rule cball_prod_subset_of_far_from_boundary
          [OF clK xK yK k0 farx fary dz])
    then show ?thesis using mxKK by blast
  qed
  have radu: "sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) < R\<^sub>u" for x
    by (rule supconv_radius_uniform[OF lou e Rup smallu])
  have radw: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) < R\<^sub>w" for x
    by (rule supconv_radius_uniform[OF low e Rwp smallw])
  have subu: "cball x R\<^sub>u \<subseteq> interior K" if d: "dist x (fst \<xi>\<^sub>0) \<le> \<rho>" for x
  proof -
    have "cball x R\<^sub>u \<subseteq> cball (fst \<xi>\<^sub>0) \<kappa>"
    proof
      fix y assume "y \<in> cball x R\<^sub>u"
      then have dy: "dist x y \<le> R\<^sub>u" by simp
      have "dist (fst \<xi>\<^sub>0) y \<le> dist (fst \<xi>\<^sub>0) x + dist x y"
        by (rule dist_triangle)
      also have "\<dots> \<le> \<rho> + R\<^sub>u"
        using d dy by (simp add: dist_commute)
      finally show "y \<in> cball (fst \<xi>\<^sub>0) \<kappa>" using fitu by simp
    qed
    then show ?thesis using insx by blast
  qed
  have subw: "cball x R\<^sub>w \<subseteq> interior K" if d: "dist x (snd \<xi>\<^sub>0) \<le> \<rho>" for x
  proof -
    have "cball x R\<^sub>w \<subseteq> cball (snd \<xi>\<^sub>0) \<kappa>"
    proof
      fix y assume "y \<in> cball x R\<^sub>w"
      then have dy: "dist x y \<le> R\<^sub>w" by simp
      have "dist (snd \<xi>\<^sub>0) y \<le> dist (snd \<xi>\<^sub>0) x + dist x y"
        by (rule dist_triangle)
      also have "\<dots> \<le> \<rho> + R\<^sub>w"
        using d dy by (simp add: dist_commute)
      finally show "y \<in> cball (snd \<xi>\<^sub>0) \<kappa>" using fitw by simp
    qed
    then show ?thesis using insy by blast
  qed
  have icu: "isCont (\<lambda>y. \<theta> * u y) z" for z
    using cu[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
  have icw: "isCont (- w) z" for z
    using cw[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
  have uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
      \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    by (rule usc_eps_of_continuous[OF icu])
  have uw: "\<And>c z. (- w) z < c \<Longrightarrow>
      \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    by (rule usc_eps_of_continuous[OF icw])
  have atu: "z \<in> interior K"
    if d: "dist x (fst \<xi>\<^sub>0) \<le> \<rho>"
      and o: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
          = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)" for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x)))"
      by (rule supconv_attain_radius[OF Bu e o])
    also have "\<dots> < R\<^sub>u" by (rule radu)
    finally have "z \<in> cball x R\<^sub>u" by (simp add: dist_commute)
    then show ?thesis using subu[OF d] by blast
  qed
  have atw: "z \<in> interior K"
    if d: "dist x (snd \<xi>\<^sub>0) \<le> \<rho>"
      and o: "supconv (- w) \<epsilon> x = (- w) z - (dist x z)\<^sup>2 / (2*\<epsilon>)" for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x)))"
      by (rule supconv_attain_radius[OF Bw e o])
    also have "\<dots> < R\<^sub>w" by (rule radw)
    finally have "z \<in> cball x R\<^sub>w" by (simp add: dist_commute)
    then show ?thesis using subw[OF d] by blast
  qed
  show False
    by (rule comparison_supconv_maximiser_complete_gen
        [where u = u and w = w and \<xi>\<^sub>0 = \<xi>\<^sub>0 and D\<^sub>0 = D\<^sub>0
           and \<Omega>\<^sub>u = "interior K" and \<Omega>\<^sub>w = "interior K"
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa> = \<kappa>\<^sub>P and \<rho> = \<rho> and r = r
           and Pn = Pn and Gf = Gf and Zf = Zf and KZ = KZ and KG = KG
           and Bu = Bu and Bw = Bw and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL e kap scP Pjet symZ bZ lipG
            KGnn rho(1) rho(2) D0 Bu Bw uu uw])
       (use mxK atu atw glb rsmall in blast)+
qed

subsection \<open>The chain at the concrete penalty \<open>soft_pen\<close>\<close>

text \<open>Every abstract hypothesis of the \<open>_gen\<close> chain is discharged at
  \<open>Pn = soft_pen \<kappa>\<close>:

    \<open>sc\<close>    by \<open>soft_pen_semiconcave\<close>
    \<open>Pjet\<close>  by \<open>soft_pen_jet_field\<close>   (gradient field \<open>soft_grad \<kappa>\<close>,
                                      Hessian field \<open>soft_hess \<kappa>\<close>)
    \<open>symZ\<close>  by \<open>soft_hess_sym\<close>
    \<open>bZ\<close>    by \<open>soft_hess_bound\<close>       with \<open>KZ = 2\<kappa>\<close>
    \<open>lipG\<close>  by \<open>soft_grad_lipschitz\<close>   with \<open>KG = 3\<kappa>\<close>

  so the theorem below mentions no penalty data beyond \<open>\<kappa>\<close> itself;
  \<open>KZ\<close> and \<open>KG\<close> are free parameters, not sharp constants.\<close>

theorem comparison_from_localised_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and K :: "(real^'n) set"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>\<^sub>P"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - soft_pen \<kappa>\<^sub>P (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and xK: "fst \<xi>\<^sub>0 \<in> K" and yK: "snd \<xi>\<^sub>0 \<in> K"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (fst \<xi>\<^sub>0) b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (snd \<xi>\<^sub>0) b"
    and rho: "0 < \<rho>" "\<rho> < r" and rk: "r \<le> \<kappa>"
    and Rup: "0 < R\<^sub>u" and Rwp: "0 < R\<^sub>w"
    and smallu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    and fitu: "\<rho> + R\<^sub>u \<le> \<kappa>" and fitw: "\<rho> + R\<^sub>w \<le> \<kappa>"
    and D0: "0 < D\<^sub>0"
    and glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
  shows False
proof -
  have KGnn: "0 \<le> 3*\<kappa>\<^sub>P" using kap by linarith
  show False
    by (rule comparison_from_localised_maximiser_gen
        [where u = u and w = w and K = K and \<xi>\<^sub>0 = \<xi>\<^sub>0 and D\<^sub>0 = D\<^sub>0
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and \<rho> = \<rho> and r = r and \<kappa> = \<kappa>
           and Pn = "soft_pen \<kappa>\<^sub>P" and Gf = "soft_grad \<kappa>\<^sub>P"
           and Zf = "soft_hess \<kappa>\<^sub>P" and KZ = "2*\<kappa>\<^sub>P" and KG = "3*\<kappa>\<^sub>P"
           and Bu = Bu and Bw = Bw and Blu = Blu and Blw = Blw
           and R\<^sub>u = R\<^sub>u and R\<^sub>w = R\<^sub>w and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL e kap
            soft_pen_semiconcave[OF kap] soft_pen_jet_field soft_hess_sym
            soft_hess_bound[OF kap] soft_grad_lipschitz[OF kap] KGnn cK
            Bu Bw lou low cu cw])
       (use mxKK xK yK farx fary rho rk Rup Rwp smallu smallw fitu fitw
            D0 glb rsmall in blast)+
qed

subsection \<open>Branch (A): the off-diagonal case closes\<close>

text \<open>Given the localised maximiser off the diagonal, the remaining
  parameters of \<open>comparison_from_localised_maximiser_soft\<close> are
  determined:

    \<open>R\<^sub>u = R\<^sub>w = \<kappa>\<^sub>g/4\<close>, \<open>r = \<kappa>\<^sub>g\<close>, \<open>\<rho> < 3\<kappa>\<^sub>g/4\<close> small enough that
    \<open>6\<rho> < (1 - 1/R d) norm d\<close> (\<open>soft_rho_exists\<close>),
    \<open>c = norm (soft_grad \<kappa>\<^sub>P d)\<close> (positive by \<open>soft_grad_norm_pos\<close>),
    \<open>D\<^sub>0 = 1\<close>

  \<open>rsmall\<close> is \<open>soft_rsmall_of_rho\<close>, and \<open>glb\<close> holds by reflexivity
  since \<open>c\<close> is the gradient norm; \<open>\<kappa>\<^sub>P\<close> cancels in \<open>rsmall\<close>.\<close>

theorem comparison_soft_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa>\<^sub>g < dist xh b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa>\<^sub>g < dist yh b"
    and smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and off: "xh \<noteq> yh"
  shows False
proof -
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have dne: "xh - yh \<noteq> 0" using off by simp
  \<comment> \<open>the positive gradient lower bound\<close>
  define c where "c = norm (soft_grad \<kappa>\<^sub>P (xh - yh))"
  have cpos: "0 < c" unfolding c_def by (rule soft_grad_norm_pos[OF dne kPpos])
  \<comment> \<open>the radii\<close>
  define R\<^sub>u where "R\<^sub>u = \<kappa>\<^sub>g/4"
  have Rupos: "0 < R\<^sub>u" unfolding R\<^sub>u_def using kgpos by simp
  have Bpos: "0 < 3*\<kappa>\<^sub>g/4" using kgpos by simp
  obtain \<rho> where rpos: "0 < \<rho>" and rlt: "\<rho> < 3*\<kappa>\<^sub>g/4"
    and rgrad: "6 * \<rho> < (1 - 1 / sqrt ((norm (xh - yh))\<^sup>2 + 1)) * norm (xh - yh)"
    using soft_rho_exists[OF dne Bpos] by blast
  have rltk: "\<rho> < \<kappa>\<^sub>g" using rlt kgpos by simp
  have fitu: "\<rho> + R\<^sub>u \<le> \<kappa>\<^sub>g" unfolding R\<^sub>u_def using rlt by simp
  have rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
    unfolding c_def by (rule soft_rsmall_of_rho[OF kPpos rgrad])
  have glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh)))"
    unfolding c_def by simp
  \<comment> \<open>the maximiser hypothesis in the paired form\<close>
  have mxp: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
        - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    if "x \<in> K" "y \<in> K" for x y
    using mxKK[OF that] by simp
  have xKp: "fst (xh, yh) \<in> K" using xhK by simp
  have yKp: "snd (xh, yh) \<in> K" using yhK by simp
  have farxp: "\<kappa>\<^sub>g < dist (fst (xh, yh)) b" if "b \<in> K - interior K" for b
    using farx[OF that] by simp
  have faryp: "\<kappa>\<^sub>g < dist (snd (xh, yh)) b" if "b \<in> K - interior K" for b
    using fary[OF that] by simp
  have smu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2" unfolding R\<^sub>u_def by (rule smallu)
  have smw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>u\<^sup>2" unfolding R\<^sub>u_def by (rule smallw)
  have D0: "(0::real) < 1" by simp
  show False
    by (rule comparison_from_localised_maximiser_soft
        [where u = u and w = w and K = K and \<xi>\<^sub>0 = "(xh, yh)" and D\<^sub>0 = 1
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and \<kappa> = \<kappa>\<^sub>g and \<rho> = \<rho> and r = \<kappa>\<^sub>g
           and Bu = Bu and Bw = Bw and Blu = Blu and Blw = Blw
           and R\<^sub>u = R\<^sub>u and R\<^sub>w = R\<^sub>u and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL epos kPnn cK Bu Bw lou low cu cw])
       (use mxp xKp yKp farxp faryp rpos rltk order.refl Rupos
            smu smw fitu D0 glb rsmall in blast)+
qed

subsection \<open>Branch (A) in the two-domain setting\<close>

text \<open>The same branch with the \<open>x\<close>-side boundary avoidance replaced by
  \<open>posb\<close> - the sup-convolution is positive on a \<open>\<rho>\<^sub>u\<close>-ball around
  \<open>x^h\<close>, supplied by Definition 3.1's gate with no geometry needed.  The
  \<open>y\<close>-side keeps its ball, paid for by \<open>K \<subseteq> K'\<^sup>\<circ>\<close>; the maximality
  hypothesis \<open>mxU\<close> ranges over \<open>UNIV \<times> K'\<close>, from
  \<open>doubled_maximiser_over_UNIV_snd\<close>.\<close>

theorem comparison_2dom_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K' :: "(real^'n) set"
  assumes sub: "visc_subsol k L {q. 0 < u q} u"
    and sup: "supersol_jet k L (interior K') w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and low: "\<And>y. Blw \<le> (- w) y"
    and uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and clK': "closed K'" and yhK': "yh \<in> K'"
    and mxU: "\<And>a q. q \<in> K' \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> a + supconv (- w) \<epsilon> q - soft_pen \<kappa>\<^sub>P (a - q)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and fary: "\<And>b. b \<in> K' - interior K' \<Longrightarrow> \<kappa>\<^sub>g < dist yh b"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and rupos: "0 < \<rho>\<^sub>u"
    and posb: "\<And>a. dist a xh \<le> \<rho>\<^sub>u \<Longrightarrow> 0 < supconv (\<lambda>y. \<theta> * u y) \<epsilon> a"
    and off: "xh \<noteq> yh"
  shows False
proof -
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have kgnn: "0 \<le> \<kappa>\<^sub>g" using kgpos by linarith
  have dne: "xh - yh \<noteq> 0" using off by simp
  define c where "c = norm (soft_grad \<kappa>\<^sub>P (xh - yh))"
  have cpos: "0 < c" unfolding c_def by (rule soft_grad_norm_pos[OF dne kPpos])
  define R\<^sub>w where "R\<^sub>w = \<kappa>\<^sub>g/4"
  have Rwpos: "0 < R\<^sub>w" unfolding R\<^sub>w_def using kgpos by simp
  have smallw': "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    unfolding R\<^sub>w_def by (rule smallw)
  have Bpos: "0 < min (3*\<kappa>\<^sub>g/4) \<rho>\<^sub>u" using kgpos rupos by simp
  obtain \<rho> where rpos: "0 < \<rho>" and rlt: "\<rho> < min (3*\<kappa>\<^sub>g/4) \<rho>\<^sub>u"
    and rgrad: "6 * \<rho>
        < (1 - 1 / sqrt ((norm (xh - yh))\<^sup>2 + 1)) * norm (xh - yh)"
    using soft_rho_exists[OF dne Bpos] by blast
  have rlt1: "\<rho> < 3*\<kappa>\<^sub>g/4" using rlt by simp
  have rltu: "\<rho> \<le> \<rho>\<^sub>u" using rlt by simp
  have rltk: "\<rho> < \<kappa>\<^sub>g" using rlt1 kgpos by simp
  have fitw: "\<rho> + R\<^sub>w \<le> \<kappa>\<^sub>g" unfolding R\<^sub>w_def using rlt1 by simp
  have rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
    unfolding c_def by (rule soft_rsmall_of_rho[OF kPpos rgrad])
  have glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh)))"
    unfolding c_def by simp
  have insy: "cball yh \<kappa>\<^sub>g \<subseteq> interior K'"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK' yhK' kgnn fary])
  have ballK': "cball (snd (xh, yh)) \<kappa>\<^sub>g \<subseteq> K'"
    using insy interior_subset by auto
  have mx': "\<And>a q. q \<in> K' \<Longrightarrow>
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> a + supconv (- w) \<epsilon> q - soft_pen \<kappa>\<^sub>P (a - q)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    using mxU by simp
  have mxK: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst p) + supconv (- w) \<epsilon> (snd p)
        - soft_pen \<kappa>\<^sub>P (fst p - snd p)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    if p: "p \<in> cball (xh, yh) \<kappa>\<^sub>g" for p
    by (rule mxK_of_UNIV_snd
        [where A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and Bfun = "supconv (- w) \<epsilon>"
           and Pn = "soft_pen \<kappa>\<^sub>P" and K' = K' and \<xi>\<^sub>0 = "(xh, yh)"
           and r = \<kappa>\<^sub>g and p = p,
         OF mx' ballK' p])
  have atw: "z \<in> interior K'"
    if d: "dist a (snd (xh, yh)) \<le> \<rho>"
      and o: "supconv (- w) \<epsilon> a = (- w) z - (dist a z)\<^sup>2 / (2*\<epsilon>)" for a z
  proof -
    have d1: "dist a z \<le> sqrt (max 0 (2*\<epsilon>*(Bw - (- w) a)))"
      by (rule supconv_attain_radius[OF Bw epos o])
    have d2: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) a))) < R\<^sub>w"
      by (rule supconv_radius_uniform[OF low epos Rwpos smallw'])
    have dz: "dist a z \<le> R\<^sub>w" using d1 d2 by linarith
    have "dist yh z \<le> dist yh a + dist a z" by (rule dist_triangle)
    also have "\<dots> \<le> \<rho> + R\<^sub>w" using d dz by (simp add: dist_commute)
    finally have "z \<in> cball yh \<kappa>\<^sub>g" using fitw by simp
    then show ?thesis using insy by blast
  qed
  have atu: "z \<in> {q. 0 < u q}"
    if d: "dist a (fst (xh, yh)) \<le> \<rho>"
      and o: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> a = \<theta> * u z - (dist a z)\<^sup>2 / (2*\<epsilon>)"
    for a z
  proof -
    have du: "dist a xh \<le> \<rho>\<^sub>u" using d rltu by simp
    show ?thesis by (rule atu_of_positive_ball[OF t(1) epos posb du o])
  qed
  have D0: "(0::real) < 1" by simp
  have KGnn: "0 \<le> 3*\<kappa>\<^sub>P" using kPnn by linarith
  show False
    by (rule comparison_supconv_maximiser_complete_gen
        [where u = u and w = w and \<xi>\<^sub>0 = "(xh, yh)" and D\<^sub>0 = 1
           and \<Omega>\<^sub>u = "{q. 0 < u q}" and \<Omega>\<^sub>w = "interior K'"
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa> = \<kappa>\<^sub>P and \<rho> = \<rho> and r = \<kappa>\<^sub>g
           and Pn = "soft_pen \<kappa>\<^sub>P" and Gf = "soft_grad \<kappa>\<^sub>P"
           and Zf = "soft_hess \<kappa>\<^sub>P" and KZ = "2*\<kappa>\<^sub>P" and KG = "3*\<kappa>\<^sub>P"
           and Bu = Bu and Bw = Bw and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL epos kPnn
            soft_pen_semiconcave[OF kPnn] soft_pen_jet_field soft_hess_sym
            soft_hess_bound[OF kPnn] soft_grad_lipschitz[OF kPnn] KGnn
            rpos rltk D0 Bu Bw uu uw])
       (use mxK atu atw glb rsmall in blast)+
qed

subsection \<open>Branch (B): the diagonal case closes too\<close>

text \<open>The four steps chained: at a diagonal maximiser (interior, by the
  localisation), the maximiser inequality bounds the increment of
  \<open>B = supconv(-w)\<epsilon>\<close> above by the penalty, which is \<open>o(\<bar>h\<bar>^2)\<close>; that
  descends to \<open>-w\<close> at the attainment point, and a supersolution cannot
  have such a flat point.  This uses no property of the subsolution
  side, so the diagonal case is a genuinely different argument from the
  off-diagonal one.\<close>

theorem comparison_soft_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n \<Rightarrow> real"
  assumes sup: "supersol_jet k L (interior K) w"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bw: "\<And>y. (- w) y \<le> Bw"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and epos: "0 < \<epsilon>"
    and pK: "p \<in> K" and pint: "p \<in> interior K"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> A p + supconv (- w) \<epsilon> p - soft_pen \<kappa>\<^sub>P (p - p)"
    and rad: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) p))) < R\<^sub>w"
    and subw: "cball p R\<^sub>w \<subseteq> interior K"
  shows False
proof -
  \<comment> \<open>the attainment point, and it is interior\<close>
  obtain ys where ysO: "ys \<in> interior K"
    and opt: "supconv (- w) \<epsilon> p = (- w) ys - (dist p ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_in_rad[OF Bw epos uw rad subw] by blast
  \<comment> \<open>\<open>p\<close> is interior, so \<open>p + hh\<close> stays in \<open>K\<close> for small \<open>hh\<close>\<close>
  \<comment> \<open>\<open>mem_interior\<close> already delivers the ball inside \<open>K\<close> itself, so no
      subset-transitivity step is needed --- routing it through
      \<open>interior_subset\<close> instead made \<open>blast\<close> search for seconds and PIDE flag it\<close>
  obtain r\<^sub>0 where r0: "0 < r\<^sub>0" and rb: "ball p r\<^sub>0 \<subseteq> K"
    using pint unfolding mem_interior by blast
  have nb: "p + hh \<in> K" if "hh \<noteq> 0" and "dist hh 0 < r\<^sub>0" for hh
  proof -
    have "dist (p + hh) p < r\<^sub>0" using that by (simp add: dist_norm)
    then have "p + hh \<in> ball p r\<^sub>0" by (simp add: dist_commute)
    then show ?thesis using rb by blast
  qed
  have nbhd: "\<forall>\<^sub>F hh in at 0. p + hh \<in> K"
    unfolding eventually_at using r0 nb by blast
  \<comment> \<open>step 1: the increment bound\<close>
  have dom: "\<forall>\<^sub>F hh in at 0.
      supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p \<le> soft_pen \<kappa>\<^sub>P hh"
  proof (rule eventually_mono[OF nbhd])
    fix hh :: "real^'n"
    assume hK: "p + hh \<in> K"
    show "supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p \<le> soft_pen \<kappa>\<^sub>P hh"
      by (rule diagonal_max_increment_soft[OF mxKK pK hK])
  qed
  \<comment> \<open>step 2: it is the one-sided hypothesis\<close>
  have ub: "\<forall>\<^sub>F hh in at 0.
      (supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p) / (norm hh)\<^sup>2 < c"
    if c: "0 < c" for c
    by (rule diagonal_increment_onesided[OF dom c])
  \<comment> \<open>step 3: descend to the attainment point\<close>
  have ubw: "\<forall>\<^sub>F hh in at 0. ((- w) (ys + hh) - (- w) ys) / (norm hh)\<^sup>2 < c"
    if c: "0 < c" for c
    by (rule supconv_onesided_descent[OF Bw epos opt ub c])
  \<comment> \<open>step 4: a supersolution has no such flat point\<close>
  show False
    by (rule supersol_no_vanishing_jet_onesided
        [OF sup ysO kk(1) kk(2) LL ubw])
qed

subsection \<open>A nonempty compact set has a nonempty frontier\<close>

text \<open>\<open>compact_frontier_nonempty\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The two branches combined\<close>

text \<open>\<open>doubling_localised_maximiser_soft\<close> produces the maximiser; branch
  (A) closes it off the diagonal, branch (B) on it.  Branch (B)'s
  geometric hypotheses follow from the localisation:

    \<open>xh \<in> interior K\<close> - \<open>farx\<close> gives \<open>\<kappa>\<^sub>g < dist xh b\<close> for every
      boundary \<open>b\<close>, ruling out \<open>xh\<close> itself being one.
    \<open>cball xh R\<^sub>w \<subseteq> interior K\<close> - from
      \<open>cball_subset_interior_of_far_from_boundary\<close> at radius \<open>\<kappa>\<^sub>g\<close>.
    the attainment radius bound - from \<open>supconv_radius_uniform\<close>.\<close>

theorem comparison_soft_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and zK: "z \<in> K"
    and Mval: "M \<le> \<theta> * u z - w z"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> \<theta> * u c - w c \<le> m"
    and gapMm: "m < M"
  shows False
proof -
  obtain \<epsilon> \<kappa>\<^sub>g \<kappa>\<^sub>P xh yh where
        epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxb: "\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and farx: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b"
    and fary: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b"
    and smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using doubling_localised_maximiser_soft
      [OF cK neK Bu Bw lou low cu cw zK Mval bdry gapMm] by blast
  have mx: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
        - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa>\<^sub>P (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mxb that by blast
  have farxa: "\<kappa>\<^sub>g < dist xh b" if "b \<in> K - interior K" for b
    using farx that by blast
  have farya: "\<kappa>\<^sub>g < dist yh b" if "b \<in> K - interior K" for b
    using fary that by blast
  show False
  proof (cases "xh = yh")
    case False
    show False
      by (rule comparison_soft_off_diagonal
          [OF sub sup t(1) t(2) kk(1) kk(2) LL cK Bu Bw lou low cu cw
              epos kgpos kPpos xhK yhK mx farxa farya smallu smallw False])
  next
    case True
    \<comment> \<open>\<open>xh\<close> is interior: a boundary point would give \<open>\<kappa>\<^sub>g < dist xh xh = 0\<close>\<close>
    have pint: "xh \<in> interior K"
    proof (rule ccontr)
      assume "xh \<notin> interior K"
      with xhK have "xh \<in> K - interior K" by simp
      from farxa[OF this] show False using kgpos by simp
    qed
    have clK: "closed K" by (rule compact_imp_closed[OF cK])
    have kgnn: "0 \<le> \<kappa>\<^sub>g" using kgpos by linarith
    have insx: "cball xh \<kappa>\<^sub>g \<subseteq> interior K"
      by (rule cball_subset_interior_of_far_from_boundary
          [OF clK xhK kgnn farxa])
    have Rwpos: "0 < \<kappa>\<^sub>g/4" using kgpos by simp
    have shrink: "cball xh (\<kappa>\<^sub>g/4) \<subseteq> cball xh \<kappa>\<^sub>g"
    proof
      fix y assume "y \<in> cball xh (\<kappa>\<^sub>g/4)"
      then have d1: "dist xh y \<le> \<kappa>\<^sub>g/4" by simp
      have d2: "\<kappa>\<^sub>g/4 \<le> \<kappa>\<^sub>g" using kgpos by simp
      show "y \<in> cball xh \<kappa>\<^sub>g" using d1 d2 by simp
    qed
    have subw: "cball xh (\<kappa>\<^sub>g/4) \<subseteq> interior K" using shrink insx by blast
    have rad: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) xh))) < \<kappa>\<^sub>g/4"
      by (rule supconv_radius_uniform[OF low epos Rwpos smallw])
    have icwd: "isCont (- w) z" for z
      using cw[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
    have uwd: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
      by (rule usc_eps_of_continuous[OF icwd])
    have mxd: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
          - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> xh
          - soft_pen \<kappa>\<^sub>P (xh - xh)" if "x \<in> K" "y \<in> K" for x y
      using mx[OF that] unfolding True[symmetric] .
    show False
      by (rule comparison_soft_diagonal
          [where w = w and K = K and A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>"
             and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and p = xh and R\<^sub>w = "\<kappa>\<^sub>g/4" and Bw = Bw,
           OF sup kk(1) kk(2) LL Bw uwd epos xhK pint mxd rad subw])
  qed
qed

section \<open>Theorem 4.2(a): \<open>max_principle_boundary\<close>\<close>

text \<open>\<open>theta_exists_aux\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


theorem max_principle_boundary_holds:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
  shows "max_principle_boundary k L K"
proof -
  have dim: "0 < CARD('n)" using kk by simp
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  show ?thesis
    unfolding max_principle_boundary_def
  proof (intro allI impI)
    fix u w :: "real^'n \<Rightarrow> real"
    assume subE: "visc_subsol_env k L K (interior K) u"
      and supE: "visc_supersol_env k L K (interior K) w"
      and cu: "continuous_on K u" and cw: "continuous_on K w"
    \<comment> \<open>Definition 3.1(b) yields the jet form once and for all\<close>
    have Kb: "bounded K" by (rule compact_imp_bounded[OF cK])
    obtain Bw where Bw: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    proof -
      have "bounded (w ` K)"
        by (rule compact_imp_bounded[OF compact_continuous_image[OF cw cK]])
      then obtain a where a: "\<forall>z \<in> w ` K. norm z \<le> a"
        unfolding bounded_iff by blast
      have "- a \<le> w y" if y: "y \<in> K" for y
      proof -
        have "norm (w y) \<le> a" using a y by blast
        then have "\<bar>w y\<bar> \<le> a" by simp
        then have "- (w y) \<le> a" by (simp add: abs_le_iff)
        then show ?thesis by linarith
      qed
      then show thesis by (rule that)
    qed
    have sup: "supersol_jet k L (interior K) w"
      by (rule visc_supersol_env_imp_jet
            [OF visc_supersol_env_imp_env2[OF supE] Kb Bw])
    obtain Bu where Bu: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    proof -
      have "bounded (u ` K)"
        by (rule compact_imp_bounded[OF compact_continuous_image[OF cu cK]])
      then obtain a where a: "\<forall>z \<in> u ` K. norm z \<le> a"
        unfolding bounded_iff by blast
      have "u y \<le> a" if y: "y \<in> K" for y
      proof -
        have "norm (u y) \<le> a" using a y by blast
        then have "\<bar>u y\<bar> \<le> a" by simp
        then show ?thesis by (simp add: abs_le_iff)
      qed
      then show thesis by (rule that)
    qed
    have sub: "visc_subsol k L (interior K) u"
      by (rule visc_subsol_env_imp_visc_subsol
            [OF visc_subsol_env_imp_env2[OF subE] Kb Bu kk(1) kk(2) LL])
    show "\<exists>x \<in> K - interior K. \<forall>y \<in> K. u y - w y \<le> u x - w x"
    proof (rule ccontr)
      assume nb: "\<not> (\<exists>x \<in> K - interior K. \<forall>y \<in> K. u y - w y \<le> u x - w x)"
      \<comment> \<open>the global maximiser\<close>
      obtain xs where xsK: "xs \<in> K"
        and xsmax: "\<And>y. y \<in> K \<Longrightarrow> u y - w y \<le> u xs - w xs"
        using sup_diff_attained_on_compact[OF cK neK cu cw] by blast
      \<comment> \<open>the boundary is compact and nonempty\<close>
      have clS: "closed (K - interior K)"
        by (intro closed_Diff clK open_interior)
      have bS: "bounded (K - interior K)"
        by (rule bounded_subset[OF compact_imp_bounded[OF cK]]) blast
      have cpS: "compact (K - interior K)"
        using bS clS by (simp add: compact_eq_bounded_closed)
      have neS: "K - interior K \<noteq> {}"
        by (rule compact_frontier_nonempty[OF cK neK dim])
      have cS: "continuous_on (K - interior K) (\<lambda>y. u y - w y)"
        by (intro continuous_intros
            continuous_on_subset[OF cu Diff_subset]
            continuous_on_subset[OF cw Diff_subset])
      obtain xb where xbS: "xb \<in> K - interior K"
        and xbmax: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y - w y \<le> u xb - w xb"
        using continuous_attains_sup[OF cpS neS cS] by blast
      \<comment> \<open>the boundary maximum is STRICTLY below the global one\<close>
      have gap: "u xb - w xb < u xs - w xs"
      proof -
        from nb obtain y where yK: "y \<in> K"
          and ygt: "\<not> (u y - w y \<le> u xb - w xb)"
          using xbS by blast
        have "u xb - w xb < u y - w y" using ygt by linarith
        also have "u y - w y \<le> u xs - w xs" by (rule xsmax[OF yK])
        finally show ?thesis .
      qed
      \<comment> \<open>globally bounded, globally continuous replacements\<close>
      obtain Bu where Bu0: "0 \<le> Bu" and BuK: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bu"
        using bounded_on_compact[OF cK cu] by blast
      obtain Bw where Bw0: "0 \<le> Bw" and BwK: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> Bw"
        using bounded_on_compact[OF cK cw] by blast
      define B where "B = max Bu Bw"
      have B0: "0 \<le> B" unfolding B_def using Bu0 by simp
      have BuB: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
        unfolding B_def using BuK by (simp add: le_max_iff_disj)
      have BwB: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
        unfolding B_def using BwK by (simp add: le_max_iff_disj)
      obtain u' where cu': "continuous_on UNIV u'"
        and equ: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y" and bu': "\<And>y. \<bar>u' y\<bar> \<le> B"
        using continuous_extension_bounded[OF clK cu B0 BuB] by blast
      obtain w' where cw': "continuous_on UNIV w'"
        and eqw: "\<And>y. y \<in> K \<Longrightarrow> w' y = w y" and bw': "\<And>y. \<bar>w' y\<bar> \<le> B"
        using continuous_extension_bounded[OF clK cw B0 BwB] by blast
      have sub': "visc_subsol k L (interior K) u'"
        by (rule visc_subsol_extend[OF sub equ])
      have sup': "supersol_jet k L (interior K) w'"
        by (rule supersol_jet_extend[OF sup eqw])
      \<comment> \<open>the \<open>\<theta>\<close>-scaling preserves the gap\<close>
      have Gpos: "0 < (u xs - w xs) - (u xb - w xb)" using gap by linarith
      obtain \<theta> where tpos: "0 < \<theta>" and tlt1: "\<theta> < 1"
        and tgap: "(1-\<theta>)*(2*B) < (u xs - w xs) - (u xb - w xb)"
        using theta_exists_aux[OF B0 Gpos] by blast
      have absu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" by (rule BuB)
      have strict: "\<theta> * u y - w y < \<theta> * u xs - w xs"
        if y: "y \<in> K - interior K" for y
        by (rule theta_gap_preserved
            [where u = u and w = w and K = K and B = B and \<theta> = \<theta>
               and M = "u xs - w xs" and m = "u xb - w xb"
               and xs = xs and S = "K - interior K" and y = y,
             OF absu less_imp_le[OF tlt1] tgap xsK order.refl
                Diff_subset xbmax y])
      \<comment> \<open>a uniform boundary bound for the scaled pair\<close>
      have cS2: "continuous_on (K - interior K) (\<lambda>y. \<theta> * u y - w y)"
        by (intro continuous_intros
            continuous_on_subset[OF cu Diff_subset]
            continuous_on_subset[OF cw Diff_subset])
      obtain xc where xcS: "xc \<in> K - interior K"
        and xcmax: "\<And>y. y \<in> K - interior K \<Longrightarrow>
            \<theta> * u y - w y \<le> \<theta> * u xc - w xc"
        using continuous_attains_sup[OF cpS neS cS2] by blast
      define mm where "mm = \<theta> * u xc - w xc"
      define MM where "MM = \<theta> * u xs - w xs"
      have mlt: "mm < MM" unfolding mm_def MM_def by (rule strict[OF xcS])
      \<comment> \<open>transfer everything to the extended data and close\<close>
      have bdry': "\<theta> * u' c - w' c \<le> mm" if c: "c \<in> K - interior K" for c
      proof -
        have cK': "c \<in> K" using c by simp
        have "\<theta> * u' c - w' c = \<theta> * u c - w c"
          unfolding equ[OF cK'] eqw[OF cK'] ..
        also have "\<dots> \<le> mm" unfolding mm_def by (rule xcmax[OF c])
        finally show ?thesis .
      qed
      have Mval': "MM \<le> \<theta> * u' xs - w' xs"
        unfolding MM_def equ[OF xsK] eqw[OF xsK] by simp
      have upu: "\<theta> * u' y \<le> \<theta> * B" for y
        by (rule mult_left_mono) (use bu'[of y] tpos in linarith)+
      have lou: "- (\<theta> * B) \<le> \<theta> * u' y" for y
      proof -
        have "\<theta> * (- B) \<le> \<theta> * u' y"
          by (rule mult_left_mono) (use bu'[of y] tpos in linarith)+
        then show ?thesis by simp
      qed
      have upw: "(- w') y \<le> B" for y using bw'[of y] by simp
      have low: "- B \<le> (- w') y" for y using bw'[of y] by simp
      have cuu: "continuous_on UNIV (\<lambda>y. \<theta> * u' y)"
        by (intro continuous_intros cu')
      \<comment> \<open>\<open>continuous_intros\<close> does not see through the FUNCTION-level negation
          \<open>- w'\<close>; unfold it to a lambda first\<close>
      have cww: "continuous_on UNIV (- w')"
      proof -
        have e: "(- w') = (\<lambda>y. - w' y)" by (rule ext) simp
        show ?thesis unfolding e by (intro continuous_intros cw')
      qed
      show False
        by (rule comparison_soft_complete
            [where u = u' and w = w' and K = K and \<theta> = \<theta>
               and Bu = "\<theta> * B" and Bw = B and Blu = "- (\<theta> * B)" and Blw = "- B"
               and z = xs and M = MM and m = mm,
             OF sub' sup' tpos tlt1 kk(1) kk(2) LL cK neK upu upw lou low
                cuu cww xsK Mval' bdry' mlt])
    qed
  qed
qed

section \<open>Uniqueness on a general compact set\<close>

text \<open>The first consequence of Theorem 4.2(a): two continuous viscosity
  solutions on compact \<open>K\<close> agreeing on \<open>K - interior K\<close> agree everywhere
  on \<open>K\<close>.  Both directions swap the roles of sub- and supersolution,
  putting the maximum of \<open>u - w\<close> on the boundary where it vanishes.
  This generalises the third clause of \<open>theorem_1_1_ball_fragment\<close>,
  previously available only for \<open>K = cball 0 r\<close> via the explicit
  Example 3.1 formula \<open>ball_v\<close>.\<close>

text \<open>The comparison principle proper, with ordered boundary data: a
  subsolution below a supersolution on the boundary stays below it
  throughout \<open>K\<close>.\<close>

theorem viscosity_uniqueness_compact:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and subu: "visc_subsol_env k L K (interior K) u"
    and supu: "visc_supersol_env k L K (interior K) u"
    and subw: "visc_subsol_env k L K (interior K) w"
    and supw: "visc_supersol_env k L K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  have mpb: "max_principle_boundary k L K"
    by (rule max_principle_boundary_holds[OF cK neK kk(1) kk(2) LL])
  \<comment> \<open>\<open>u - w\<close> peaks on the boundary, where it vanishes\<close>
  have le: "u x \<le> w x"
  proof -
    obtain b where bB: "b \<in> K - interior K"
      and bmax: "\<And>y. y \<in> K \<Longrightarrow> u y - w y \<le> u b - w b"
      using mpb subu supw cu cw unfolding max_principle_boundary_def by blast
    have "u b - w b = 0" using bd[OF bB] by simp
    then have "u x - w x \<le> 0" using bmax[OF x] by linarith
    then show ?thesis by linarith
  qed
  \<comment> \<open>and the same with the roles swapped\<close>
  have ge: "w x \<le> u x"
  proof -
    obtain b where bB: "b \<in> K - interior K"
      and bmax: "\<And>y. y \<in> K \<Longrightarrow> w y - u y \<le> w b - u b"
      using mpb subw supu cw cu unfolding max_principle_boundary_def by blast
    have "w b - u b = 0" using bd[OF bB] by simp
    then have "w x - u x \<le> 0" using bmax[OF x] by linarith
    then show ?thesis by linarith
  qed
  from le ge show ?thesis by simp
qed

section \<open>Map of the Theorem 4.2(a) chain\<close>

text \<open>This theory is long enough that the order of the argument is not
  visible from the section headings; the chain in dependency order:

  1. The operator and its envelopes: \<open>ell_op_lsc_elliptic_le\<close>,
  \<open>ell_op_env_strict_contradiction\<close> give degenerate ellipticity for both
  envelopes and the closing contradiction off the origin;
  \<open>eq36_rhs_antitone\<close> handles \<open>p = 0\<close>.

  2. The doubling: \<open>doubling_maximiser_exists\<close>, \<open>doubling_dist_bound\<close>,
  \<open>doubling_grad_lower_bound\<close> give the maximising pair, the \<open>O(1/\<alpha>)\<close>
  penalty estimate, and a positive lower bound on the shared gradient.

  3. Doubled jet to component jets to operator bounds:
  \<open>doubled_supconv_jet_exists\<close>, \<open>doubled_jet_slices_at_max\<close>,
  \<open>jet_imp_local_max_test\<close>, \<open>visc_subsol_scaled_uniform\<close>.

  4. Removing corrections, and compactness:
  \<open>ell_op_lsc_le_of_nearby\<close> passes a bound at nearby points to the
  envelope, subsuming both the \<open>\<delta> I\<close> shift and Jensen's tilt;
  \<open>symmetric_form_bound\<close> and \<open>bounded_seq_limit_point\<close> turn
  quadratic-form bounds into a limiting matrix pair without the spectral
  theorem.

  5. Assembly from bounds rather than limits:
  \<open>comparison_supconv_bounded_family\<close>, \<open>tilted_doubled_psd_ordering\<close>.

  6. The instantiation: \<open>comparison_supconv_doubling_complete\<close> runs
  Jensen at shrinking tilts and discharges the geometric data, closing
  \<open>max_principle_boundary\<close>, which requires continuity of \<open>u\<close> and \<open>w\<close> on
  \<open>K\<close>.\<close>


(*<*)
end
(*>*)
