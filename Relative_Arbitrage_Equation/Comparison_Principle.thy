section \<open>The instantiation: Theorem 4.2(a) from the doubling data alone\<close>

(*<*)
theory Comparison_Principle
  imports Comparison_Localisation
begin

(*>*)

subsection \<open>Assembly 1 complete: the contradiction from the maximiser alone\<close>

text \<open>The completion: from a plain maximiser of the doubled sup-convolution
  functional at \<open>\<xi>\<^sub>0\<close> - no strict gap - plus the gradient lower bound
  there and the attainment balls, this derives \<open>False\<close>.  The strict gap
  is manufactured by the \<open>-\<delta>\<^sub>i\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> perturbation with
  \<open>\<delta>\<^sub>i=D\<^sub>0/(2+i) \<rightarrow> 0\<close> (\<open>shifted_jensen_family_gen\<close>).  The three \<open>O(\<delta>\<^sub>i)\<close>
  costs - gradient shift \<open>2\<delta>\<^sub>i(\<cdot>-\<xi>\<^sub>0)\<close>, Hessian shift \<open>\<plusminus>2\<delta>\<^sub>iI\<close> with
  ordering defect \<open>4\<delta>\<^sub>i\<close>, and Hessian norm shift \<open>2D\<^sub>0\<parallel>I\<parallel>\<close> - land
  exactly where the generalised interfaces expect them.\<close>

text \<open>\<open>block_fst_matrix_apply_gen\<close>, \<open>block_snd_matrix_apply_gen\<close>, \<open>transpose_matrix_block_fst_gen\<close>, \<open>transpose_matrix_block_snd_gen\<close>, \<open>diff_displacement_bound\<close>, \<open>penalty_gradient_nearby_upper_gen\<close>, \<open>penalty_gradient_nearby_bound_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The penalty is not the quadratic \<open>(\<alpha>/2)(norm d)\<^sup>2\<close> but an arbitrary
  \<open>Pn\<close> that is \<open>\<kappa>\<close>-semiconcave with gradient field \<open>Gf\<close> and Hessian
  field \<open>Zf\<close>, evaluated at the displacement \<open>d\<close> of the \<open>i\<close>-th
  maximiser.  Jensen's tilt is genuinely quadratic and not part of the
  penalty, so \<open>jet_transfer_quadratic\<close> applies; the consumer
  \<open>comparison_supconv_bounded_family\<close> is penalty-agnostic.\<close>

context geometric_operator
begin

theorem comparison_supconv_maximiser_complete_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
    and Pn :: "real^'n \<Rightarrow> real"
    and Gf :: "real^'n \<Rightarrow> real^'n" and Zf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes sub: "subsol \<Omega>\<^sub>u u" and sup: "supersol_usc \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
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
    by (rule transpose_shift_add
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
      by (rule transpose_shift_add
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
         OF sub sup t(1) t(2) e Bu Bw])
       (use ysu ysw symXs symYs psdS cs0 jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

end

section \<open>Supersolutions are a local notion\<close>

lemma supersol_jet_cong_on:
  fixes w w' :: "real^'n::finite \<Rightarrow> real" and G :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal"
  assumes s: "visc_supersol_gen test_fun_at nhds G \<Omega> w" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> w' y = w y"
  shows "visc_supersol_gen test_fun_at nhds G \<Omega> w'"
proof (rule visc_supersol_gen_cong[OF s])
  show "w x = w' x" if "x \<in> \<Omega>" for x using eq[OF that] by simp
  show "eventually (\<lambda>y. w y = w' y) (nhds x)" if "x \<in> \<Omega>" for x
    using eventually_nhds_in_open[OF op that] by eventually_elim (simp add: eq)
qed

section \<open>The two branches of the contradiction\<close>

subsection \<open>Branch (A): the off-diagonal case, in the two-domain setting\<close>

text \<open>Off the diagonal, the \<open>x\<close>-side needs no boundary avoidance, only
  \<open>posb\<close> - the sup-convolution is positive on a \<open>\<rho>\<^sub>u\<close>-ball around
  \<open>x^h\<close>, supplied by Definition 3.1's gate with no geometry needed.  The
  \<open>y\<close>-side keeps its ball, paid for by \<open>K \<subseteq> K'\<^sup>\<circ>\<close>; the maximality
  hypothesis \<open>mxU\<close> ranges over \<open>UNIV \<times> K'\<close>, from
  \<open>doubled_maximiser_over_UNIV_snd\<close>.\<close>

context geometric_operator
begin

theorem comparison_2dom_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K' :: "(real^'n) set"
  assumes sub: "subsol {q. 0 < u q} u"
    and sup: "supersol_usc (interior K') w"
    and t: "0 < \<theta>" "\<theta> < 1"
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
         OF sub sup t(1) t(2) epos kPnn
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
  assumes sup: "supersol_usc (interior K) w"
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
        [OF sup ysO ubw])
qed

subsection \<open>A nonempty compact set has a nonempty frontier\<close>

text \<open>\<open>compact_frontier_nonempty\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

section \<open>Theorem 4.2(a)\<close>

text \<open>Theorem 4.2(a) of \<^cite>\<open>LaiShkolnikovSoner\<close>: on a compact \<open>K\<close>, if \<open>u\<close> is
  upper semicontinuous on \<open>K\<close> and a viscosity subsolution in the interior,
  and \<open>w\<close> is lower semicontinuous on \<open>K\<close> and a viscosity supersolution in
  the interior, then \<open>u - w\<close> attains its maximum over \<open>K\<close> on the
  boundary.  Semicontinuity is relative to \<open>K\<close>, in the \<open>\<epsilon>\<close>-form.  The
  bounds \<open>\<bar>u\<bar>, \<bar>w\<bar> \<le> B\<close> on \<open>K\<close> are explicit here; the paper's proof uses
  \<open>\<parallel>u\<parallel>\<^sub>\<infinity>\<close> and \<open>\<parallel>w\<parallel>\<^sub>\<infinity>\<close> without saying so.

  The proof argues by contradiction with a fixed \<open>\<theta> \<in> (0,1)\<close> that makes
  \<open>\<theta>u - w\<close> strictly smaller on the boundary than at an interior maximiser,
  and closes both branches with the sup-convolution and Jensen machinery of
  the sections above.  In place of the paper's subsequential limit of the
  maximisers, a Lebesgue number covers the boundary by open sets on which
  \<open>\<theta>u(z\<^sub>1) - w(z\<^sub>2)\<close> stays below the interior maximum; this needs only
  semicontinuity.\<close>

subsection \<open>The off-diagonal branch without continuity\<close>

text \<open>The off-diagonal branch on \<open>K\<close> itself: the \<open>\<epsilon>\<close>-form upper
  semicontinuity of \<open>\<theta>u\<close> and \<open>-w\<close> is assumed directly, and the assembly
  \<open>comparison_supconv_maximiser_complete_gen\<close> is called with
  \<open>\<Omega>\<^sub>u = \<Omega>\<^sub>w = interior K\<close>.\<close>

theorem comparison_soft_off_diagonal_usc:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "subsol (interior K) u"
    and sup: "supersol_usc (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and epos: "0 < \<epsilon>" and kgpos: "0 < kg" and kPpos: "0 < kP"
    and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen kP (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen kP (xh - yh)"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> kg < dist xh b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> kg < dist yh b"
    and smallu: "2*\<epsilon>*(Bu - Blu) < (kg/4)\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (kg/4)\<^sup>2"
    and off: "xh \<noteq> yh"
  shows False
proof -
  have kPnn: "0 \<le> kP" using kPpos by linarith
  have kgnn: "0 \<le> kg" using kgpos by linarith
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have dne: "xh - yh \<noteq> 0" using off by simp
  define c where "c = norm (soft_grad kP (xh - yh))"
  define R where "R = kg/4"
  have Rpos: "0 < R" unfolding R_def using kgpos by simp
  have smu: "2*\<epsilon>*(Bu - Blu) < R\<^sup>2" unfolding R_def by (rule smallu)
  have smw: "2*\<epsilon>*(Bw - Blw) < R\<^sup>2" unfolding R_def by (rule smallw)
  have Bpos: "0 < 3*kg/4" using kgpos by simp
  obtain \<rho> where rpos: "0 < \<rho>" and rlt: "\<rho> < 3*kg/4"
    and rgrad: "6 * \<rho> < (1 - 1 / sqrt ((norm (xh - yh))\<^sup>2 + 1)) * norm (xh - yh)"
    using soft_rho_exists[OF dne Bpos] by blast
  have rltk: "\<rho> < kg" using rlt kgpos by linarith
  have fit: "\<rho> + R \<le> kg" unfolding R_def using rlt by linarith
  have rsmall: "(3*kP) * (2*\<rho>) < c"
    unfolding c_def by (rule soft_rsmall_of_rho[OF kPpos rgrad])
  have glb: "c \<le> norm (soft_grad kP (fst (xh, yh) - snd (xh, yh)))"
    unfolding c_def by simp
  have insx: "cball xh kg \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK xhK kgnn farx])
  have insy: "cball yh kg \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK yhK kgnn fary])
  have mxK: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst p) + supconv (- w) \<epsilon> (snd p)
        - soft_pen kP (fst p - snd p)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh)) + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen kP (fst (xh, yh) - snd (xh, yh))"
    if p: "p \<in> cball (xh, yh) kg" for p
  proof -
    have dz: "dist p (xh, yh) \<le> kg" using p by (simp add: dist_commute)
    have "fst p \<in> K \<and> snd p \<in> K"
      by (rule cball_prod_subset_of_far_from_boundary[OF clK xhK yhK kgnn farx fary dz])
    then show ?thesis using mxKK[of "fst p" "snd p"] by simp
  qed
  have near: "z \<in> interior K"
    if c1: "dist x x0 \<le> \<rho>" and c2: "dist x z \<le> R" and x0: "cball x0 kg \<subseteq> interior K"
    for x x0 z
  proof -
    have "dist x0 z \<le> dist x0 x + dist x z" by (rule dist_triangle)
    moreover have "dist x0 x = dist x x0" by (rule dist_commute)
    ultimately have "dist x0 z \<le> kg" using c1 c2 fit by linarith
    then have "z \<in> cball x0 kg" by simp
    then show ?thesis using x0 by blast
  qed
  have atu: "z \<in> interior K"
    if d: "dist x (fst (xh, yh)) \<le> \<rho>"
      and o: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)"
    for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x)))"
      by (rule supconv_attain_radius[OF Bu epos o])
    also have "\<dots> < R" by (rule supconv_radius_uniform[OF lou epos Rpos smu])
    finally have dR: "dist x z \<le> R" by linarith
    have dx: "dist x xh \<le> \<rho>" using d by simp
    show ?thesis by (rule near[OF dx dR insx])
  qed
  have atw: "z \<in> interior K"
    if d: "dist x (snd (xh, yh)) \<le> \<rho>"
      and o: "supconv (- w) \<epsilon> x = (- w) z - (dist x z)\<^sup>2 / (2*\<epsilon>)"
    for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x)))"
      by (rule supconv_attain_radius[OF Bw epos o])
    also have "\<dots> < R" by (rule supconv_radius_uniform[OF low epos Rpos smw])
    finally have dR: "dist x z \<le> R" by linarith
    have dx: "dist x yh \<le> \<rho>" using d by simp
    show ?thesis by (rule near[OF dx dR insy])
  qed
  have D0: "(0::real) < 1" by simp
  have KGnn: "0 \<le> 3*kP" using kPnn by linarith
  show False
    by (rule comparison_supconv_maximiser_complete_gen
        [where u = u and w = w and \<xi>\<^sub>0 = "(xh, yh)" and D\<^sub>0 = 1
           and \<Omega>\<^sub>u = "interior K" and \<Omega>\<^sub>w = "interior K"
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa> = kP and \<rho> = \<rho> and r = kg
           and Pn = "soft_pen kP" and Gf = "soft_grad kP"
           and Zf = "soft_hess kP" and KZ = "2*kP" and KG = "3*kP"
           and Bu = Bu and Bw = Bw and c = c,
         OF sub sup t(1) t(2) epos kPnn
            soft_pen_semiconcave[OF kPnn] soft_pen_jet_field soft_hess_sym
            soft_hess_bound[OF kPnn] soft_grad_lipschitz[OF kPnn] KGnn
            rpos rltk D0 Bu Bw uu uw])
       (use mxK atu atw glb rsmall in blast)+
qed

subsection \<open>The theorem\<close>

theorem max_principle_usc_lsc:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "subsol_env2 K (interior K) u"
    and supw: "supersol_env2 K (interior K) w"
  shows "\<exists>x \<in> K - interior K. \<forall>y\<in>K. u y - w y \<le> u x - w x"
proof (rule ccontr)
  assume nb: "\<not> (\<exists>x \<in> K - interior K. \<forall>y\<in>K. u y - w y \<le> u x - w x)"
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have Kb: "bounded K" by (rule compact_imp_bounded[OF cK])
  have dim: "0 < CARD('n)" by simp
  obtain x0 where x0K: "x0 \<in> K" using neK by blast
  have B0: "0 \<le> B" using Bu[OF x0K] by linarith
  have uup: "u y \<le> B" if "y \<in> K" for y using Bu[OF that] by (simp add: abs_le_iff)
  have ulo: "- B \<le> u y" if "y \<in> K" for y using Bu[OF that] by (simp add: abs_le_iff)
  have wup: "w y \<le> B" if "y \<in> K" for y using Bw[OF that] by (simp add: abs_le_iff)
  have wlo: "- B \<le> w y" if "y \<in> K" for y using Bw[OF that] by (simp add: abs_le_iff)

  \<comment> \<open>1.  globally usc extensions of \<open>u\<close> and \<open>-w\<close>, by a constant below the data\<close>
  define C where "C = - B - 1"
  define ut where "ut = (\<lambda>y. if y \<in> K then u y else C)"
  define nw where "nw = (\<lambda>y. if y \<in> K then - w y else C)"
  define wt where "wt = (\<lambda>y. - nw y)"
  have nwt: "(- wt) = nw" by (rule ext) (simp add: wt_def)
  have utK: "ut y = u y" if "y \<in> K" for y using that by (simp add: ut_def)
  have nwK: "nw y = - w y" if "y \<in> K" for y using that by (simp add: nw_def)
  have wtK: "wt y = w y" if "y \<in> K" for y using that by (simp add: wt_def nw_def)
  have utC: "ut y = C" if "y \<notin> K" for y using that by (simp add: ut_def)
  have nwC: "nw y = C" if "y \<notin> K" for y using that by (simp add: nw_def)
  have utup: "ut y \<le> B" for y
  proof (cases "y \<in> K")
    case True then show ?thesis using uup[OF True] utK[OF True] by linarith
  next
    case False then show ?thesis using B0 utC[OF False] unfolding C_def by linarith
  qed
  have utlo: "C \<le> ut y" for y
  proof (cases "y \<in> K")
    case True then show ?thesis using ulo[OF True] utK[OF True] unfolding C_def by linarith
  next
    case False then show ?thesis using utC[OF False] by linarith
  qed
  have nwup: "nw y \<le> B" for y
  proof (cases "y \<in> K")
    case True then show ?thesis using wlo[OF True] nwK[OF True] by linarith
  next
    case False then show ?thesis using B0 nwC[OF False] unfolding C_def by linarith
  qed
  have nwlo: "C \<le> nw y" for y
  proof (cases "y \<in> K")
    case True then show ?thesis using wup[OF True] nwK[OF True] unfolding C_def by linarith
  next
    case False then show ?thesis using nwC[OF False] by linarith
  qed
  have uscut: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> ut y < c" if lt: "ut z < c" for c z
  proof -
    have lo: "C \<le> u y" if "y \<in> K" for y using ulo[OF that] unfolding C_def by linarith
    have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (if y \<in> K then u y else C) < c"
      by (rule usc_extend_rel[OF clK uscu lo lt[unfolded ut_def]])
    then show ?thesis unfolding ut_def .
  qed
  have uscnw: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> nw y < c" if lt: "nw z < c" for c z
  proof -
    have usc: "\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> - w y < c"
      if zK: "z \<in> K" and zc: "- w z < c" for c z
    proof -
      have "- c < w z" using zc by linarith
      from lscw[OF zK this] obtain e where e0: "0 < e"
        and h: "\<forall>y\<in>K. dist z y < e \<longrightarrow> - c < w y" by blast
      have "\<forall>y\<in>K. dist z y < e \<longrightarrow> - w y < c"
      proof (intro ballI impI)
        fix y assume "y \<in> K" "dist z y < e"
        then have "- c < w y" using h by blast
        then show "- w y < c" by linarith
      qed
      then show ?thesis using e0 by blast
    qed
    have lo: "C \<le> - w y" if "y \<in> K" for y using wup[OF that] unfolding C_def by linarith
    have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (if y \<in> K then - w y else C) < c"
      by (rule usc_extend_rel[OF clK usc lo lt[unfolded nw_def]])
    then show ?thesis unfolding nw_def .
  qed

  \<comment> \<open>2.  the maxima of \<open>u - w\<close> over \<open>K\<close> and over \<open>K - interior K\<close>\<close>
  define S where "S = K - interior K"
  have SK: "S \<subseteq> K" unfolding S_def by blast
  have clS: "closed S" unfolding S_def by (intro closed_Diff clK open_interior)
  have bS: "bounded S" by (rule bounded_subset[OF Kb SK])
  have cpS: "compact S" using bS clS by (simp add: compact_eq_bounded_closed)
  have neS: "S \<noteq> {}" unfolding S_def by (rule compact_frontier_nonempty[OF cK neK dim])
  have uscg: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> ut y + nw y < c" if "ut z + nw z < c" for c z
    by (rule usc_eps_add[OF uscut uscnw that])
  have gB: "ut y + nw y \<le> 2 * B" for y using utup[of y] nwup[of y] by linarith
  obtain xs where xsK: "xs \<in> K"
    and xsmax: "\<And>y. y \<in> K \<Longrightarrow> ut y + nw y \<le> ut xs + nw xs"
    using usc_attains_sup_gen[where f = "\<lambda>y. ut y + nw y" and S = K and B = "2*B",
        OF uscg gB cK neK] by blast
  obtain xb where xbS: "xb \<in> S"
    and xbmax: "\<And>y. y \<in> S \<Longrightarrow> ut y + nw y \<le> ut xb + nw xb"
    using usc_attains_sup_gen[where f = "\<lambda>y. ut y + nw y" and S = S and B = "2*B",
        OF uscg gB cpS neS] by blast
  have xbK: "xb \<in> K" using xbS SK by blast
  have gap: "u xb - w xb < u xs - w xs"
  proof -
    from nb xbS obtain y where yK: "y \<in> K"
      and ygt: "\<not> (u y - w y \<le> u xb - w xb)" unfolding S_def by blast
    have "ut y + nw y \<le> ut xs + nw xs" by (rule xsmax[OF yK])
    then have "u y - w y \<le> u xs - w xs"
      using utK[OF yK] nwK[OF yK] utK[OF xsK] nwK[OF xsK] by linarith
    then show ?thesis using ygt by linarith
  qed
  have bmax: "u y - w y \<le> u xb - w xb" if yS: "y \<in> S" for y
  proof -
    have yK: "y \<in> K" using yS SK by blast
    have "ut y + nw y \<le> ut xb + nw xb" by (rule xbmax[OF yS])
    then show ?thesis using utK[OF yK] nwK[OF yK] utK[OF xbK] nwK[OF xbK] by linarith
  qed

  \<comment> \<open>3.  the \<open>\<theta>\<close>-scaling keeps the boundary strictly below \<open>xs\<close>\<close>
  have Gpos: "0 < (u xs - w xs) - (u xb - w xb)" using gap by linarith
  obtain \<theta> where tpos: "0 < \<theta>" and tlt1: "\<theta> < 1"
    and tgap: "(1-\<theta>)*(2*B) < (u xs - w xs) - (u xb - w xb)"
    using theta_exists_aux[OF B0 Gpos] by blast
  have strict: "\<theta> * u y - w y < \<theta> * u xs - w xs" if y: "y \<in> S" for y
    by (rule theta_gap_preserved
        [where u = u and w = w and K = K and B = B and \<theta> = \<theta>
           and M = "u xs - w xs" and m = "u xb - w xb"
           and xs = xs and S = S and y = y,
         OF Bu less_imp_le[OF tlt1] tgap xsK order.refl SK bmax y])
  define MM where "MM = \<theta> * ut xs + nw xs"
  have MMval: "MM = \<theta> * u xs - w xs" unfolding MM_def using utK[OF xsK] nwK[OF xsK] by simp
  have strictS: "\<theta> * ut b + nw b < MM" if bS: "b \<in> S" for b
  proof -
    have bK: "b \<in> K" using bS SK by blast
    have "\<theta> * ut b + nw b = \<theta> * u b - w b" using utK[OF bK] nwK[OF bK] by simp
    then show ?thesis using strict[OF bS] MMval by linarith
  qed
  have uut: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> \<theta> * ut y < c" if "\<theta> * ut z < c" for c z
    by (rule usc_eps_scale[OF uscut tpos that])

  \<comment> \<open>4.  a Lebesgue number for the cover of the boundary by the open sets on
      which the doubled data stays below \<open>MM\<close>; this replaces the uniform
      moduli of the continuous case\<close>
  define GG where "GG = {U. open U \<and> (\<forall>z1\<in>U. \<forall>z2\<in>U. \<theta> * ut z1 + nw z2 < MM)}"
  have opn: "open G" if "G \<in> GG" for G using that unfolding GG_def by blast
  have cover: "S \<subseteq> \<Union>GG"
  proof
    fix b assume bS: "b \<in> S"
    define \<delta> where "\<delta> = MM - (\<theta> * ut b + nw b)"
    have \<delta>0: "0 < \<delta>" unfolding \<delta>_def using strictS[OF bS] by linarith
    define \<eta> where "\<eta> = \<delta> / 2"
    have \<eta>0: "0 < \<eta>" unfolding \<eta>_def using \<delta>0 by linarith
    define U where "U = {y. \<theta> * ut y < \<theta> * ut b + \<eta>} \<inter> {y. nw y < nw b + \<eta>}"
    have oU: "open U" unfolding U_def
      by (intro open_Int open_usc_sublevel[OF uut] open_usc_sublevel[OF uscnw])
    have bU: "b \<in> U" unfolding U_def using \<eta>0 by simp
    have pU: "\<forall>z1\<in>U. \<forall>z2\<in>U. \<theta> * ut z1 + nw z2 < MM"
    proof (intro ballI)
      fix z1 z2 assume "z1 \<in> U" "z2 \<in> U"
      then have "\<theta> * ut z1 < \<theta> * ut b + \<eta>" "nw z2 < nw b + \<eta>" unfolding U_def by auto
      then show "\<theta> * ut z1 + nw z2 < MM" using \<delta>_def \<eta>_def by linarith
    qed
    have "U \<in> GG" unfolding GG_def using oU pU by blast
    then show "b \<in> \<Union>GG" using bU by blast
  qed
  obtain e where e0: "0 < e" and leb: "\<And>x. x \<in> S \<Longrightarrow> \<exists>G\<in>GG. ball x e \<subseteq> G"
    using Heine_Borel_lemma[OF cpS cover opn] by blast
  have loc: "e/2 \<le> dist b z1 \<and> e/2 \<le> dist b z2"
    if bS: "b \<in> S" and dz: "dist z1 z2 < e/4" and val: "MM \<le> \<theta> * ut z1 + nw z2"
    for b z1 z2
  proof -
    have no: False if i1: "dist b z1 < e" and i2: "dist b z2 < e"
    proof -
      obtain G where GG: "G \<in> GG" and bG: "ball b e \<subseteq> G" using leb[OF bS] by blast
      have "z1 \<in> G" "z2 \<in> G" using bG i1 i2 by auto
      then have "\<theta> * ut z1 + nw z2 < MM" using GG unfolding GG_def by blast
      then show False using val by linarith
    qed
    have t1: "dist b z2 \<le> dist b z1 + dist z1 z2" by (rule dist_triangle)
    have t2: "dist b z1 \<le> dist b z2 + dist z2 z1" by (rule dist_triangle)
    have ds: "dist z2 z1 = dist z1 z2" by (rule dist_commute)
    show ?thesis
    proof
      show "e/2 \<le> dist b z1"
      proof (rule ccontr)
        assume "\<not> e/2 \<le> dist b z1"
        then have "dist b z1 < e" "dist b z2 < e" using t1 dz e0 by linarith+
        then show False by (rule no)
      qed
      show "e/2 \<le> dist b z2"
      proof (rule ccontr)
        assume "\<not> e/2 \<le> dist b z2"
        then have "dist b z1 < e" "dist b z2 < e" using t2 ds dz e0 by linarith+
        then show False by (rule no)
      qed
    qed
  qed

  \<comment> \<open>5.  the parameters, in the order the localisation needs them\<close>
  define kg where "kg = e/4"
  have kgpos: "0 < kg" unfolding kg_def using e0 by simp
  have kg4: "0 < kg/4" using kgpos by simp
  define D where "D = B - C"
  have Dnn: "0 \<le> D" unfolding D_def C_def using B0 by linarith
  have H0: "0 < (kg/4)\<^sup>2" using kgpos by simp
  obtain \<epsilon> where epos: "0 < \<epsilon>" and esm: "2*\<epsilon>*D < (kg/4)\<^sup>2"
    using exists_eps_aux[OF H0 Dnn] by blast
  have tD: "\<theta> * D \<le> D"
    by (rule mult_left_le_one_le[OF Dnn less_imp_le[OF tpos] less_imp_le[OF tlt1]])
  have eq1: "\<theta>*B - \<theta>*C = \<theta> * D" unfolding D_def by (simp add: right_diff_distrib)
  have smallu: "2*\<epsilon>*(\<theta>*B - \<theta>*C) < (kg/4)\<^sup>2"
  proof -
    have "2*\<epsilon>*(\<theta>*B - \<theta>*C) \<le> 2*\<epsilon>*D"
      unfolding eq1 by (rule mult_left_mono[OF tD]) (use epos in simp)
    then show ?thesis using esm by linarith
  qed
  have smallw: "2*\<epsilon>*(B - C) < (kg/4)\<^sup>2" using esm unfolding D_def .
  have Bu': "\<theta> * ut y \<le> \<theta> * B" for y by (rule mult_left_mono[OF utup]) (use tpos in simp)
  have lou': "\<theta> * C \<le> \<theta> * ut y" for y by (rule mult_left_mono[OF utlo]) (use tpos in simp)
  have Bw': "(- wt) y \<le> B" for y unfolding nwt by (rule nwup)
  have low': "C \<le> (- wt) y" for y unfolding nwt by (rule nwlo)
  have uwt: "\<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- wt) y < c" if "(- wt) z < c" for c z
    using uscnw that unfolding nwt by blast

  \<comment> \<open>6.  the doubled maximiser over \<open>K \<times> K\<close>, with \<open>|xh - yh| < kg/4\<close>\<close>
  have bnd: "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> x + supconv (- wt) \<epsilon> y \<le> \<theta> * B + B"
    if "x \<in> K" "y \<in> K" for x y
  proof -
    have "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> x \<le> \<theta> * B" by (rule supconv_le[OF Bu' epos])
    moreover have "supconv (- wt) \<epsilon> y \<le> B" by (rule supconv_le[OF Bw' epos])
    ultimately show ?thesis by linarith
  qed
  obtain kP xh yh where kPpos: "0 < kP" and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxb: "\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * ut y) \<epsilon> x + supconv (- wt) \<epsilon> y - soft_pen kP (x - y)
        \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> yh
          - soft_pen kP (xh - yh)"
    and near: "dist xh yh < kg/4"
    using doubling_close_maximiser_supconv_soft[OF cK neK Bu' Bw' epos xsK bnd kg4]
    by blast
  have mx: "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> x + supconv (- wt) \<epsilon> y - soft_pen kP (x - y)
      \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> yh
        - soft_pen kP (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mxb that by blast
  have kPnn: "0 \<le> kP" using kPpos by linarith

  \<comment> \<open>7.  the attainment points carry the value \<open>MM\<close> and sit next to the
      maximiser, so the Lebesgue number keeps the maximiser off the boundary\<close>
  have base: "MM \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> yh
      - soft_pen kP (xh - yh)"
  proof -
    have a1: "\<theta> * ut xs \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xs" by (rule supconv_ge[OF Bu' epos])
    have a2: "(- wt) xs \<le> supconv (- wt) \<epsilon> xs" by (rule supconv_ge[OF Bw' epos])
    have a3: "soft_pen kP (xs - xs) = 0" by (simp add: soft_pen_zero)
    have a4: "(- wt) xs = nw xs" by (simp add: nwt)
    have "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xs + supconv (- wt) \<epsilon> xs - soft_pen kP (xs - xs)
        \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> yh - soft_pen kP (xh - yh)"
      by (rule mx[OF xsK xsK])
    then show ?thesis unfolding MM_def using a1 a2 a3 a4 by linarith
  qed
  obtain z1 where o1: "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh
      = \<theta> * ut z1 - (dist xh z1)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF Bu' epos uut, where x = xh] by blast
  obtain z2 where o2: "supconv (- wt) \<epsilon> yh = (- wt) z2 - (dist yh z2)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF Bw' epos uwt, where x = yh] by blast
  have val: "MM \<le> \<theta> * ut z1 + nw z2"
  proof -
    have q1: "0 \<le> (dist xh z1)\<^sup>2 / (2*\<epsilon>)" using epos by simp
    have q2: "0 \<le> (dist yh z2)\<^sup>2 / (2*\<epsilon>)" using epos by simp
    have q3: "0 \<le> soft_pen kP (xh - yh)" by (rule soft_pen_nonneg[OF kPnn])
    have q4: "(- wt) z2 = nw z2" by (simp add: nwt)
    show ?thesis using base o1 o2 q1 q2 q3 q4 by linarith
  qed
  have rad1: "dist xh z1 < kg/4"
  proof -
    have "dist xh z1 \<le> sqrt (max 0 (2*\<epsilon>*(\<theta>*B - \<theta> * ut xh)))"
      by (rule supconv_attain_radius[OF Bu' epos o1])
    also have "\<dots> < kg/4" by (rule supconv_radius_uniform[OF lou' epos kg4 smallu])
    finally show ?thesis .
  qed
  have rad2: "dist yh z2 < kg/4"
  proof -
    have "dist yh z2 \<le> sqrt (max 0 (2*\<epsilon>*(B - (- wt) yh)))"
      by (rule supconv_attain_radius[OF Bw' epos o2])
    also have "\<dots> < kg/4" by (rule supconv_radius_uniform[OF low' epos kg4 smallw])
    finally show ?thesis .
  qed
  have dz: "dist z1 z2 < e/4"
  proof -
    have "dist z1 z2 \<le> dist z1 xh + dist xh z2" by (rule dist_triangle)
    moreover have "dist xh z2 \<le> dist xh yh + dist yh z2" by (rule dist_triangle)
    moreover have "dist z1 xh = dist xh z1" by (rule dist_commute)
    ultimately show ?thesis using rad1 rad2 near e0 unfolding kg_def by linarith
  qed
  have farz: "e/2 \<le> dist b z1 \<and> e/2 \<le> dist b z2" if "b \<in> S" for b
    by (rule loc[OF that dz val])
  have farx: "kg < dist xh b" if b: "b \<in> K - interior K" for b
  proof -
    have bS: "b \<in> S" using b unfolding S_def .
    have "dist b z1 \<le> dist b xh + dist xh z1" by (rule dist_triangle)
    moreover have "dist b xh = dist xh b" by (rule dist_commute)
    ultimately show ?thesis using farz[OF bS] rad1 e0 unfolding kg_def by linarith
  qed
  have fary: "kg < dist yh b" if b: "b \<in> K - interior K" for b
  proof -
    have bS: "b \<in> S" using b unfolding S_def .
    have "dist b z2 \<le> dist b yh + dist yh z2" by (rule dist_triangle)
    moreover have "dist b yh = dist yh b" by (rule dist_commute)
    ultimately show ?thesis using farz[OF bS] rad2 e0 unfolding kg_def by linarith
  qed

  \<comment> \<open>8.  the viscosity properties of the extensions, in jet form\<close>
  have subenv: "subsol_env2 K (interior K) ut"
    by (rule visc_subsol_env2_cong[OF interior_subset _ subu]) (simp add: ut_def)
  have sub: "subsol (interior K) ut"
    by (rule visc_subsol_env_imp_visc_subsol
        [OF subenv Kb _, where Bu = B]) (use utup in simp)
  have supj0: "supersol_usc (interior K) w"
    by (rule visc_supersol_env_imp_jet[OF supw Kb wlo])
  have sup: "supersol_usc (interior K) wt"
  proof (rule supersol_jet_cong_on[OF supj0 open_interior])
    fix y assume "y \<in> interior K"
    then have "y \<in> K" using interior_subset by blast
    then show "wt y = w y" by (rule wtK)
  qed

  \<comment> \<open>9.  the two branches\<close>
  show False
  proof (cases "xh = yh")
    case False
    show False
      by (rule comparison_soft_off_diagonal_usc
          [where u = ut and w = wt and K = K and \<theta> = \<theta> and \<epsilon> = \<epsilon>
             and Bu = "\<theta>*B" and Bw = B and Blu = "\<theta>*C" and Blw = C
             and kg = kg and kP = kP and xh = xh and yh = yh,
           OF sub sup tpos tlt1 cK Bu' Bw' lou' low' uut uwt
              epos kgpos kPpos xhK yhK mx farx fary smallu smallw False])
  next
    case True
    have kgnn: "0 \<le> kg" using kgpos by linarith
    have insx: "cball xh kg \<subseteq> interior K"
      by (rule cball_subset_interior_of_far_from_boundary[OF clK xhK kgnn farx])
    have pint: "xh \<in> interior K" using insx kgnn by auto
    have subw: "cball xh (kg/4) \<subseteq> interior K"
    proof -
      have "cball xh (kg/4) \<subseteq> cball xh kg"
        using kgpos by (simp add: cball_subset_cball_iff)
      then show ?thesis using insx by blast
    qed
    have rad: "sqrt (max 0 (2*\<epsilon>*(B - (- wt) xh))) < kg/4"
      by (rule supconv_radius_uniform[OF low' epos kg4 smallw])
    have mxd: "supconv (\<lambda>y. \<theta> * ut y) \<epsilon> x + supconv (- wt) \<epsilon> y
          - soft_pen kP (x - y)
        \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> xh
          - soft_pen kP (xh - xh)" if "x \<in> K" "y \<in> K" for x y
      using mx[OF that] unfolding True[symmetric] .
    show False
      by (rule comparison_soft_diagonal
          [where w = wt and K = K and A = "supconv (\<lambda>y. \<theta> * ut y) \<epsilon>"
             and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = kP and p = xh and R\<^sub>w = "kg/4" and Bw = B,
           OF sup Bw' uwt epos xhK pint mxd rad subw])
  qed
qed

text \<open>Theorem 4.2(b): ordered boundary data stay ordered, since \<open>u - w\<close> peaks
  on the boundary.\<close>

corollary max_principle_le:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "subsol_env2 K (interior K) u"
    and supw: "supersol_env2 K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y \<le> w y"
  shows "\<And>y. y \<in> K \<Longrightarrow> u y \<le> w y"
proof -
  fix y assume "y \<in> K"
  moreover obtain x where "x \<in> K - interior K" and "\<forall>y\<in>K. u y - w y \<le> u x - w x"
    using max_principle_usc_lsc[OF cK neK uscu lscw Bu Bw subu supw] by blast
  ultimately show "u y \<le> w y" using bd by fastforce
qed

text \<open>Proposition 4.1 (uniqueness): two solutions with the same boundary data
  agree, by the comparison in both directions.  A solution is both usc and lsc
  relative to \<open>K\<close>.\<close>

corollary uniqueness_from_max_principle:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and uscu: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and lscu: "\<And>c z. z \<in> K \<Longrightarrow> c < u z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < u y"
    and uscw: "\<And>c z. z \<in> K \<Longrightarrow> w z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> w y < c"
    and lscw: "\<And>c z. z \<in> K \<Longrightarrow> c < w z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
    and subu: "subsol_env2 K (interior K) u"
    and supu: "supersol_env2 K (interior K) u"
    and subw: "subsol_env2 K (interior K) w"
    and supw: "supersol_env2 K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
  shows "\<And>y. y \<in> K \<Longrightarrow> u y = w y"
proof -
  fix y assume y: "y \<in> K"
  have le1: "u z \<le> w z" and le2: "w z \<le> u z" if "z \<in> K - interior K" for z
    using bd[OF that] by simp_all
  have "u y \<le> w y"
    by (rule max_principle_le[OF cK neK uscu lscw Bu Bw subu supw le1 y])
  moreover have "w y \<le> u y"
    by (rule max_principle_le[OF cK neK uscw lscu Bw Bu subw supu le2 y])
  ultimately show "u y = w y" by simp
qed

end

text \<open>Continuous data on compact \<open>K\<close> are bounded and semicontinuous relative
  to \<open>K\<close> in both directions, and the touching-on-\<open>K\<close> predicates pass to the
  \<open>C\<^sup>2\<close> ones; so Theorem 4.2(a) and uniqueness hold for them.\<close>

lemma continuous_on_rel_eps:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes cf: "continuous_on K f" and z: "z \<in> K"
  shows continuous_on_rel_usc: "f z < c \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> f y < c"
    and continuous_on_rel_lsc: "c < f z \<Longrightarrow> \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < f y"
proof -
  have *: "\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> \<bar>f y - f z\<bar> < \<bar>c - f z\<bar>" if "c \<noteq> f z"
  proof -
    have pos: "0 < \<bar>c - f z\<bar>" using that by simp
    obtain d where "0 < d" "\<forall>y\<in>K. dist y z < d \<longrightarrow> dist (f y) (f z) < \<bar>c - f z\<bar>"
      using cf[unfolded continuous_on_iff, rule_format, OF z pos] by blast
    then show ?thesis by (auto simp: dist_commute dist_real_def)
  qed
  show "\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> f y < c" if lt: "f z < c"
  proof -
    obtain e where "0 < e" "\<forall>y\<in>K. dist z y < e \<longrightarrow> \<bar>f y - f z\<bar> < \<bar>c - f z\<bar>"
      using *[of] lt by force
    then show ?thesis using lt by (intro exI[of _ e]) (auto simp: abs_less_iff)
  qed
  show "\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> c < f y" if lt: "c < f z"
  proof -
    obtain e where "0 < e" "\<forall>y\<in>K. dist z y < e \<longrightarrow> \<bar>f y - f z\<bar> < \<bar>c - f z\<bar>"
      using *[of] lt by force
    then show ?thesis using lt by (intro exI[of _ e]) (auto simp: abs_less_iff)
  qed
qed

context geometric_operator
begin

corollary max_principle_boundary_holds:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and subE: "subsol_env K (interior K) u"
    and supE: "supersol_env K (interior K) w"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>x\<in>K - interior K. \<forall>y\<in>K. u y - w y \<le> u x - w x"
proof -
  obtain Bu Bw where "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bu" "\<forall>y\<in>K. \<bar>w y\<bar> \<le> Bw"
    using bounded_on_compact[OF cK cu] bounded_on_compact[OF cK cw] by blast
  then have B: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> max Bu Bw \<and> \<bar>w y\<bar> \<le> max Bu Bw"
    by (auto simp: le_max_iff_disj)
  show ?thesis
    by (rule max_principle_usc_lsc[OF cK neK continuous_on_rel_usc[OF cu]
          continuous_on_rel_lsc[OF cw], where B = "max Bu Bw"])
      (use B visc_subsol_env_imp_env2[OF subE] visc_supersol_env_imp_env2[OF supE] in auto)
qed

section \<open>Uniqueness on a general compact set\<close>

text \<open>The first consequence of Theorem 4.2(a), for continuous solutions on
  compact \<open>K\<close> agreeing on \<open>K - interior K\<close>: an instance of
  @{thm [source] uniqueness_from_max_principle}.\<close>

theorem viscosity_uniqueness_compact:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and subu: "subsol_env K (interior K) u"
    and supu: "supersol_env K (interior K) u"
    and subw: "subsol_env K (interior K) w"
    and supw: "supersol_env K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  obtain Bu Bw where "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bu" "\<forall>y\<in>K. \<bar>w y\<bar> \<le> Bw"
    using bounded_on_compact[OF cK cu] bounded_on_compact[OF cK cw] by blast
  then have B: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> max Bu Bw \<and> \<bar>w y\<bar> \<le> max Bu Bw"
    by (auto simp: le_max_iff_disj)
  show ?thesis
    by (rule uniqueness_from_max_principle[OF cK neK
          continuous_on_rel_usc[OF cu] continuous_on_rel_lsc[OF cu]
          continuous_on_rel_usc[OF cw] continuous_on_rel_lsc[OF cw], where B = "max Bu Bw"])
      (use B bd x visc_subsol_env_imp_env2 visc_supersol_env_imp_env2 subu supu subw supw in auto)
qed

end

section \<open>Map of the Theorem 4.2(a) chain\<close>

text \<open>This theory is long enough that the order of the argument is not
  visible from the section headings; the chain in dependency order:

  1. The operator and its envelopes: \<open>env_strict_contradiction\<close>
  gives the closing contradiction off the origin.

  2. The doubling: \<open>doubling_maximiser_exists_gen\<close>, \<open>doubling_near_soft\<close>,
  \<open>soft_grad_norm_pos\<close> give the maximising pair, the closeness of its
  components once \<open>\<kappa>\<close> is large, and a positive lower bound on the shared
  gradient.

  3. Doubled jet to component jets to operator bounds:
  \<open>doubled_supconv_jet_exists_shifted_gen\<close>, \<open>tilted_doubled_jet_slices_gen\<close>,
  \<open>superjet_local_max\<close>, \<open>visc_subsol_scaled_uniform\<close>.

  4. Removing corrections, and compactness:
  \<open>op_lsc_le_of_nearby\<close> passes a bound at nearby points to the
  envelope, subsuming both the \<open>\<delta> I\<close> shift and Jensen's tilt;
  \<open>symmetric_form_bound\<close> and \<open>bounded_seq_limit_point_triple\<close> turn
  quadratic-form bounds into a limiting matrix pair without the spectral
  theorem.

  5. Assembly from bounds rather than limits:
  \<open>comparison_supconv_bounded_family\<close>, \<open>tilted_doubled_psd_ordering_gen\<close>.

  6. The instantiation: \<open>max_principle_usc_lsc\<close> closes Theorem 4.2(a)
  for semicontinuous data, with \<open>comparison_soft_diagonal\<close> closing the
  diagonal branch, where \<open>p = 0\<close>; \<open>max_principle_boundary_holds\<close> is its
  continuous-data form.\<close>


(*<*)
end
(*>*)
