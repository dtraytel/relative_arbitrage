section \<open>Sup-convolution jets and the contradiction in the limit\<close>

(*<*)
theory Comparison_Localisation
  imports Comparison_Strictness
begin

(*>*)


text \<open>The comparison argument doubles the variables in the
  sup-convolutions of the scaled subsolution and of the negated
  supersolution, which are semiconvex, and Jensen's lemma supplies
  second-order jets at the maximisers of the doubled functional (the
  doubling and penalty tools are in
  @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}).  This
  theory turns those jets into operator inequalities for the original
  functions and shows that the inequalities contradict each other in the
  limit.\<close>

subsection \<open>The supersolution has no vanishing one-sided subjet\<close>

text \<open>A supersolution for \<open>F\<^sup>*\<close> has no one-sided second-order subjet
  \<open>(0, 0)\<close> at a point of \<open>\<Omega>\<close>: the supersolution inequality at the
  shifted matrix \<open>- \<delta> I\<close> (\<open>supersol_shifted_bound_onesided\<close>)
  contradicts the locale's \<open>usc_small_shift\<close>.  This rules out a doubled
  maximum on the diagonal for a penalty whose 2-jet vanishes at the
  origin, such as the quartic one.\<close>

context geometric_operator
begin

theorem supersol_no_vanishing_jet_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "supersol_usc \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh) / (norm hh)\<^sup>2 < c"
  shows False
proof -
  obtain \<delta> :: real where d0: "0 < \<delta>"
    and ltone: "\<And>q :: real^'n.
      F_usc q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
  proof (rule usc_small_shift_lt_one)
    fix dd :: real
    assume a1: "0 < dd" and a2: "dd < 1"
      and a3: "\<And>q :: real^'n.
        F_usc q ((0::real^'n^'n) - dd *\<^sub>R mat 1) < 1"
    show thesis by (rule that[OF a1 a3])
  qed
  have Ys: "transpose (0::real^'n^'n) = 0"
    by (simp add: transpose_def vec_eq_iff)
  have ub0: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
      ((- w) (yh + hh) - (- w) yh - (- (0::real^'n)) \<bullet> hh
        - (hh \<bullet> ((- (0::real^'n^'n)) *v hh))/2) / (norm hh)\<^sup>2 < c"
    using ub by simp
  have one: "1 \<le> F_usc (0::real^'n)
      ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_onesided[OF sup yh Ys ub0 d0])
  show False using one ltone[of "0::real^'n"] by simp

qed

subsection \<open>Operator bounds from sup-convolution jets\<close>

text \<open>The comparison argument's doubled functional is built from the
  sup-convolutions of \<open>\<theta> u\<close> and \<open>- w\<close>, since those are what is semiconvex
  and what Jensen's lemma applies to; the jet produced at the doubled
  maximum is thus a jet of \<open>supconv (\<theta> u) \<epsilon>\<close>, not of \<open>\<theta> u\<close>. This
  theorem closes that gap: the \<open>\<delta>\<close>-corrected quadratic bound for the
  sup-convolution at \<open>x\<close> transfers, by \<open>supconv_local_max_transfer_ball\<close>,
  to the same bound for \<open>\<theta> u\<close> at the attaining point \<open>y\<^sub>s\<close> -- same
  \<open>p\<close>, same matrix -- where the viscosity property applies, with
  \<open>y\<^sub>s\<close> now the point that must lie in \<open>\<Omega>\<close>.\<close>

theorem subsol_shifted_bound_supconv:
  fixes u :: "real^'n::finite \<Rightarrow> real" and Xm :: "real^'n^'n"
  assumes sub: "subsol \<Omega> u"
    and t: "0 < \<theta>"
    and ysO: "ys \<in> \<Omega>"
    and Xs: "transpose Xm = Xm"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
        = \<theta> * u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "F p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
proof -
  have sym: "transpose (Xm + \<delta> *\<^sub>R mat 1) = Xm + \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_add[OF Xs])
  obtain r where r: "0 < r"
    and b: "\<And>h. norm h < r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
          - (p \<bullet> h + (h \<bullet> (Xm *v h))/2 + (\<delta>/2) * (norm h)\<^sup>2)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> x"
    using superjet_local_max[OF jet d] by blast
  have lm: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
        - (p \<bullet> h + (h \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v h))/2)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> x" if "norm h < r" for h
  proof -
    have q: "h \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v h)
        = h \<bullet> (Xm *v h) + \<delta> * (norm h)\<^sup>2"
      by (rule quad_form_shift_identity)
    from b[OF that] show ?thesis
      unfolding q by (simp add: add_divide_distrib)
  qed
  have maxloc: "\<exists>e>0. \<forall>z \<in> ball ys e.
      \<theta> * u z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> \<theta> * u ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    by (rule supconv_local_max_transfer_ball[OF Bu e opt r lm])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - ys)
        + ((z - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      (\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) (Xm + \<delta> *\<^sub>R mat 1) ys"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys = p"
    by simp
  have "F ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    by (rule visc_subsol_scaled_uniform[OF sub dilation homogeneous t ysO tf maxloc])
  thus ?thesis unfolding g .
qed

end

text \<open>The supersolution side, for any operator \<open>G\<close>: a jet of the
  sup-convolution of \<open>- w\<close> at \<open>x\<close> gives the supersolution inequality at
  the attaining point, with the matrix corrected to \<open>Y - \<delta> I\<close>.\<close>

theorem supersol_shifted_bound_supconv:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n^'n \<Rightarrow> ereal"
  assumes sup: "visc_supersol_gen test_fun_at nhds G \<Omega> w"
    and ysO: "ys \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "1 \<le> G p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have sym: "transpose (Ym - \<delta> *\<^sub>R mat 1) = Ym - \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_diff[OF Ys])
  obtain r where r: "0 < r"
    and b: "\<And>h. norm h < r \<Longrightarrow>
        supconv (- w) \<epsilon> (x + h)
          - ((- p) \<bullet> h + (h \<bullet> ((- Ym) *v h))/2 + (\<delta>/2) * (norm h)\<^sup>2)
        \<le> supconv (- w) \<epsilon> x"
    using superjet_local_max[OF jet d] by blast
  have lm: "supconv (- w) \<epsilon> (x + h)
        - ((- p) \<bullet> h + (h \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v h))/2)
      \<le> supconv (- w) \<epsilon> x" if "norm h < r" for h
  proof -
    have q: "h \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v h)
        = h \<bullet> ((- Ym) *v h) + \<delta> * (norm h)\<^sup>2"
      by (rule quad_form_shift_identity)
    from b[OF that] show ?thesis
      unfolding q by (simp add: add_divide_distrib)
  qed
  have tr: "\<exists>e>0. \<forall>z \<in> ball ys e.
      (- w) z - ((- p) \<bullet> (z - ys)
          + ((z - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> (- w) ys - ((- p) \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    by (rule supconv_local_max_transfer_ball[OF Bw e opt r lm])
  obtain s where s: "0 < s"
    and m: "\<And>z. z \<in> ball ys s \<Longrightarrow>
      (- w) z - ((- p) \<bullet> (z - ys)
          + ((z - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> (- w) ys - ((- p) \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    using tr by blast
  have minloc: "\<exists>e>0. \<forall>z \<in> ball ys e.
      w ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)
      \<le> w z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)"
  proof (rule exI[of _ s], intro conjI ballI)
    show "0 < s" by (rule s)
    fix z assume z: "z \<in> ball ys s"
    from m[OF z] show
      "w ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)
      \<le> w z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)"
      unfolding neg_shift_matrix_apply
      by simp
  qed
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - ys)
        + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      (\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) (Ym - \<delta> *\<^sub>R mat 1) ys"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) ys = p"
    by simp
  have "1 \<le> G ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup ysO tf minloc unfolding visc_supersol_gen_nhds by blast
  thus ?thesis unfolding g .
qed

text \<open>For \<open>G = F\<^sup>*\<close> and \<open>p \<noteq> 0\<close> the envelope is \<open>F\<close> itself
  (\<open>usc_off_zero\<close>).\<close>

context geometric_operator
begin

corollary supersol_shifted_bound_supconv_ne:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_usc \<Omega> w" and ysO: "ys \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>" and p0: "p \<noteq> 0"
  shows "1 \<le> F p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have "1 \<le> F_usc p (Ym - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_supconv[OF sup ysO Ys Bw e opt jet d])
  then show ?thesis
    using usc_off_zero[OF transpose_shift_diff[OF Ys] p0] by simp
qed

subsection \<open>The contradiction from bounds at nearby points\<close>

text \<open>Jensen's lemma perturbs the gradient as well as the matrix, so the
  operator bounds arrive at points near \<open>(p, X)\<close> and \<open>(p, Y)\<close>, not at
  them.  Bounds holding arbitrarily close to a point pass to the envelopes
  there (@{thm [source] op_lsc_le_of_nearby},
  @{thm [source] op_usc_ge_of_nearby}), and off \<open>p = 0\<close> the envelopes are
  \<open>F\<close>; so a strict bound \<open>c < 1\<close> near \<open>(p, X)\<close> and the bound \<open>1\<close> near
  \<open>(p, Y)\<close> contradict degenerate ellipticity when \<open>X \<preceq> Y\<close>.\<close>

theorem env_strict_contradiction_of_nearby:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and pnz: "p \<noteq> 0" and c1: "c < 1"
    and subs: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X) < e
        \<and> F p' M' \<le> c"
    and sups: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y) < e
        \<and> 1 \<le> F p' M'"
  shows False
proof -
  have lsc: "F_lsc p X \<le> ereal c"
    by (rule op_lsc_le_of_nearby[OF subs])
  have c1e: "ereal c < 1"
    using c1 by (simp add: one_ereal_def)
  have sub: "F_lsc p X < 1"
    using lsc c1e by (rule le_less_trans)
  have sup: "1 \<le> F_usc p Y"
    using op_usc_ge_of_nearby[OF sups] by (simp add: one_ereal_def)
  show False
    by (rule env_strict_contradiction[OF psd symX symY pnz sub sup])
qed

end

subsection \<open>Scaling preserves a strict gap\<close>

text \<open>If \<open>\<bar>u\<bar> \<le> B\<close> on \<open>K\<close> and \<open>u - w\<close> exceeds its values on \<open>S \<subseteq> K\<close> by
  more than \<open>(1 - \<theta>) 2B\<close> at a point of \<open>K\<close>, then \<open>\<theta> u - w\<close> still
  separates that point strictly from \<open>S\<close>: the strict subsolution
  \<open>\<theta> u\<close> inherits the gap of \<open>u - w\<close>.\<close>

lemma theta_gap_preserved:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
    and t: "\<theta> \<le> 1"
    and gap: "(1 - \<theta>) * (2*B) < M - m"
    and xK: "xs \<in> K" and xval: "M \<le> u xs - w xs"
    and SK: "S \<subseteq> K"
    and bdry: "\<And>y. y \<in> S \<Longrightarrow> u y - w y \<le> m"
    and y: "y \<in> S"
  shows "\<theta> * u y - w y < \<theta> * u xs - w xs"
proof -
  have yK: "y \<in> K" using y SK by blast
  have t0: "0 \<le> 1 - \<theta>" using t by simp
  have uy: "\<bar>u y\<bar> \<le> B" by (rule bd[OF yK])
  have ux: "\<bar>u xs\<bar> \<le> B" by (rule bd[OF xK])
  have ly: "(1 - \<theta>) * (- B) \<le> (1 - \<theta>) * u y"
    by (rule mult_left_mono[OF _ t0]) (use uy in linarith)
  have lx: "(1 - \<theta>) * u xs \<le> (1 - \<theta>) * B"
    by (rule mult_left_mono[OF _ t0]) (use ux in linarith)  have ey: "\<theta> * u y - w y = (u y - w y) - (1 - \<theta>) * u y"
    by (simp add: algebra_simps)
  have ex: "\<theta> * u xs - w xs = (u xs - w xs) - (1 - \<theta>) * u xs"
    by (simp add: algebra_simps)
  have my: "u y - w y \<le> m" by (rule bdry[OF y])
  have dexp: "(1 - \<theta>) * (2*B) = (1 - \<theta>) * B + (1 - \<theta>) * B"
    by (simp add: algebra_simps)
  have neg: "(1 - \<theta>) * (- B) = - ((1 - \<theta>) * B)"
    by (simp add: algebra_simps)
  from ly lx my xval gap show ?thesis
    unfolding ey ex using dexp neg by linarith
qed

subsection \<open>The contradiction along a sequence of jets\<close>

text \<open>The form in which the doubling delivers the bounds: along sequences
  \<open>X\<^sub>i \<longlonglongrightarrow> X\<^sub>0\<close>, \<open>Y\<^sub>i \<longlonglongrightarrow> Y\<^sub>0\<close> with gradients converging to
  \<open>p \<noteq> 0\<close>, a bound \<open>F \<le> c < 1\<close> at \<open>X\<^sub>i + \<delta> I\<close> and a bound
  \<open>F \<ge> 1\<close> at \<open>Y\<^sub>i - \<delta> I\<close> for all small \<open>\<delta> > 0\<close> contradict
  \<open>X\<^sub>0 \<preceq> Y\<^sub>0\<close>.  No rate and no relation between \<open>i\<close> and \<open>\<delta>\<close> is
  assumed.\<close>

context geometric_operator
begin

theorem env_strict_contradiction_of_shifted_limits:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and p0: "psd (Y0 - X0)"
    and pnz: "p \<noteq> 0"
    and c1: "c < 1" and D: "0 < D"
    and bndu: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        F (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> c"
    and bndw: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        1 \<le> F (Pw i) (Y i - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have sX0: "transpose X0 = X0"
    by (rule transpose_limit[OF cX symX])
  have sY0: "transpose Y0 = Y0"
    by (rule transpose_limit[OF cY symY])
  note p0
  have subs: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X0) < e
      \<and> F p' M' \<le> c" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pu i, X i)) \<longlonglongrightarrow> ((p, X0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPu cX])
    show ?thesis
      by (rule nearby_of_convergent_shifted
          [where Q = "\<lambda>p' M'. F p' M' \<le> c", OF cZ bndu D e0])
  qed
  have sups: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y0) < e
      \<and> 1 \<le> F p' M'" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pw i, Y i)) \<longlonglongrightarrow> ((p, Y0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPw cY])
    show ?thesis
      by (rule nearby_of_convergent_shifted_neg
          [where Q = "\<lambda>p' M'. 1 \<le> F p' M'", OF cZ bndw D e0])
  qed
  show False
    by (rule env_strict_contradiction_of_nearby[OF p0 sX0 sY0 pnz c1 subs sups])
qed

subsection \<open>The contradiction from a sequence of sup-convolution jets\<close>

text \<open>Each index \<open>i\<close> of the Jensen application supplies a maximiser, its jet,
  and the sup-convolution attainment point.  The per-index operator bounds
  come from \<open>subsol_shifted_bound_supconv\<close> and
  \<open>supersol_shifted_bound_supconv\<close>, and
  \<open>env_strict_contradiction_of_shifted_limits\<close> takes both limits, with no
  rate and no relation assumed between \<open>i\<close> and \<open>\<delta>\<close>.\<close>

theorem comparison_supconv_sequence_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "nat \<Rightarrow> real^'n^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
    and xu xw ysu ysw :: "nat \<Rightarrow> real^'n"
  assumes sub: "subsol \<Omega>\<^sub>u u" and sup: "supersol_usc \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and e: "0 < \<epsilon>"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and ysuO: "\<And>i. ysu i \<in> \<Omega>\<^sub>u" and yswO: "\<And>i. ysw i \<in> \<Omega>\<^sub>w"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and p0: "psd (Y0 - X0)"
    and optu: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i)
        = \<theta> * u (ysu i) - (dist (xu i) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    and optw: "\<And>i. supconv (- w) \<epsilon> (xw i)
        = (- w) (ysw i) - (dist (xw i) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    and jetu: "\<And>i. ((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i) - Pu i \<bullet> h
        - (h \<bullet> (X i *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "\<And>i. ((\<lambda>h. (supconv (- w) \<epsilon> (xw i + h) - supconv (- w) \<epsilon> (xw i)
        - (- Pw i) \<bullet> h - (h \<bullet> ((- Y i) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and pnz: "p \<noteq> 0"
  shows False
proof -
  have bndu: "F (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule subsol_shifted_bound_supconv
        [OF sub t(1) ysuO symX Bu e optu jetu that(1)])
  \<comment> \<open>The supersolution bound is over \<open>F\<^sup>*\<close>, and \<open>F\<^sup>* = F\<close> only away from
      \<open>0\<close>; the gradient FAMILY need not avoid \<open>0\<close>, but its LIMIT does, so it
      avoids \<open>0\<close> eventually.  Shifting every family past that index costs
      nothing --- all hypotheses are either indexwise or convergences.\<close>
  have np: "0 < norm p" using pnz by simp
  obtain N where N: "\<And>i. N \<le> i \<Longrightarrow> norm p / 2 < norm (Pw i)"
  proof -
    have cn: "(\<lambda>i. norm (Pw i)) \<longlonglongrightarrow> norm p"
      by (rule tendsto_norm[OF cPw])
    have "norm p / 2 < norm p" using np by simp
    then have "\<forall>\<^sub>F i in sequentially. norm p / 2 < norm (Pw i)"
      using cn by (rule order_tendstoD(1)[rotated])
    then obtain N0 where N0: "\<forall>n\<ge>N0. norm p / 2 < norm (Pw n)"
      unfolding eventually_sequentially by blast
    show thesis by (rule that[of N0]) (use N0 in blast)
  qed
  have pwnz: "Pw (i + N) \<noteq> 0" for i
  proof -
    have "norm p / 2 < norm (Pw (i + N))" by (rule N) simp
    then show ?thesis using np by auto
  qed
  have bndw: "1 \<le> F (Pw (i + N)) (Y (i + N) - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule supersol_shifted_bound_supconv_ne
        [OF sup yswO symY Bw e optw jetw that(1) pwnz])
  have bndu': "F (Pu (i + N)) (X (i + N) + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule bndu[OF that(1) that(2)])
  show False
    by (rule env_strict_contradiction_of_shifted_limits
        [OF LIMSEQ_ignore_initial_segment[OF cX]
           LIMSEQ_ignore_initial_segment[OF cY]
           LIMSEQ_ignore_initial_segment[OF cPu]
           LIMSEQ_ignore_initial_segment[OF cPw]
           symX symY p0
           pnz t(2)
           zero_less_one bndu' bndw])
qed

end

subsection \<open>The sup-convolution is attained\<close>

text \<open>\<open>comparison_supconv_sequence_complete\<close> takes attainment of each
  sup-convolution as a hypothesis - the points \<open>y\<^sub>s\<close> where
  \<open>supconv u \<epsilon> x = u y\<^sub>s - dist(x,y\<^sub>s)\<^sup>2/(2\<epsilon>)\<close>.  For usc \<open>u\<close> bounded above
  they exist by @{thm [source] supconv_attained_usc}, and every one of them
  lies within \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))\<close> of \<open>x\<close>
  (@{thm [source] supconv_attain_radius}).\<close>

lemma supconv_attained_usc_ball:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  obtains ys where "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    and "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc[OF B e uscu] by blast
  have "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))"
    by (rule supconv_attain_radius[OF B e v])
  then show ?thesis by (intro that[OF _ v]) linarith
qed

text \<open>The \<open>+1\<close> margin is not needed: any radius \<open>R\<close> exceeding
  \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))\<close> serves. With the margin,
  \<open>cball x R \<subseteq> \<Omega>\<close> would ask \<open>\<Omega>\<close> for a ball of radius one, which no
  bounded \<open>\<Omega>\<close> of small diameter has; with \<open>R\<close> free, the hypothesis
  separates into a geometric condition on \<open>R\<close> and a smallness condition
  on \<open>\<epsilon>\<close>, discharged separately at the top level.\<close>

lemma supconv_attained_usc_ball_rad:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
  shows "\<exists>ys. dist x ys \<le> R
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc[OF B e uscu] by blast
  have "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))"
    by (rule supconv_attain_radius[OF B e v])
  then have "dist x ys \<le> R" using R by linarith
  with v show ?thesis by blast
qed

corollary supconv_attained_usc_in_rad:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and sub: "cball x R \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball_rad[OF B e uscu R] by blast
  have "ys \<in> cball x R" using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

corollary supconv_attained_usc_family:
  fixes u :: "real^'n::finite \<Rightarrow> real" and xs :: "nat \<Rightarrow> real^'n"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  shows "\<exists>ys. \<forall>i. supconv u \<epsilon> (xs i)
      = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF B e uscu] by blast
  then show ?thesis by (rule choice)
qed

subsection \<open>The sup-convolution converges to its function uniformly on compacts\<close>

text \<open>For bounded continuous \<open>u\<close>: above \<open>u\<close> always (@{thm [source] supconv_ge}),
  and within \<open>\<sigma>\<close> of it once the penalty beats the range of \<open>u\<close> outside a
  ball on which a modulus of continuity of \<open>u\<close> on a neighbourhood of \<open>K\<close>
  keeps \<open>u\<close> below \<open>u x + \<sigma>\<close> (@{thm [source] supconv_le_of_local_bound_usc}).\<close>

lemma supconv_uniform_upper:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K"
    and B: "\<And>y. u y \<le> Bu" and lo: "\<And>y. Bl \<le> u y"
    and cu: "continuous_on UNIV u"
  shows "uniform_limit K (\<lambda>\<epsilon>. supconv u \<epsilon>) u (at_right 0)"
  unfolding uniform_limit_iff
proof (intro allI impI)
  fix \<sigma> :: real assume s: "0 < \<sigma>"
  obtain R where R: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> R"
    using compact_imp_bounded[OF cK] bounded_iff by blast
  have "uniformly_continuous_on (cball 0 (R + 1)) u"
    by (rule compact_uniformly_continuous[OF continuous_on_subset[OF cu subset_UNIV] compact_cball])
  then obtain d where d: "0 < d" and ucu: "\<And>x y. x \<in> cball 0 (R + 1) \<Longrightarrow> y \<in> cball 0 (R + 1)
      \<Longrightarrow> dist y x < d \<Longrightarrow> dist (u y) (u x) < \<sigma>/2"
    unfolding uniformly_continuous_on_def using half_gt_zero[OF s] by metis
  define h where "h = min (d/2) 1"
  have h: "0 < h" "h < d" "h \<le> 1" unfolding h_def using d by auto
  have "((\<lambda>\<epsilon>::real. 2*\<epsilon>*(Bu - Bl)) \<longlongrightarrow> 2*0*(Bu - Bl)) (at_right 0)"
    by (intro tendsto_intros)
  then have small: "\<forall>\<^sub>F \<epsilon> in at_right 0. 2*\<epsilon>*(Bu - Bl) < h\<^sup>2"
    by (rule order_tendstoD(2)) (use h(1) in simp)
  show "\<forall>\<^sub>F \<epsilon> in at_right 0. \<forall>x\<in>K. dist (supconv u \<epsilon> x) (u x) < \<sigma>"
  proof (rule eventually_mono[OF eventually_conj[OF small eventually_at_right_less]], intro ballI)
    fix \<epsilon> x assume e: "2*\<epsilon>*(Bu - Bl) < h\<^sup>2 \<and> 0 < \<epsilon>" and x: "x \<in> K"
    have xC: "x \<in> cball 0 (R + 1)" using R[OF x] by simp
    have loc: "u y \<le> u x + \<sigma>/2" if y: "dist x y \<le> h" for y
    proof -
      have "norm y \<le> norm x + dist x y" using dist_triangle[of 0 y x] by simp
      then have yC: "y \<in> cball 0 (R + 1)" unfolding mem_cball_0 using R[OF x] y h(3) by linarith
      have "dist y x < d" using y h(2) dist_commute[of x y] by linarith
      then show ?thesis using ucu[OF xC yC] unfolding dist_real_def abs_less_iff by linarith
    qed
    have "2*\<epsilon>*(Bu - (u x + \<sigma>/2)) \<le> 2*\<epsilon>*(Bu - Bl)"
      using lo[of x] s e by (intro mult_left_mono) auto
    then have gap: "2*\<epsilon>*(Bu - (u x + \<sigma>/2)) < h\<^sup>2" using e by linarith
    have up: "supconv u \<epsilon> x \<le> u x + \<sigma>/2"
      by (rule supconv_le_of_local_bound_usc[OF B _ _ gap loc]) (use e h in auto)
    have "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B conjunct2[OF e]])
    then show "dist (supconv u \<epsilon> x) (u x) < \<sigma>"
      unfolding dist_real_def abs_less_iff using up s by (intro conjI) linarith+
  qed
qed

subsection \<open>The contradiction from bounded jets\<close>

text \<open>The hypotheses as the doubling produces them, with no convergence
  assumed: the Hessians \<open>X\<^sub>i\<close>, \<open>Y\<^sub>i\<close> bounded, \<open>Y\<^sub>i - X\<^sub>i\<close> positive
  semidefinite up to \<open>c\<^sub>i I\<close> with \<open>c\<^sub>i \<longlonglongrightarrow> 0\<close>, and both gradients
  approaching a bounded sequence \<open>G\<^sub>i\<close> with \<open>c \<le> norm G\<^sub>i\<close>.  A
  subsequence along which everything converges has a nonzero limit
  gradient, and \<open>comparison_supconv_sequence_complete\<close>
  applies to it.\<close>

context geometric_operator
begin

theorem comparison_supconv_bounded_family:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "nat \<Rightarrow> real^'n^'n" and Pu Pw G :: "nat \<Rightarrow> real^'n"
    and xu xw ysu ysw :: "nat \<Rightarrow> real^'n"
  assumes sub: "subsol \<Omega>\<^sub>u u" and sup: "supersol_usc \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and e: "0 < \<epsilon>"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and ysuO: "\<And>i. ysu i \<in> \<Omega>\<^sub>u" and yswO: "\<And>i. ysw i \<in> \<Omega>\<^sub>w"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and psdi: "\<And>i. psd (Y i - X i + (cs i) *\<^sub>R mat 1)"
    and cs0: "cs \<longlonglongrightarrow> 0"
    and optu: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i)
        = \<theta> * u (ysu i) - (dist (xu i) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    and optw: "\<And>i. supconv (- w) \<epsilon> (xw i)
        = (- w) (ysw i) - (dist (xw i) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    and jetu: "\<And>i. ((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i) - Pu i \<bullet> h
        - (h \<bullet> (X i *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "\<And>i. ((\<lambda>h. (supconv (- w) \<epsilon> (xw i + h) - supconv (- w) \<epsilon> (xw i)
        - (- Pw i) \<bullet> h - (h \<bullet> ((- Y i) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and bX: "\<And>i. norm (X i) \<le> BX" and bY: "\<And>i. norm (Y i) \<le> BY"
    and bG: "\<And>i. norm (G i) \<le> BG"
    and au: "(\<lambda>i. Pu i - G i) \<longlonglongrightarrow> 0"
    and aw: "(\<lambda>i. Pw i - G i) \<longlonglongrightarrow> 0"
    and glb: "\<And>i. c \<le> norm (G i)" and cpos: "0 < c"
  shows False
proof -
  obtain g X0 Y0 rr where sm: "strict_mono rr"
    and cG: "(\<lambda>i. G (rr i)) \<longlonglongrightarrow> g"
    and cX: "(\<lambda>i. X (rr i)) \<longlonglongrightarrow> X0"
    and cY: "(\<lambda>i. Y (rr i)) \<longlonglongrightarrow> Y0"
    using bounded_seq_limit_point_triple
      [where A = G and B = X and C = Y and Ba = BG and Bb = BX and Bc = BY,
       OF bG bX bY]
    by blast
  have aur: "(\<lambda>i. Pu (rr i) - G (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF au sm] by (simp add: o_def)
  have awr: "(\<lambda>i. Pw (rr i) - G (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF aw sm] by (simp add: o_def)
  have cPu: "(\<lambda>i. Pu (rr i)) \<longlonglongrightarrow> g"
    using tendsto_add[OF aur cG] by simp
  have cPw: "(\<lambda>i. Pw (rr i)) \<longlonglongrightarrow> g"
    using tendsto_add[OF awr cG] by simp  have cnorm: "(\<lambda>i. norm (G (rr i))) \<longlonglongrightarrow> norm g"
    by (rule tendsto_norm[OF cG])
  have cg: "c \<le> norm g"
  proof (rule tendsto_lowerbound[OF cnorm])
    show "\<forall>\<^sub>F i in sequentially. c \<le> norm (G (rr i))"
      using glb by simp
  qed simp
  have pnz: "g \<noteq> 0"
    using cg cpos by auto
  have ysuOr: "ysu (rr i) \<in> \<Omega>\<^sub>u" for i by (rule ysuO)
  have yswOr: "ysw (rr i) \<in> \<Omega>\<^sub>w" for i by (rule yswO)
  have symXr: "transpose (X (rr i)) = X (rr i)" for i by (rule symX)
  have symYr: "transpose (Y (rr i)) = Y (rr i)" for i by (rule symY)
  have psdir: "psd (Y (rr i) - X (rr i) + (cs (rr i)) *\<^sub>R mat 1)" for i
    by (rule psdi)
  have csr: "(\<lambda>i. cs (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF cs0 sm] by (simp add: o_def)
  have p0: "psd (Y0 - X0)"
    by (rule psd_diff_limit_shifted[OF cX cY csr psdir])
  have optur: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i))
      = \<theta> * u (ysu (rr i)) - (dist (xu (rr i)) (ysu (rr i)))\<^sup>2 / (2*\<epsilon>)" for i
    by (rule optu)
  have optwr: "supconv (- w) \<epsilon> (xw (rr i))
      = (- w) (ysw (rr i)) - (dist (xw (rr i)) (ysw (rr i)))\<^sup>2 / (2*\<epsilon>)" for i
    by (rule optw)
  have jetur: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i) + h)
      - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i)) - Pu (rr i) \<bullet> h
      - (h \<bullet> (X (rr i) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    by (rule jetu)
  have jetwr: "((\<lambda>h. (supconv (- w) \<epsilon> (xw (rr i) + h)
      - supconv (- w) \<epsilon> (xw (rr i))
      - (- Pw (rr i)) \<bullet> h - (h \<bullet> ((- Y (rr i)) *v h))/2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)" for i
    by (rule jetw)
  show False
    by (rule comparison_supconv_sequence_complete
        [OF sub sup t(1) t(2) e Bu Bw ysuOr yswOr
           symXr symYr p0 optur optwr jetur jetwr cX cY cPu cPw pnz])
qed

end

(*<*)
end
(*>*)
