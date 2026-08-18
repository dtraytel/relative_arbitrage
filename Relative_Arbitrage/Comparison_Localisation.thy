section \<open>Penalties, sup-convolutions and the localised maximiser\<close>

(*<*)
theory Comparison_Localisation
  imports Comparison_Strictness
begin

(*>*)


text \<open>The doubling machinery as this proof consumes it: the penalty's
  jet, the sup-convolution chain that removes the jet correction, Jensen's
  tilt, the attainment of the sup-convolution, and the parameter threading
  that puts the doubled maximiser away from the boundary.\<close>

subsection \<open>The quartic penalty and its exact second-order expansion\<close>

text \<open>\<open>quartic_pen\<close> lives in @{theory Second_Order_Viscosity_Analysis.Soft_Penalty}.\<close>

text \<open>The jet itself, in the shape the slice lemmas consume: gradient
  \<open>\<beta>(d \<bullet> d) d\<close>, quadratic form \<open>h \<mapsto> \<beta>(d \<bullet> d)(h \<bullet> h) + 2\<beta>(d \<bullet> h)\<^sup>2\<close>.
  Exact, holding at every \<open>d\<close> with no smallness hypothesis.\<close>

text \<open>At \<open>d = 0\<close> both gradient and quadratic form vanish, so the quartic
  penalty has second-order jet \<open>(0, 0)\<close> there; feeding this to
  \<open>supersol_no_vanishing_jet\<close> gives the paper's \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.\<close>

subsection \<open>The doubled penalty's jet, for an arbitrary penalty\<close>

text \<open>Below \<open>sums_matrix_inequality\<close> the \<open>psd\<close> chain is abstract in the two
  block maps; \<open>sums_matrix_inequality\<close> itself uses an exact identity for
  the quadratic penalty, which for general \<open>P\<close> is only asymptotic, and this
  lemma supplies it. Writing \<open>e k = fst k - snd k\<close>, the doubled penalty
  \<open>z \<mapsto> P (fst z - snd z)\<close> has gradient \<open>(G, -G)\<close> and Hessian
  \<open>k \<mapsto> (Z (e k), -Z (e k))\<close> at \<open>z'\<close>, with numerator collapsing to
  \<open>R (e k)\<close>. Although \<open>e\<close> is not injective near \<open>0\<close>, the limit survives
  because \<open>e\<close> is 2-Lipschitz and kills only the diagonal, where \<open>R 0 = 0\<close>.\<close>

text \<open>\<open>matrix_vector_mult_diff_gen\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

text \<open>\<open>doubled_penalty_jet\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Semiconvexity of the doubled functional, for a general penalty\<close>

text \<open>\<open>convex_on_prod_diff\<close>, \<open>convex_on_proj_sum\<close>, \<open>semiconvex_penalty_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>A concrete penalty: semiconcave, with a vanishing 2-jet at the origin\<close>

text \<open>\<open>soft_pen\<close> lives in @{theory Second_Order_Viscosity_Analysis.Soft_Penalty}.\<close>

text \<open>\<open>convex_on_norm_lift\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>























theorem supersol_no_vanishing_jet_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh) / (norm hh)\<^sup>2 < c"
  shows False
proof -
  obtain \<delta> :: real where d0: "0 < \<delta>"
    and ltone: "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
  proof (rule ell_op_usc_small_shift_lt_one[OF k(1) k(2) L])
    fix dd :: real
    assume a1: "0 < dd" and a2: "dd < 1"
      and a3: "\<And>q :: real^'n.
        ell_op_usc k L q ((0::real^'n^'n) - dd *\<^sub>R mat 1) < 1"
    show thesis by (rule that[OF a1 a3])
  qed
  have Ys: "transpose (0::real^'n^'n) = 0"
    by (simp add: transpose_def vec_eq_iff)
  have ub0: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
      ((- w) (yh + hh) - (- w) yh - (- (0::real^'n)) \<bullet> hh
        - (hh \<bullet> ((- (0::real^'n^'n)) *v hh))/2) / (norm hh)\<^sup>2 < c"
    using ub by simp
  have one: "1 \<le> ell_op_usc k L (0::real^'n)
      ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_onesided[OF sup yh Ys ub0 d0])
  show False using one ltone[of "0::real^'n"] by simp

qed

theorem supersol_no_vanishing_jet:
  fixes w :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  obtain \<delta> :: real where d0: "0 < \<delta>"
    and ltone: "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
  proof (rule ell_op_usc_small_shift_lt_one[OF k(1) k(2) L])
    fix dd :: real
    assume a1: "0 < dd" and a2: "dd < 1"
      and a3: "\<And>q :: real^'n.
        ell_op_usc k L q ((0::real^'n^'n) - dd *\<^sub>R mat 1) < 1"
    show thesis by (rule that[OF a1 a3])
  qed
  have Ys: "transpose (0::real^'n^'n) = 0"
    by (simp add: transpose_def vec_eq_iff)
  have jet0: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- (0::real^'n)) \<bullet> h
      - (h \<bullet> ((- (0::real^'n^'n)) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using jet by simp
  have one: "1 \<le> ell_op_usc k L (0::real^'n)
      ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound[OF sup yh Ys jet0 d0])
  show False using one ltone[of "0::real^'n"] by simp

qed

subsection \<open>Theorem 4.2(a): the closing chain from jets\<close>

text \<open>Theorem 4.2(a) from second-order jets for \<open>\<theta> u\<close> at \<open>xh\<close> and for
  \<open>-w\<close> at \<open>yh\<close> with a common gradient \<open>p\<close>, the ordering
  \<open>psd (Ym - Xm)\<close>, symmetry of both matrices, and the off-diagonal
  condition \<open>p \<noteq> 0\<close>. The shift correction \<open>\<delta>\<close> used to reach genuine
  local extrema is removed by the lower and upper envelopes and does not
  appear in the statement.\<close>

theorem comparison_env_from_jets:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Xm Ym :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xh: "xh \<in> \<Omega>" and yh: "yh \<in> \<Omega>"
    and Xs: "transpose Xm = Xm" and Ys: "transpose Ym = Ym"
    and psd: "psd (Ym - Xm)"
    and p: "p \<noteq> 0"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jetu: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have subs: "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule subsol_shifted_bound[OF sub t(1) xh Xs k(1) k(2) L jetu that(1)])
  have sups: "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule supersol_shifted_bound_ne[OF sup yh k(1) k(2) L Ys jetw
          that(1) p])
  show False
    by (rule env_strict_contradiction_of_shifts[OF psd Xs Ys p k(1) k(2) L
          zero_less_one t(2) subs sups])
qed

text \<open>The same conclusion with the off-diagonal condition \<open>p \<noteq> 0\<close>
  replaced, via \<open>doubling_grad_nonzero\<close>, by the statement that \<open>xh\<close>
  fails to maximise \<open>u - w\<close> over \<open>K\<close>.\<close>

subsection \<open>Wiring the theorem on sums to the ordering hypothesis\<close>

text \<open>\<open>sums_gives_ordering\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>With linearity and symmetry of the two blocks, supplied by the
  Alexandrov jet's bounded linear and symmetric Hessian, the ordering
  becomes the \<open>psd\<close> hypothesis \<open>comparison_env_from_jets\<close> wants.\<close>

subsection \<open>Discharging the negativity hypothesis at the doubled maximum\<close>

text \<open>\<open>sums_ordering_at_interior_max\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The same conclusion in \<open>psd\<close> form, consumed by
  \<open>comparison_env_from_jets\<close>, depending only on the maximum property of
  the doubled functional, its Alexandrov jet, and the linearity and
  symmetry of the two diagonal blocks.\<close>










theorem comparison_env_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and a b :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xhO: "xh \<in> \<Omega>" and yhO: "yh \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and blW: "bounded_linear W"
    and symW: "\<And>z z'. z \<bullet> W z' = z' \<bullet> W z"
    and dpos: "0 < dd"
    and mx: "\<And>hk. norm hk < dd \<Longrightarrow>
        a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and nz: "\<alpha> *\<^sub>R (xh - yh) \<noteq> 0"
    and jetu: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh
        - (\<alpha> *\<^sub>R (xh - yh)) \<bullet> h
        - (h \<bullet> (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. ((- w) (yh + h) - (- w) yh
        - (- (\<alpha> *\<^sub>R (xh - yh))) \<bullet> h
        - (h \<bullet> ((- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have symX: "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    by (rule block_matrices_from_jet(1)[OF blW symW dpos mx expPsi])
  have symY: "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule block_matrices_from_jet(2)[OF blW symW dpos mx expPsi])
  have psdXY: "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
    by (rule block_matrices_from_jet(3)[OF blW symW dpos mx expPsi])
  show False
    by (rule comparison_env_from_jets[OF sub sup t(1) t(2) xhO yhO symX symY
          psdXY nz kk(1) kk(2) LL jetu jetw])
qed

text \<open>The same, with the off-diagonal condition traded for the statement
  that \<open>x'\<close> fails to maximise \<open>u - w\<close> over \<open>K\<close>; by the gradient
  alignment this is the same condition as \<open>p \<noteq> 0\<close>.\<close>

subsection \<open>Deriving the component jets from the doubled jet\<close>

text \<open>\<open>penalty_difference_identity\<close>, \<open>filterlim_slice_fst\<close>, \<open>filterlim_slice_snd\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The norm of a slice vector is the norm of its nonzero component,
  which keeps the quotient in the jet transfer unchanged.\<close>

text \<open>\<open>doubled_slice_numerator_fst\<close>, \<open>doubled_jet_slice_fst\<close>, \<open>doubled_jet_slice_fst_gen\<close>, \<open>penalty_difference_identity_snd\<close>, \<open>doubled_slice_numerator_snd\<close>, \<open>doubled_jet_slice_snd\<close>, \<open>doubled_jet_slice_snd_gen\<close>, \<open>doubled_jet_slices_at_max\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Matching the block Hessians against their matrices\<close>

text \<open>The slice jets carry their Hessians as functions
  \<open>h \<mapsto> fst (W (h,0)) + \<alpha> h\<close> and \<open>h \<mapsto> snd (W (0,h)) + \<alpha> h\<close>, while the
  viscosity machinery wants matrices. \<open>matrix_works\<close> bridges them, but
  is stated for \<open>Vector_Spaces.linear\<close>, so real-vector-space \<open>linear\<close>
  must be routed through \<open>linear_matrix_vector_mul_eq\<close> first.\<close>

text \<open>\<open>block_fst_matrix_apply\<close>, \<open>block_snd_matrix_apply\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Theorem 4.2(a) from the doubled jet alone\<close>

text \<open>The component jets are no longer hypotheses: they are produced from
  the doubled jet by \<open>doubled_jet_slices_at_max\<close> and matched to their
  matrices by the lemmas above. What remains assumed is the doubled data
  itself -- an interior maximum of
  \<open>\<theta> u(x) - w(y) - (\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> at \<open>z' = (x', y')\<close> with its
  Alexandrov jet -- plus the two viscosity properties and the
  off-diagonal condition.\<close>

subsection \<open>The subsolution bound straight from a sup-convolution jet\<close>

text \<open>The comparison argument's doubled functional is built from the
  sup-convolutions of \<open>u\<close> and \<open>w\<close>, since those are what is semiconvex
  and what Jensen's lemma applies to; the jet produced at the doubled
  maximum is thus a jet of \<open>supconv (\<theta> u) \<epsilon>\<close>, not of \<open>\<theta> u\<close>. This
  theorem closes that gap: the \<open>\<delta>\<close>-corrected quadratic bound for the
  sup-convolution at \<open>x\<close> transfers, by \<open>supconv_local_max_transfer_ball\<close>,
  to the same bound for \<open>\<theta> u\<close> at the attaining point \<open>y\<^sub>s\<close> -- same
  \<open>p\<close>, same matrix -- where the viscosity property applies, with
  \<open>y\<^sub>s\<close> now the point that must lie in \<open>\<Omega>\<close>.\<close>

theorem subsol_shifted_bound_supconv:
  fixes u :: "real^'n::finite \<Rightarrow> real" and Xm :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and ysO: "ys \<in> \<Omega>"
    and Xs: "transpose Xm = Xm"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
        = \<theta> * u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
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
  have ne: "feasible k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding g by (rule feasible_nonempty[OF kk(1) kk(2) LL])
  have "ell_op k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    by (rule visc_subsol_scaled_uniform[OF sub t ysO tf ne maxloc])
  thus ?thesis unfolding g .
qed

text \<open>\<open>neg_shift_matrix_apply\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


theorem supersol_shifted_bound_supconv:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and ysO: "ys \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
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
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup ysO tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

corollary supersol_shifted_bound_supconv_ne:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w" and ysO: "ys \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>" and p0: "p \<noteq> 0"
  shows "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_supconv[OF sup ysO Ys Bw e opt jet d])
  then show ?thesis
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL p0] by simp
qed

subsection \<open>Theorem 4.2(a) from sup-convolution jets\<close>

text \<open>The closing chain in the form the comparison argument reaches: both
  bounds come from jets of the sup-convolutions, which the doubled
  functional carries, and the two attaining points \<open>y\<^sub>s\<^sup>u\<close> and
  \<open>y\<^sub>s\<^sup>w\<close> are where the viscosity properties are applied. The uniform
  bound \<open>\<theta> < 1\<close> on the subsolution side survives the \<open>\<delta> \<rightarrow> 0\<close>
  limit and yields the strict envelope inequality; the off-diagonal
  condition \<open>p \<noteq> 0\<close> identifies the two envelopes with \<open>F\<close> itself. No
  \<open>\<delta>\<close> appears in the conclusion.\<close>

theorem comparison_supconv_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Xm Ym :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and ysuO: "ysu \<in> \<Omega>" and yswO: "ysw \<in> \<Omega>"
    and Xs: "transpose Xm = Xm" and Ys: "transpose Ym = Ym"
    and psd: "psd (Ym - Xm)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
    and optu: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> xu
        = \<theta> * u ysu - (dist xu ysu)\<^sup>2 / (2*\<epsilon>)"
    and optw: "supconv (- w) \<epsilon> xw = (- w) ysw - (dist xw ysw)\<^sup>2 / (2*\<epsilon>)"
    and jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> xu - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (xw + h) - supconv (- w) \<epsilon> xw
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have subs: "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule subsol_shifted_bound_supconv[OF sub t(1) ysuO Xs kk(1) kk(2) LL
          Bu e optu jetu that(1)])
  have sups: "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule supersol_shifted_bound_supconv_ne[OF sup yswO kk(1) kk(2) LL
          Ys Bw e optw jetw that(1) pnz])
  show False
    by (rule env_strict_contradiction_of_shifts[OF psd Xs Ys pnz kk(1) kk(2) LL
          zero_less_one t(2) subs sups])
qed

subsection \<open>Theorem 4.2(a) from the doubled sup-convolution jet alone\<close>

text \<open>The full composition: the two component jets are no longer
  hypotheses but the two coordinate slices of the doubled jet, produced
  by \<open>doubled_jet_slices_at_max\<close> with \<open>a\<close> and \<open>b\<close> instantiated at the
  two sup-convolutions, and matched to their matrices by the block
  lemmas; the three matrix hypotheses come from
  \<open>block_matrices_from_jet\<close>. What remains assumed is the two viscosity
  properties, the scaling parameter \<open>\<theta>\<close>, an interior maximum of the
  doubled sup-convolution functional with its Alexandrov jet, the
  off-diagonal condition, and that each sup-convolution is attained at a
  point of \<open>\<Omega>\<close>.\<close>

subsection \<open>Absorbing Jensen's tilt: the general nearby-point form\<close>

text \<open>The tilt perturbs the gradient as well as the matrix, unlike the
  earlier shift theorems, which move only the matrix by \<open>\<delta> I\<close>; Jensen's
  tilt moves the gradient by an amount \<open>\<le> dd\<close> that is at our disposal
  but not zero. The right statement is the general one: a bound holding
  at points arbitrarily close to \<open>(p, M)\<close>, however produced, passes to
  the lower envelope -- exactly the content of \<open>F\<^sub>*\<close>, subsuming both
  the \<open>\<delta> I\<close> shifts and the tilt, with the nearby point allowed to
  depend on the radius so that \<open>dd\<close> can be chosen after it.\<close>

theorem ell_op_lsc_le_of_nearby:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
      dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e
      \<and> ell_op k L p' M' \<le> c"
  shows "ell_op_lsc k L p M \<le> ereal c"
  unfolding ell_op_lsc_def
proof (rule SUP_least)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  obtain p' M' where d: "dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e"
    and bd: "ell_op k L p' M' \<le> c"
    using b[OF e0] by blast
  have mem: "((p', M') :: (real^'n) \<times> (real^'n^'n)) \<in> ball (p, M) e"
    using d by (simp add: dist_commute)
  have "(INF v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)
      \<le> ell_op_pair k L (p', M')"
    by (rule INF_lower[OF mem])
  also have "\<dots> \<le> ereal c"
    using bd by (simp add: ell_op_pair_def)
  finally show "(INF v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)
      \<le> ereal c" .
qed

theorem ell_op_usc_ge_of_nearby:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
      dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e
      \<and> c \<le> ell_op k L p' M'"
  shows "ereal c \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  obtain p' M' where d: "dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e"
    and bd: "c \<le> ell_op k L p' M'"
    using b[OF e0] by blast
  have mem: "((p', M') :: (real^'n) \<times> (real^'n^'n)) \<in> ball (p, M) e"
    using d by (simp add: dist_commute)
  have "ereal c \<le> ell_op_pair k L (p', M')"
    using bd by (simp add: ell_op_pair_def)
  also have "\<dots> \<le> (SUP v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)"
    by (rule SUP_upper[OF mem])
  finally show "ereal c
      \<le> (SUP v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)" .
qed

text \<open>The closing contradiction in that generality: compare
  \<open>env_strict_contradiction_of_shifts\<close>, whose hypotheses no longer name
  the \<open>\<delta> I\<close> shifts, only that suitable bounds hold arbitrarily near
  \<open>(p, X)\<close> and \<open>(p, Y)\<close> -- the form the tilt-absorption argument needs,
  since there the nearby points are produced by re-running Jensen with a
  smaller \<open>dd\<close> rather than by a fixed algebraic shift.\<close>

theorem env_strict_contradiction_of_nearby:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and pnz: "p \<noteq> 0" and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1"
    and subs: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X) < e
        \<and> ell_op k L p' M' \<le> c"
    and sups: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y) < e
        \<and> 1 \<le> ell_op k L p' M'"
  shows False
proof -
  have lsc: "ell_op_lsc k L p X \<le> ereal c"
    by (rule ell_op_lsc_le_of_nearby[OF subs])
  have c1e: "ereal c < 1"
    using c1 by (simp add: one_ereal_def)
  have sub: "ell_op_lsc k L p X < 1"
    using lsc c1e by (rule le_less_trans)
  have sup: "1 \<le> ell_op_usc k L p Y"
    using ell_op_usc_ge_of_nearby[OF sups] by (simp add: one_ereal_def)
  show False
    by (rule ell_op_env_strict_contradiction[OF psd symX symY pnz kk(1) kk(2)
          LL sub sup])
qed

subsection \<open>The quantitative input the tilt argument needs\<close>

text \<open>The nearby-point hypothesis is discharged once the perturbed data
  approaches \<open>(p, M)\<close> at a controlled rate in the tilt parameter; this
  lemma isolates and discharges exactly that, reducing the remaining
  work to one estimate: the maximiser and its jet move at most linearly
  in \<open>dd\<close>. No convergence of the jets themselves is needed, only
  \<open>dist ((P dd, Mf dd)) (p, M) \<le> \<kappa> dd\<close> for arbitrary \<open>\<kappa>\<close>, since the
  radius is chosen after it.\<close>

text \<open>Theorem 4.2(a) reduces to one quantitative hypothesis per side: the
  perturbed gradient/matrix pair at tilt \<open>dd\<close> lies within \<open>\<kappa> dd\<close> of the
  limiting pair; the envelopes, strictness, ordering and off-diagonal
  condition are already established.\<close>

subsection \<open>A tilt that needs no limit at all\<close>

text \<open>\<open>gradient_is_minus_tilt\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>If the tilt is antisymmetric, \<open>p = (p\<^sub>0,-p\<^sub>0)\<close>, the two block gradients
  are exact negatives of each other, giving the alignment
  \<open>comparison_supconv_complete\<close> needs with no limit and no rate estimate on
  the tilt.  This route needs Jensen's lemma to deliver such an
  antisymmetric tilt.\<close>

subsection \<open>The Hessians at the doubled maximum are two-sidedly bounded\<close>

text \<open>Route (i) needs the perturbed Hessians bounded as the tilt shrinks.
  \<open>convex_alexandrov\<close> (@{theory Second_Order_Viscosity_Analysis.Alexandrov}) supplies a Hessian \<open>B\<close> with
  \<open>0 \<le> k \<bullet> Bk\<close>; combined with \<open>k \<bullet> Wk \<le> 0\<close> from
  \<open>second_order_interior_max\<close>, this pins the Hessian \<open>W = B - cI\<close> at a
  maximum of a semiconvex function between \<open>-c\<close> and \<open>0\<close>.
  \<open>semiconvex_alexandrov_bounded\<close> carries this two-sided bound, and
  \<open>norm_matrix_le_of_form_bound\<close> turns it into a matrix-norm bound.\<close>






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

subsection \<open>Symmetry and the ordering pass to the limit\<close>subsection \<open>Symmetry and the ordering pass to the limit\<close>

text \<open>\<open>tendsto_entry\<close>, \<open>transpose_limit\<close>, \<open>tendsto_quadratic_form\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>





theorem env_strict_contradiction_of_limits:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and psdi: "\<And>i. psd (Y i - X i)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1"
    and bndu: "\<And>i. ell_op k L (Pu i) (X i) \<le> c"
    and bndw: "\<And>i. 1 \<le> ell_op k L (Pw i) (Y i)"
  shows False
proof -
  have sX0: "transpose X0 = X0"
    by (rule transpose_limit[OF cX symX])
  have sY0: "transpose Y0 = Y0"
    by (rule transpose_limit[OF cY symY])
  have p0: "psd (Y0 - X0)"
    by (rule psd_diff_limit[OF cX cY psdi])
  have subs: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X0) < e
      \<and> ell_op k L p' M' \<le> c" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pu i, X i)) \<longlonglongrightarrow> ((p, X0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPu cX])
    have P: "ell_op k L (fst ((Pu i, X i) :: (real^'n) \<times> (real^'n^'n)))
        (snd ((Pu i, X i) :: (real^'n) \<times> (real^'n^'n))) \<le> c" for i
      using bndu[of i] by simp
    obtain z where dz: "dist z ((p, X0) :: (real^'n) \<times> (real^'n^'n)) < e"
      and pz: "ell_op k L (fst z) (snd z) \<le> c"
      using nearby_of_convergent
        [where P = "\<lambda>z. ell_op k L (fst z) (snd z) \<le> c", OF cZ P e0]
      by blast
    have zc: "(fst z, snd z) = z" by simp
    from dz pz show ?thesis
      by (intro exI[of _ "fst z"] exI[of _ "snd z"]) (simp add: zc)
  qed
  have sups: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y0) < e
      \<and> 1 \<le> ell_op k L p' M'" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pw i, Y i)) \<longlonglongrightarrow> ((p, Y0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPw cY])
    have P: "1 \<le> ell_op k L (fst ((Pw i, Y i) :: (real^'n) \<times> (real^'n^'n)))
        (snd ((Pw i, Y i) :: (real^'n) \<times> (real^'n^'n)))" for i
      using bndw[of i] by simp
    obtain z where dz: "dist z ((p, Y0) :: (real^'n) \<times> (real^'n^'n)) < e"
      and pz: "1 \<le> ell_op k L (fst z) (snd z)"
      using nearby_of_convergent
        [where P = "\<lambda>z. 1 \<le> ell_op k L (fst z) (snd z)", OF cZ P e0]
      by blast
    have zc: "(fst z, snd z) = z" by simp
    from dz pz show ?thesis
      by (intro exI[of _ "fst z"] exI[of _ "snd z"]) (simp add: zc)
  qed
  show False
    by (rule env_strict_contradiction_of_nearby[OF p0 sX0 sY0 pnz kk(1) kk(2)
          LL c1 subs sups])
qed

subsection \<open>The gradient alignment along the family\<close>

text \<open>\<open>tendsto_of_norm_bound\<close>, \<open>gradient_sequences_align\<close>, \<open>gradient_sequences_align_of_bound\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The diagonal step: two limits at once\<close>

text \<open>\<open>nearby_of_convergent_shifted\<close>, \<open>nearby_of_convergent_shifted_neg\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The contradiction with both limits taken together: bounds at the
  \<open>\<delta>\<close>-corrected matrices along a sequence of tilts is exactly what the
  doubling reaches.\<close>

theorem env_strict_contradiction_of_shifted_limits:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and p0: "psd (Y0 - X0)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1" and D: "0 < D"
    and bndu: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        ell_op k L (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> c"
    and bndw: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        1 \<le> ell_op k L (Pw i) (Y i - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have sX0: "transpose X0 = X0"
    by (rule transpose_limit[OF cX symX])
  have sY0: "transpose Y0 = Y0"
    by (rule transpose_limit[OF cY symY])
  note p0
  have subs: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X0) < e
      \<and> ell_op k L p' M' \<le> c" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pu i, X i)) \<longlonglongrightarrow> ((p, X0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPu cX])
    show ?thesis
      by (rule nearby_of_convergent_shifted
          [where Q = "\<lambda>p' M'. ell_op k L p' M' \<le> c", OF cZ bndu D e0])
  qed
  have sups: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y0) < e
      \<and> 1 \<le> ell_op k L p' M'" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pw i, Y i)) \<longlonglongrightarrow> ((p, Y0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPw cY])
    show ?thesis
      by (rule nearby_of_convergent_shifted_neg
          [where Q = "\<lambda>p' M'. 1 \<le> ell_op k L p' M'", OF cZ bndw D e0])
  qed
  show False
    by (rule env_strict_contradiction_of_nearby[OF p0 sX0 sY0 pnz kk(1) kk(2)
          LL c1 subs sups])
qed

subsection \<open>Theorem 4.2(a) from a sequence of sup-convolution jets\<close>

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
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
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
  have bndu: "ell_op k L (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule subsol_shifted_bound_supconv
        [OF sub t(1) ysuO symX kk(1) kk(2) LL Bu e optu jetu that(1)])
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
  have bndw: "1 \<le> ell_op k L (Pw (i + N)) (Y (i + N) - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule supersol_shifted_bound_supconv_ne
        [OF sup yswO kk(1) kk(2) LL symY Bw e optw jetw that(1) pwnz])
  have bndu': "ell_op k L (Pu (i + N)) (X (i + N) + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule bndu[OF that(1) that(2)])
  show False
    by (rule env_strict_contradiction_of_shifted_limits
        [OF LIMSEQ_ignore_initial_segment[OF cX]
           LIMSEQ_ignore_initial_segment[OF cY]
           LIMSEQ_ignore_initial_segment[OF cPu]
           LIMSEQ_ignore_initial_segment[OF cPw]
           symX symY p0
           pnz kk(1) kk(2) LL t(2)
           zero_less_one bndu' bndw])
qed

subsection \<open>The shrinking tilt is always available\<close>

text \<open>\<open>jensen_tilt_threshold_pos\<close>, \<open>jensen_tilt_small_enough\<close>, \<open>tilt_sequence_pos\<close>, \<open>tilt_sequence_lt\<close>, \<open>tilt_sequence_tendsto\<close>, \<open>tilt_sequence_admissible\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>Replacing the Lipschitz modulus by compactness\<close>

text \<open>\<open>positive_separation_of_value_gap\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>Two consequences: \<open>doubling_grad_lower_bound\<close> with the Lipschitz
  hypothesis replaced by an abstract separation, and the same for the
  shared gradient's norm - the separation plays exactly the role the
  Lipschitz constant did.\<close>

text \<open>For the doubling run on sup-convolutions, the separation is required of
  \<open>supconv(-w)\<epsilon>\<close> itself, supplied by \<open>positive_separation_of_value_gap\<close>
  from compactness of \<open>K\<close> and \<open>supconv_continuous\<close> alone - no Lipschitz
  constant enters.  The sign bookkeeping is as in
  \<open>doubling_grad_lower_bound_supconv\<close>, with \<open>w\<close> instantiated at \<open>-B\<close>.\<close>

text \<open>\<open>shifted_family_parameters\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The sup-convolution is attained\<close>

text \<open>\<open>comparison_supconv_sequence_complete\<close> takes attainment of each
  sup-convolution as a hypothesis - the points \<open>y\<^sub>s\<close> where
  \<open>supconv u \<epsilon> x = u y\<^sub>s - dist(x,y\<^sub>s)\<^sup>2/(2\<epsilon>)\<close>.  For continuous \<open>u\<close>
  bounded above they exist by coercivity: beyond an explicit radius
  \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))+1\<close> the penalty already beats the value at \<open>x\<close>,
  so the supremum over the whole space equals the supremum over one
  compact ball, attained by continuity.\<close>

theorem supconv_attained_ball:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
  shows "\<exists>ys. dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"proof -
  define M where "M = max 0 (2*\<epsilon>*(Bu - u x))"
  have M0: "0 \<le> M" unfolding M_def by simp
  have s0: "0 \<le> sqrt M" using M0 by simp
  define R where "R = sqrt M + 1"
  have R0: "0 < R" unfolding R_def using s0 by linarith
  have Rsq: "2*\<epsilon>*(Bu - u x) < R\<^sup>2"
  proof -
    have sq: "(sqrt M)\<^sup>2 = M" using M0 by simp
    have exp: "R\<^sup>2 = (sqrt M)\<^sup>2 + 2 * sqrt M + 1"
      unfolding R_def by (simp add: power2_eq_square algebra_simps)
    have "M \<le> R\<^sup>2"
      unfolding exp sq using s0 by linarith
    moreover have "2*\<epsilon>*(Bu - u x) \<le> M"
      unfolding M_def by simp
    moreover have "M < R\<^sup>2"
      unfolding exp sq using s0 by linarith
    ultimately show ?thesis by linarith
  qed
  have cpt: "compact (cball x R)" by (rule compact_cball)
  have ne: "cball x R \<noteq> {}" using R0 by auto
  have cont: "continuous_on (cball x R) (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
    by (intro continuous_intros continuous_on_subset[OF cu subset_UNIV])
       (use e in auto)
  obtain ys where ysin: "ys \<in> cball x R"
    and ysmax: "\<forall>y \<in> cball x R.
        u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using continuous_attains_sup[OF cpt ne cont] by blast
  have xin: "x \<in> cball x R" using R0 by simp
  have key: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    with ysmax show ?thesis by blast
  next
    case False
    then have gt: "R < dist x y" by simp
    have lt: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) < u x"
    proof -
      have "R\<^sup>2 < (dist x y)\<^sup>2"
        by (rule power_strict_mono[OF gt less_imp_le[OF R0]]) simp
      then have big: "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2"
        using Rsq by linarith
      have c0: "0 < 2*\<epsilon>" using e by simp
      have "(Bu - u x) * (2*\<epsilon>) < (dist x y)\<^sup>2"
        using big by (simp add: algebra_simps)
      then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using c0 by (simp add: pos_less_divide_eq)
      then show ?thesis using B[of y] by linarith
    qed
    have xval: "u x = u x - (dist x x)\<^sup>2 / (2*\<epsilon>)" by simp
    have "u x - (dist x x)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      using ysmax xin by blast
    with lt xval show ?thesis by linarith
  qed
  have "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  proof (rule antisym)
    show "supconv u \<epsilon> x \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      unfolding supconv_def by (rule cSUP_least) (auto simp: key)
    show "u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>) \<le> supconv u \<epsilon> x"
      unfolding supconv_def
      by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  qed
  moreover have "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    using ysin unfolding R_def M_def by (simp add: dist_commute)
  ultimately show ?thesis by blast
qed

corollary supconv_attained:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
  shows "\<exists>ys. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  using supconv_attained_ball[OF B e cu] by blast

text \<open>As a family: along any sequence of base points the attaining points can
  be chosen simultaneously by countable choice, with no uniformity in
  \<open>i\<close> needed.\<close>

text \<open>The attaining point lies in an explicit ball of radius
  \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))+1\<close> around the base point, an \<open>O(\<surd>\<epsilon>)\<close> bound
  that makes the \<open>y\<^sub>s \<in> \<Omega>\<close> hypothesis of the comparison theorems
  dischargeable rather than assumed.  Stated as a separate corollary so
  existing consumers of \<open>supconv_attained\<close> are untouched.\<close>

corollary supconv_attained_in:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and sub: "cball x (sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1) \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball[OF B e cu] by blast
  have "ys \<in> cball x (sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1)"
    using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

text \<open>The family form: along any sequence of base points, the attaining points
  can be chosen inside \<open>\<Omega>\<close> simultaneously, provided each base point's
  ball is.\<close>

corollary supconv_attained_family_in:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and xs :: "nat \<Rightarrow> 'a"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and sub: "\<And>i. cball (xs i)
        (sqrt (max 0 (2*\<epsilon>*(Bu - u (xs i)))) + 1) \<subseteq> \<Omega>"
  shows "\<exists>ys. \<forall>i. ys i \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. y \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_in[OF B e cu sub] by blast
  then show ?thesis by (rule choice)
qed

subsection \<open>The attainment radius as a parameter\<close>

text \<open>The \<open>+1\<close> in \<open>supconv_attained_ball\<close> is an artifact of a strict
  inequality in its proof; with it, \<open>cball x R \<subseteq> \<Omega>\<close> asks \<open>\<Omega>\<close> for a ball
  of radius one, which no bounded \<open>\<Omega>\<close> of small diameter has.  Any radius
  exceeding \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))\<close> serves as well, separating the
  hypothesis into a geometric condition on \<open>R\<close> and a smallness condition
  on \<open>\<epsilon>\<close>, discharged separately at the top level.\<close>

theorem supconv_attained_ball_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
  shows "\<exists>ys. dist x ys \<le> R
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define M where "M = max 0 (2*\<epsilon>*(Bu - u x))"
  have M0: "0 \<le> M" unfolding M_def by simp
  have s0: "0 \<le> sqrt M" using M0 by simp
  have sR: "sqrt M < R" using R unfolding M_def .
  have R0: "0 < R" using s0 sR by linarith
  have Rsq: "2*\<epsilon>*(Bu - u x) < R\<^sup>2"
  proof -
    have sq: "(sqrt M)\<^sup>2 = M" using M0 by simp
    have "(sqrt M)\<^sup>2 < R\<^sup>2"
      by (rule power_strict_mono[OF sR s0]) simp
    then have "M < R\<^sup>2" unfolding sq .
    moreover have "2*\<epsilon>*(Bu - u x) \<le> M" unfolding M_def by simp
    ultimately show ?thesis by linarith
  qed
  have cpt: "compact (cball x R)" by (rule compact_cball)
  have ne: "cball x R \<noteq> {}" using R0 by auto
  have cont: "continuous_on (cball x R) (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
    by (intro continuous_intros continuous_on_subset[OF cu subset_UNIV])
       (use e in auto)
  obtain ys where ysin: "ys \<in> cball x R"
    and ysmax: "\<forall>y \<in> cball x R.
        u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using continuous_attains_sup[OF cpt ne cont] by blast
  have xin: "x \<in> cball x R" using R0 by simp
  have key: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    with ysmax show ?thesis by blast
  next
    case False
    then have gt: "R < dist x y" by simp
    have lt: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) < u x"
    proof -
      have "R\<^sup>2 < (dist x y)\<^sup>2"
        by (rule power_strict_mono[OF gt less_imp_le[OF R0]]) simp
      then have big: "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2"
        using Rsq by linarith
      have c0: "0 < 2*\<epsilon>" using e by simp
      have "(Bu - u x) * (2*\<epsilon>) < (dist x y)\<^sup>2"
        using big by (simp add: algebra_simps)
      then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using c0 by (simp add: pos_less_divide_eq)
      then show ?thesis using B[of y] by linarith
    qed
    have xval: "u x = u x - (dist x x)\<^sup>2 / (2*\<epsilon>)" by simp
    have "u x - (dist x x)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      using ysmax xin by blast
    with lt xval show ?thesis by linarith
  qed
  have "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  proof (rule antisym)
    show "supconv u \<epsilon> x \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      unfolding supconv_def by (rule cSUP_least) (auto simp: key)
    show "u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>) \<le> supconv u \<epsilon> x"
      unfolding supconv_def
      by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  qed
  moreover have "dist x ys \<le> R"
    using ysin by (simp add: dist_commute)
  ultimately show ?thesis by blast
qed

corollary supconv_attained_in_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and sub: "cball x R \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball_rad[OF B e cu R] by blast
  have "ys \<in> cball x R"
    using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

corollary supconv_attained_family_in_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and xs :: "nat \<Rightarrow> 'a"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "\<And>i. sqrt (max 0 (2*\<epsilon>*(Bu - u (xs i)))) < R"
    and sub: "\<And>i. cball (xs i) R \<subseteq> \<Omega>"
  shows "\<exists>ys. \<forall>i. ys i \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. y \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_in_rad[OF B e cu R sub] by blast
  then show ?thesis by (rule choice)
qed

text \<open>Every attainment point, not just the one \<open>supconv_attained_ball\<close>
  produces, lies inside that radius: if \<open>z\<close> attains then
  \<open>u z - dist\<^sup>2/(2\<epsilon>) \<ge> u x\<close> gives \<open>dist\<^sup>2 \<le> 2\<epsilon>(B\<^sub>u-u x)\<close>.  The universal
  form is needed where membership of the attainment point in \<open>\<Omega>\<close> comes
  from a gate on \<open>u\<close> rather than from a ball.\<close>



lemma visc_subsol_mono_dom:
  assumes s: "visc_subsol k L \<Omega> u" and sub: "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_subsol k L \<Omega>' u"
  using s sub unfolding visc_subsol_def by blast

text \<open>\<open>visc_subsol_env k L K \<Omega> u\<close> reads \<open>u\<close> only on \<open>K\<close>, insensitive to its
  values off \<open>K\<close>, which is what makes the extension below legitimate:
  Definition 3.1(a) transfers to the extended function for free.\<close>

lemma visc_subsol_env_agrees:
  fixes K :: "(real^'n::finite) set"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u" and OK: "\<Omega> \<subseteq> K"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y"
  shows "visc_subsol_env2 k L K \<Omega> u'"
  unfolding visc_subsol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. u' y - \<phi> y \<le> u' x - \<phi> x"
  have xK: "x \<in> K" using x OK by blast
  have gl': "\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x"
  proof
    fix y assume y: "y \<in> K"
    have "u y - \<phi> y = u' y - \<phi> y" using eq[OF y] by simp
    also have "\<dots> \<le> u' x - \<phi> x" using gl y by blast
    also have "\<dots> = u x - \<phi> x" using eq[OF xK] by simp
    finally show "u y - \<phi> y \<le> u x - \<phi> x" .
  qed
  show "ell_op_lsc k L (g x) H \<le> 1"
    using sub x tf gl' unfolding visc_subsol_env2_def by blast
qed

text \<open>\<open>usc_extend_const_below\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>Far from \<open>K\<close> the extended function's sup-convolution returns to the
  constant, since the whole competing ball misses \<open>K\<close>: this confines the
  doubling maximiser to a bounded neighbourhood of \<open>K\<close> without boundary
  avoidance on the \<open>x\<close>-side.\<close>


lemma supconv_attained_usc_ball:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  obtains ys where "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    and "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define R where "R = sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
  have R1: "1 \<le> R" unfolding R_def by simp
  have R0: "0 < R" using R1 by linarith
  define g where "g = (\<lambda>y :: real^'n. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
  have ene: "2*\<epsilon> \<noteq> 0" using e by simp
  have pc: "isCont (\<lambda>y :: real^'n. - ((dist x y)\<^sup>2 / (2*\<epsilon>))) z" for z
    by (intro continuous_intros) (use ene in simp_all)
  have p2: "\<exists>d>0. \<forall>y. dist zz y < d \<longrightarrow> - ((dist x y)\<^sup>2 / (2*\<epsilon>)) < cc"
    if "- ((dist x zz)\<^sup>2 / (2*\<epsilon>)) < cc" for cc and zz :: "real^'n"
    by (rule usc_eps_of_continuous[OF pc that])
  have gusc: "\<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> g y < c" if lt: "g z < c"
    for c and z :: "real^'n"
  proof -
    have lt': "u z + (- ((dist x z)\<^sup>2 / (2*\<epsilon>))) < c"
      using lt unfolding g_def by simp
    from usc_eps_add[OF uscu p2 lt'] obtain d where d0: "0 < d"
      and h: "\<forall>y. dist z y < d \<longrightarrow> u y + (- ((dist x y)\<^sup>2 / (2*\<epsilon>))) < c"
      by blast
    show ?thesis
    proof (rule exI[of _ d], intro conjI allI impI d0)
      fix y assume "dist z y < d"
      then show "g y < c" using h unfolding g_def by simp
    qed
  qed
  have gB: "g y \<le> Bu" for y
  proof -
    have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
    then show ?thesis unfolding g_def using B[of y] by linarith
  qed
  have neS: "cball x R \<noteq> {}" using R0 by auto
  obtain ys where ysS: "ys \<in> cball x R"
    and mxb: "\<And>y. y \<in> cball x R \<Longrightarrow> g y \<le> g ys"
    using usc_attains_sup_gen[OF gusc _ compact_cball neS, of Bu] gB by blast
  have xS: "x \<in> cball x R" using R0 by simp
  have glob: "g y \<le> g ys" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    then show ?thesis by (rule mxb)
  next
    case False
    then have dR: "R < dist x y" by linarith
    have s0: "0 \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))" by simp
    have "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < dist x y"
      using dR unfolding R_def by linarith
    then have "(sqrt (max 0 (2*\<epsilon>*(Bu - u x))))\<^sup>2 < (dist x y)\<^sup>2"
      using s0 by (intro power_strict_mono) simp_all
    then have Rsq: "max 0 (2*\<epsilon>*(Bu - u x)) < (dist x y)\<^sup>2" by simp
    then have "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2" by simp
    then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
      using e by (simp add: pos_less_divide_eq mult.commute)
    then have "g y < u x" unfolding g_def using B[of y] by linarith
    moreover have "u x = g x" unfolding g_def by simp
    moreover have "g x \<le> g ys" by (rule mxb[OF xS])
    ultimately show ?thesis by linarith
  qed
  have bdd: "bdd_above (range (\<lambda>y :: real^'n. u y - (dist x y)\<^sup>2 / (2*\<epsilon>)))"
    by (rule supconv_bdd_above[OF B e])
  have le: "supconv u \<epsilon> x \<le> g ys"
    unfolding supconv_def
  proof (rule cSUP_least)
    show "(UNIV :: (real^'n) set) \<noteq> {}" by simp
    fix y :: "real^'n"
    show "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> g ys"
      using glob[of y] unfolding g_def by simp
  qed
  have ge: "g ys \<le> supconv u \<epsilon> x"
    unfolding supconv_def g_def by (rule cSUP_upper[OF UNIV_I bdd])
  have eq: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using le ge unfolding g_def by linarith
  have dR: "dist x ys \<le> R" using ysS by (simp add: dist_commute)
  show ?thesis by (rule that[of ys]) (use dR eq in \<open>simp_all add: R_def\<close>)
qed

lemma supconv_attained_usc_ball_rad:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
  shows "\<exists>ys. dist x ys \<le> R
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF B e uscu] by blast
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

text \<open>\<open>doubled_maximiser_over_UNIV_snd\<close>, \<open>mxK_of_UNIV_snd\<close>, \<open>cont_pos_near\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>



lemma supconv_le_of_local_bound:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and loc: "\<And>y. dist x y \<le> R \<Longrightarrow> u y \<le> M"
  shows "supconv u \<epsilon> x \<le> M"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball_rad[OF B e cu R] by blast
  have nn: "0 \<le> (dist x ys)\<^sup>2 / (2*\<epsilon>)" using e by simp
  have "supconv u \<epsilon> x \<le> u ys" unfolding v using nn by linarith
  also have "u ys \<le> M" by (rule loc[OF d])
  finally show ?thesis .
qed

text \<open>\<open>supconv_radius_uniform\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

theorem supconv_sandwich:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and lo: "\<And>y. Bl \<le> u y"
    and e: "0 < \<epsilon>" and cu: "continuous_on UNIV u"
    and h: "0 < \<eta>" and small: "2*\<epsilon>*(Bu - Bl) < \<eta>\<^sup>2"
    and loc: "\<And>y. dist x y \<le> \<eta> \<Longrightarrow> u y \<le> u x + \<sigma>"
  shows "u x \<le> supconv u \<epsilon> x"
    and "supconv u \<epsilon> x \<le> u x + \<sigma>"
proof -
  show "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B e])
  show "supconv u \<epsilon> x \<le> u x + \<sigma>"
    by (rule supconv_le_of_local_bound
        [where Bu = Bu and R = \<eta> and M = "u x + \<sigma>",
         OF B e cu supconv_radius_uniform[OF lo e h small] loc])
qed

subsection \<open>Locating the doubling maximiser away from the boundary\<close>

text \<open>\<open>uniform_modulus_on_compact\<close>, \<open>doubling_maximiser_far_from_boundary\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>The two penalty-carrying localisation helpers, generalised\<close>

text \<open>\<open>doubling_maximiser_value_transfer_gen\<close>, \<open>norm_lt_of_penalty_bound_gen\<close> live in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

subsection \<open>\<open>soft_pen\<close> vanishes on the diagonal and is coercive\<close>

text \<open>Both facts reduce to the radial profile
  \<open>h s = \<kappa>(s/2-(sqrt(s+1)-1))\<close> at \<open>s = norm d\<^sup>2\<close>: \<open>h 0 = 0\<close> is immediate,
  and monotonicity follows the difference-of-squares trick of
  \<open>soft_R_lipschitz\<close>.\<close>


















lemma supconv_uniform_upper:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K"
    and B: "\<And>y. u y \<le> Bu" and lo: "\<And>y. Bl \<le> u y"
    and cu: "continuous_on UNIV u"
    and s: "0 < \<sigma>"
  shows "\<exists>\<epsilon>\<^sub>0. 0 < \<epsilon>\<^sub>0 \<and> (\<forall>\<epsilon>. 0 < \<epsilon> \<longrightarrow> \<epsilon> \<le> \<epsilon>\<^sub>0
      \<longrightarrow> (\<forall>x\<in>K. supconv u \<epsilon> x \<le> u x + \<sigma>))"
proof -
  have bK: "bounded K" by (rule compact_imp_bounded[OF cK])
  then obtain R\<^sub>0 where R0: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> R\<^sub>0"
    using bounded_iff by blast
  define R where "R = max 0 R\<^sub>0 + 1"
  have R1: "1 \<le> R" unfolding R_def by simp
  have KR: "norm x \<le> R - 1" if "x \<in> K" for x
    using R0[OF that] unfolding R_def by simp
  have cb: "compact (cball (0::real^'n) R)" by (rule compact_cball)
  have cuR: "continuous_on (cball (0::real^'n) R) u"
    by (rule continuous_on_subset[OF cu subset_UNIV])
  obtain \<eta> where hpos: "0 < \<eta>"
    and modu: "\<And>p q. p \<in> cball (0::real^'n) R \<Longrightarrow> q \<in> cball (0::real^'n) R
        \<Longrightarrow> dist p q \<le> \<eta> \<Longrightarrow> u q \<le> u p + \<sigma>"
    using uniform_modulus_on_compact[OF cb cuR s] by blast
  define h where "h = min \<eta> 1"
  have hp: "0 < h" unfolding h_def using hpos by simp
  have hle1: "h \<le> 1" unfolding h_def by simp
  have hlem: "h \<le> \<eta>" unfolding h_def by simp
  have Dnn: "0 \<le> max 0 (Bu - Bl)" by simp
  have hsq: "0 < h\<^sup>2" using hp by simp
  obtain \<epsilon>\<^sub>0 where e0pos: "0 < \<epsilon>\<^sub>0"
    and esm: "2*\<epsilon>\<^sub>0*(max 0 (Bu - Bl)) < h\<^sup>2"
    using exists_eps_aux[OF hsq Dnn] by blast
  \<comment> \<open>the bound survives shrinking \<open>\<epsilon>\<close>, which is what lets the assembly pick ONE
      \<open>\<epsilon>\<close> serving both sup-convolutions\<close>
  have esm2: "2*\<epsilon>*(Bu - Bl) < h\<^sup>2" if ep: "0 < \<epsilon>" and ele: "\<epsilon> \<le> \<epsilon>\<^sub>0" for \<epsilon>
  proof -
    have le: "Bu - Bl \<le> max 0 (Bu - Bl)" by simp
    have e2: "0 \<le> 2*\<epsilon>" using ep by linarith
    have step1: "2*\<epsilon>*(Bu - Bl) \<le> 2*\<epsilon>*(max 0 (Bu - Bl))"
      by (rule mult_left_mono[OF le e2])
    have le2: "2*\<epsilon> \<le> 2*\<epsilon>\<^sub>0" using ele by linarith
    have step2: "2*\<epsilon>*(max 0 (Bu - Bl)) \<le> 2*\<epsilon>\<^sub>0*(max 0 (Bu - Bl))"
      by (rule mult_right_mono[OF le2 Dnn])
    from step1 step2 esm show ?thesis by linarith
  qed
  have main: "supconv u \<epsilon> x \<le> u x + \<sigma>"
    if ep: "0 < \<epsilon>" and ele: "\<epsilon> \<le> \<epsilon>\<^sub>0" and x: "x \<in> K" for \<epsilon> x
  proof -
    have nx: "norm x \<le> R - 1" by (rule KR[OF x])
    have xR: "x \<in> cball (0::real^'n) R"
      using nx R1 by (simp add: dist_norm)
    have loc: "u y \<le> u x + \<sigma>" if d: "dist x y \<le> h" for y
    proof -
      have tri: "dist 0 y \<le> dist 0 x + dist x y" by (rule dist_triangle)
      have d0y: "dist (0::real^'n) y = norm y" by simp
      have d0x: "dist (0::real^'n) x = norm x" by simp
      have "norm y \<le> norm x + h" using tri d hle1 unfolding d0y d0x by linarith
      then have "norm y \<le> R" using nx hle1 by linarith
      then have yR: "y \<in> cball (0::real^'n) R" by (simp add: dist_norm)
      have dh: "dist x y \<le> \<eta>" using d hlem by linarith
      show ?thesis by (rule modu[OF xR yR dh])
    qed
    show ?thesis
      by (rule supconv_sandwich(2)[OF B lo ep cu hp esm2[OF ep ele] loc])
  qed
  show ?thesis using e0pos main by blast
qed

subsection \<open>Threading the parameters: the localised maximiser for \<open>soft_pen\<close>\<close>

text \<open>Threading the five smallness steps, in order (the maximiser depends on
  \<open>\<kappa>\<^sub>P\<close>, which must be fixed before it, and \<open>\<beta>\<close> before \<open>\<kappa>\<^sub>P\<close>):

    \<open>G = M - m > 0\<close>, split as \<open>\<sigma> = \<tau> = \<tau>' = G/8\<close>
    \<open>\<tau>\<close>  fixes \<open>\<beta>\<^sub>0\<close>   (modulus of \<open>g\<close> on \<open>K\<close>)
    \<open>\<tau>'\<close> fixes \<open>\<kappa>\<^sub>0\<close>   (modulus of \<open>f + g\<close> on \<open>K\<close>)
    \<open>\<kappa>\<^sub>g = \<kappa>\<^sub>0/2\<close>, \<open>\<beta> = min \<beta>\<^sub>0 (\<kappa>\<^sub>0/2)\<close>
    \<open>\<sigma>\<close>  fixes \<open>\<epsilon>\<close>, and \<open>\<beta>\<close> fixes \<open>\<kappa>\<^sub>P\<close> and the maximiser

  The bound for \<open>ŷ\<close> comes free from the one for \<open>x̂\<close> via the triangle
  inequality, avoiding a second modulus for \<open>f\<close>.\<close>

theorem doubling_localised_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and zK: "z \<in> K"
    and Mval: "M \<le> \<theta> * u z - w z"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> \<theta> * u c - w c \<le> m"
    and gapMm: "m < M"
  shows "\<exists>\<epsilon>>0. \<exists>\<kappa>\<^sub>g>0. \<exists>\<kappa>\<^sub>P>0. \<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
           - soft_pen \<kappa>\<^sub>P (xh - yh))
    \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b)
    \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b)
    \<and> 2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2
    \<and> 2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
proof -
  \<comment> \<open>1. split the gap\<close>
  have Gpos: "0 < M - m" using gapMm by linarith
  obtain \<sigma> \<tau> \<tau>' where spos: "0 < \<sigma>" and tpos: "0 < \<tau>" and t'pos: "0 < \<tau>'"
    and gsum: "2*\<sigma> + \<tau> + \<tau>' < M - m"
    using gap_split_aux[OF Gpos] by blast
  \<comment> \<open>2. the modulus of \<open>g = -w\<close>, at scale \<open>\<tau>\<close>\<close>
  have cwK: "continuous_on K (- w)"
    by (rule continuous_on_subset[OF cw subset_UNIV])
  obtain \<beta>\<^sub>0 where b0pos: "0 < \<beta>\<^sub>0"
    and modg0: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<beta>\<^sub>0 \<Longrightarrow> (- w) q \<le> (- w) p + \<tau>"
    using uniform_modulus_on_compact[OF cK cwK tpos] by blast
  \<comment> \<open>3. the modulus of \<open>f + g\<close>, at scale \<open>\<tau>'\<close>\<close>
  have cFK: "continuous_on K (\<lambda>y. \<theta> * u y + (- w) y)"
    by (intro continuous_intros
        continuous_on_subset[OF cu subset_UNIV]
        continuous_on_subset[OF cw subset_UNIV])
  obtain \<kappa>\<^sub>0 where k0pos: "0 < \<kappa>\<^sub>0"
    and modF0: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<kappa>\<^sub>0
        \<Longrightarrow> (\<lambda>y. \<theta> * u y + (- w) y) q \<le> (\<lambda>y. \<theta> * u y + (- w) y) p + \<tau>'"
    using uniform_modulus_on_compact[OF cK cFK t'pos] by blast
  \<comment> \<open>4. the two radii\<close>
  define \<kappa>\<^sub>g where "\<kappa>\<^sub>g = \<kappa>\<^sub>0/2"
  define \<beta> where "\<beta> = min \<beta>\<^sub>0 (\<kappa>\<^sub>0/2)"
  have kgpos: "0 < \<kappa>\<^sub>g" unfolding \<kappa>\<^sub>g_def using k0pos by simp
  have bpos: "0 < \<beta>" unfolding \<beta>_def using b0pos k0pos by simp
  have bleb0: "\<beta> \<le> \<beta>\<^sub>0" unfolding \<beta>_def by simp
  have fit: "\<kappa>\<^sub>g + \<beta> \<le> \<kappa>\<^sub>0"
    unfolding \<kappa>\<^sub>g_def \<beta>_def using k0pos by simp
  \<comment> \<open>5. one \<open>\<epsilon>\<close> for BOTH sup-convolutions\<close>
  obtain \<epsilon>u where eupos: "0 < \<epsilon>u"
    and upu: "\<And>e x. 0 < e \<Longrightarrow> e \<le> \<epsilon>u \<Longrightarrow> x \<in> K
        \<Longrightarrow> supconv (\<lambda>y. \<theta> * u y) e x \<le> \<theta> * u x + \<sigma>"
    using supconv_uniform_upper[OF cK Bu lou cu spos] by blast
  obtain \<epsilon>w where ewpos: "0 < \<epsilon>w"
    and upw: "\<And>e x. 0 < e \<Longrightarrow> e \<le> \<epsilon>w \<Longrightarrow> x \<in> K
        \<Longrightarrow> supconv (- w) e x \<le> (- w) x + \<sigma>"
    using supconv_uniform_upper[OF cK Bw low cw spos] by blast
  \<comment> \<open>\<open>\<epsilon>\<close> must ALSO be small enough that the sup-convolution attainment radii
      \<open>R\<^sub>u\<close>, \<open>R\<^sub>w\<close> fit inside \<open>\<kappa>\<^sub>g\<close> --- a constraint that comes from downstream,
      from \<open>smallu\<close>/\<open>fitu\<close> in \<open>comparison_from_localised_maximiser_soft\<close>, and is
      invisible from the boundary argument alone.  It is consistent because
      \<open>\<kappa>\<^sub>g\<close> is fixed at step 4, BEFORE \<open>\<epsilon>\<close> is chosen at step 5.\<close>
  have hq: "0 < (\<kappa>\<^sub>g/4)\<^sup>2" using kgpos by simp
  have DunN: "0 \<le> max 0 (Bu - Blu)" by simp
  have DwnN: "0 \<le> max 0 (Bw - Blw)" by simp
  obtain \<epsilon>A where eApos: "0 < \<epsilon>A"
    and eAlt: "2*\<epsilon>A*(max 0 (Bu - Blu)) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using exists_eps_aux[OF hq DunN] by blast
  obtain \<epsilon>B where eBpos: "0 < \<epsilon>B"
    and eBlt: "2*\<epsilon>B*(max 0 (Bw - Blw)) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using exists_eps_aux[OF hq DwnN] by blast
  define \<epsilon> where "\<epsilon> = min (min \<epsilon>u \<epsilon>w) (min \<epsilon>A \<epsilon>B)"
  have epos: "0 < \<epsilon>" unfolding \<epsilon>_def using eupos ewpos eApos eBpos by simp
  have eleu: "\<epsilon> \<le> \<epsilon>u" unfolding \<epsilon>_def by simp
  have elew: "\<epsilon> \<le> \<epsilon>w" unfolding \<epsilon>_def by simp
  have eleA: "\<epsilon> \<le> \<epsilon>A" unfolding \<epsilon>_def by simp
  have eleB: "\<epsilon> \<le> \<epsilon>B" unfolding \<epsilon>_def by simp
  have smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (rule eps_mono_aux[OF epos eleA eAlt])
  have smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (rule eps_mono_aux[OF epos eleB eBlt])
  \<comment> \<open>6. an upper bound for the doubled functional on \<open>K \<times> K\<close>\<close>
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu epos] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw epos] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  obtain C where Cbnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (\<lambda>y. - supconv (- w) \<epsilon> y) y \<le> C"
    using doubling_upper_bound_exists[OF cK neK cA cB] by blast
  have Cbnd': "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y \<le> C"
    if "x \<in> K" "y \<in> K" for x y
    using Cbnd[OF that] by simp
  \<comment> \<open>7. \<open>\<beta>\<close> fixes \<open>\<kappa>\<^sub>P\<close> and with it the maximiser\<close>
  obtain \<kappa>\<^sub>P xh yh where kPpos: "0 < \<kappa>\<^sub>P" and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxb: "\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and near: "dist xh yh < \<beta>"
    using doubling_close_maximiser_supconv_soft
      [OF cK neK Bu Bw epos zK Cbnd' bpos] by blast
  have mx: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa>\<^sub>P (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mxb that by blast
  \<comment> \<open>8. transfer the value to the ORIGINAL functions\<close>
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have vt: "\<theta> * u z + (- w) z + soft_pen \<kappa>\<^sub>P (xh - yh)
      \<le> \<theta> * u xh + (- w) yh + 2*\<sigma>"
    by (rule doubling_maximiser_value_transfer_gen
        [where A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and Bf = "supconv (- w) \<epsilon>"
           and f = "\<lambda>y. \<theta> * u y" and g = "- w" and Pn = "soft_pen \<kappa>\<^sub>P"
           and K = K and xh = xh and yh = yh and z = z and \<sigma> = \<sigma>,
         OF mx zK soft_pen_zero
            supconv_ge[OF Bu epos] supconv_ge[OF Bw epos]
            upu[OF epos eleu xhK] upw[OF epos elew yhK]])
  have pnn: "0 \<le> soft_pen \<kappa>\<^sub>P (xh - yh)" by (rule soft_pen_nonneg[OF kPnn])
  have tr: "\<theta> * u z + (- w) z \<le> \<theta> * u xh + (- w) yh + 2*\<sigma>"
    using vt pnn by linarith
  \<comment> \<open>9. the boundary theorem, at radius \<open>\<kappa>\<^sub>g + \<beta>\<close>\<close>
  have valM: "M \<le> \<theta> * u z + (- w) z" using Mval by simp
  have nearle: "dist xh yh \<le> \<beta>" using near by linarith
  have modg: "(- w) q \<le> (- w) p + \<tau>" if "p \<in> K" "q \<in> K" "dist p q \<le> \<beta>" for p q
    using modg0[OF that(1) that(2)] that(3) bleb0 by linarith
  have bdry': "\<theta> * u c + (- w) c \<le> m" if "c \<in> K - interior K" for c
    using bdry[OF that] by simp
  have modF: "\<theta> * u p + (- w) p \<le> \<theta> * u q + (- w) q + \<tau>'"
    if "p \<in> K" "q \<in> K" "dist p q \<le> \<kappa>\<^sub>g + \<beta>" for p q
  proof -
    have "dist q p \<le> \<kappa>\<^sub>0" using that(3) fit by (simp add: dist_commute)
    from modF0[OF that(2) that(1) this] show ?thesis by simp
  qed
  have gap: "m + 2*\<sigma> + \<tau> + \<tau>' < M" using gsum by linarith
  have farx: "\<kappa>\<^sub>g + \<beta> < dist xh b" if b: "b \<in> K - interior K" for b
    by (rule doubling_maximiser_far_from_boundary
        [where f = "\<lambda>y. \<theta> * u y" and g = "- w" and K = K and xh = xh
           and yh = yh and M = M and z = z and \<sigma> = \<sigma> and \<beta> = \<beta>
           and \<tau> = \<tau> and m = m and \<kappa> = "\<kappa>\<^sub>g + \<beta>" and \<tau>' = \<tau>',
         OF xhK yhK valM tr nearle modg bdry' modF gap b])
  \<comment> \<open>10. and the mirror bound for \<open>ŷ\<close>, for free\<close>
  have fary: "\<kappa>\<^sub>g < dist yh b" if b: "b \<in> K - interior K" for b
  proof -
    have tri: "dist xh b \<le> dist xh yh + dist yh b" by (rule dist_triangle)
    have "\<kappa>\<^sub>g + \<beta> < dist xh b" by (rule farx[OF b])
    then show ?thesis using tri near by linarith
  qed
  \<comment> \<open>explicit introductions: a single \<open>blast\<close> over this nested existential
      searches instead of just building the witness, and PIDE flags it as
      possibly nonterminating\<close>
  have f1: "\<kappa>\<^sub>g < dist xh b" if b: "b \<in> K - interior K" for b
    using farx[OF b] bpos by linarith
  have F1: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b"
  proof
    fix b assume "b \<in> K - interior K"
    then show "\<kappa>\<^sub>g < dist xh b" by (rule f1)
  qed
  have F2: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b"
  proof
    fix b assume "b \<in> K - interior K"
    then show "\<kappa>\<^sub>g < dist yh b" by (rule fary)
  qed
  have inner: "(\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh))
      \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b)
      \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b)
      \<and> 2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2
      \<and> 2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (intro conjI mxb F1 F2 smallu smallw)
  show ?thesis
    by (rule exI[of _ \<epsilon>], rule conjI[OF epos],
        rule exI[of _ \<kappa>\<^sub>g], rule conjI[OF kgpos],
        rule exI[of _ \<kappa>\<^sub>P], rule conjI[OF kPpos],
        rule bexI[OF _ xhK], rule bexI[OF _ yhK], rule inner)
qed

subsection \<open>Skolemising a four-component existential over an index\<close>

text \<open>\<open>choice4\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

text \<open>The shifted analogue: run Jensen at the perturbation \<open>\<delta>\<^sub>i\<close> and tilt
  \<open>dd\<^sub>i\<close> of \<open>shifted_family_parameters\<close>, and skolemise.  Both hypotheses
  Jensen needs are automatic, from \<open>shifted_annulus_bound_split\<close> and the
  smallness condition \<open>2 dd\<^sub>i r < \<delta>\<^sub>i\<rho>\<^sup>2\<close>; only the maximiser property
  over \<open>cball \<xi>\<^sub>0 r\<close> is assumed.\<close>








theorem comparison_supconv_bounded_family:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "nat \<Rightarrow> real^'n^'n" and Pu Pw G :: "nat \<Rightarrow> real^'n"
    and xu xw ysu ysw :: "nat \<Rightarrow> real^'n"
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
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
        [OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw ysuOr yswOr
           symXr symYr p0 optur optwr jetur jetwr cX cY cPu cPw pnz])
qed


(*<*)
end
(*>*)
