section \<open>Readings of the paper's wording, checked\<close>

(*<*)
theory Paper_Readings
  imports Theorem_1_1_Statement
begin
(*>*)

text \<open>Several places in \<^cite>\<open>LaiShkolnikovSoner\<close> admit more than one reading,
  and the formalisation had to commit to one; elsewhere the formal definitions
  differ in form from the paper's.  This theory settles what turns on each
  choice and each difference, so that the commitments are checkable rather than
  asserted.  Its theorems are deliverables in their own right: no later
  clean-up may remove them because no proof of Theorem 1.1 uses them.\<close>

section \<open>The lower envelope: within \<open>K\<close>, or over \<open>\<real>\<^sup>n\<close>?\<close>

text \<open>Definition 3.1 writes \<open>u\<^sub>*\<close> as \<open>lim\<^sub>\<epsilon>\<^sub>\<down>\<^sub>0 inf\<^sub>{\<^sub>|\<^sub>y\<^sub>-\<^sub>x\<^sub>|\<^sub><\<^sub>\<epsilon>\<^sub>}\<close> without saying whether
  \<open>y\<close> ranges over \<open>K\<close> or over \<open>\<real>\<^sup>n\<close>.  The formalisation reads it within \<open>K\<close>
  (\<^const>\<open>lsc_envK\<close>); the alternative is the global \<^const>\<open>lsc_env\<close>.\<close>

subsection \<open>For the value function the two readings do not differ\<close>

text \<open>The value function is nonnegative, so under \<^emph>\<open>either\<close> reading the set of
  boundary points carrying the zero boundary condition for the supersolution is
  empty, and that half of clause (3) is vacuous for \<open>v\<close> itself.  Whatever
  separates the readings, it is not this.\<close>

theorem boundary_set_empty_K:
  fixes K :: "(real^'n::finite) set"
  shows "{x \<in> K - interior K.
           lsc_envK K (\<lambda>z. enn2real (xval k L K z)) x < 0} = {}"
proof -
  have "0 \<le> lsc_envK K (\<lambda>z. enn2real (xval k L K z)) x" if "x \<in> K" for x
    by (rule lsc_envK_ge[OF _ that]) simp
  then show ?thesis by force
qed

theorem boundary_set_empty_global:
  fixes K :: "(real^'n::finite) set"
  shows "{x \<in> K - interior K.
           lsc_env (\<lambda>z. enn2real (xval k L K z)) x < 0} = {}"
proof -
  have "0 \<le> lsc_env (\<lambda>z. enn2real (xval k L K z)) x" if "x \<in> K" for x
    by (rule lsc_env_ge) simp
  then show ?thesis by force
qed

subsection \<open>For the competitor they do, and only one reading is well posed\<close>

text \<open>The readings part in clause (4), where the same expression is a
  \<^emph>\<open>hypothesis\<close> on a competitor \<open>u\<close>.  Definition 3.1 supplies \<open>u\<close> only on \<open>K\<close>.
  The \<open>K\<close>-relative envelope uses exactly that data:\<close>

lemma lsc_envK_cong:
  assumes "\<And>y. y \<in> K \<Longrightarrow> u y = u' y"
  shows "lsc_envK K u x = lsc_envK K u' x"
  unfolding lsc_envK_def using assms by (auto intro!: SUP_cong INF_cong)

text \<open>The global envelope does not.  Two functions agreeing on \<open>K\<close> --- so
  indistinguishable as competitors, and with the same conclusion \<open>u = v\<close> on
  \<open>K\<close> to prove --- have the same \<open>K\<close>-relative envelope but different global
  ones at a point of \<open>K\<close>.  Under the global reading the hypothesis of the
  uniqueness clause would therefore depend on values the paper never supplies,
  so it is the \<open>K\<close>-relative reading that is well posed.\<close>

theorem lsc_env_not_determined_on_K:
  "\<exists>(K :: real set) u u' x. x \<in> K \<and> (\<forall>y\<in>K. u y = u' y)
      \<and> lsc_envK K u x = lsc_envK K u' x
      \<and> lsc_env u x \<noteq> lsc_env u' x"
proof -
  define u  :: "real \<Rightarrow> real" where "u  = (\<lambda>_. 0)"
  define u' :: "real \<Rightarrow> real" where "u' = (\<lambda>y. if y = 0 then 0 else - 1)"
  have agree: "\<forall>y\<in>{0::real}. u y = u' y" by (simp add: u_def u'_def)
  have envu: "lsc_env u 0 = 0"
    unfolding lsc_env_def u_def by simp
  have inf': "(INF y \<in> ball (0::real) e. u' y) = - 1" if e: "0 < e" for e
  proof (rule antisym)
    have bdd: "bdd_below (u' ` ball (0::real) e)"
      by (rule bdd_belowI[of _ "- 1"]) (auto simp: u'_def)
    have mem: "e/2 \<in> ball (0::real) e" using e by (simp add: dist_real_def)
    have "(INF y \<in> ball (0::real) e. u' y) \<le> u' (e/2)"
      by (rule cINF_lower[OF bdd mem])
    also have "u' (e/2) = - 1" using e by (simp add: u'_def)
    finally show "(INF y \<in> ball (0::real) e. u' y) \<le> - 1" .
    show "- 1 \<le> (INF y \<in> ball (0::real) e. u' y)"
      using e by (intro cINF_greatest) (auto simp: u'_def)
  qed
  have envu': "lsc_env u' 0 = - 1"
    unfolding lsc_env_def using inf' by simp
  have "lsc_envK {0::real} u 0 = lsc_envK {0::real} u' 0"
    by (rule lsc_envK_cong) (use agree in simp)
  then show ?thesis
    using agree envu envu' by (intro exI[of _ "{0::real}"] exI[of _ u]
        exI[of _ u'] exI[of _ 0]) simp
qed


section \<open>The expandability hypothesis: the paper's indexed family\<close>

text \<open>Theorem 1.1 asks for maps \<open>T\<^sub>\<iota>\<close>, \<open>\<iota> \<in> (1,2]\<close>, each a composition of a
  rotation, a dilation and a translation, with \<open>K \<subseteq> int T\<^sub>\<iota>(K)\<close> and
  \<open>lim\<^sub>\<iota>\<^sub>\<down>\<^sub>1 T\<^sub>\<iota> = I\<close>.  The index range beginning at \<open>1\<close> identifies \<open>\<iota>\<close> as the
  dilation factor, which is how it is read here; \<open>lim\<^sub>\<iota>\<^sub>\<down>\<^sub>1 T\<^sub>\<iota> = I\<close> is read on
  the data, the rotation tending to the identity and the translation to zero.\<close>

definition paper_expandable :: "(real^'n::finite) set \<Rightarrow> bool" where
  "paper_expandable K \<longleftrightarrow>
     (\<exists>R b. (\<forall>i. 1 < i \<longrightarrow> i \<le> 2 \<longrightarrow>
                orthogonal_matrix (R i)
              \<and> K \<subseteq> interior ((\<lambda>x. i *\<^sub>R (R i *v x) + b i) ` K))
          \<and> (\<forall>e>0. \<exists>d>1. \<forall>i. 1 < i \<longrightarrow> i < d \<longrightarrow>
                (\<forall>x. norm (R i *v x - x) \<le> e * norm x) \<and> norm (b i) \<le> e))"

text \<open>The direction that matters: the paper's hypothesis implies the formal
  one, so Theorem 1.1 applies whenever Theorem 1.1's own hypothesis holds.
  \<^const>\<open>expandable\<close> differs in presenting the family as \<open>\<forall>e>0. \<exists>\<dots>\<close>, in
  measuring closeness on the inverse map over \<open>K\<close> --- which is what the
  comparison argument consumes --- and in allowing reflections, which only
  weakens it further.\<close>

theorem paper_expandable_imp_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and pe: "paper_expandable K"
  shows "expandable K"
proof -
  obtain R b where
    fam: "\<And>i. 1 < i \<Longrightarrow> i \<le> 2 \<Longrightarrow> orthogonal_matrix (R i)
              \<and> K \<subseteq> interior ((\<lambda>x. i *\<^sub>R (R i *v x) + b i) ` K)"
    and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>d>1. \<forall>i. 1 < i \<longrightarrow> i < d \<longrightarrow>
                (\<forall>x. norm (R i *v x - x) \<le> e * norm x) \<and> norm (b i) \<le> e"
    using pe unfolding paper_expandable_def by blast
  obtain M :: real where MK: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> M"
    using compact_imp_bounded[OF cK] unfolding bounded_iff by blast
  define MM where "MM = max M 0"
  have M0: "0 \<le> MM" unfolding MM_def by simp
  have MMK: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> MM" unfolding MM_def using MK by force
  show ?thesis
    unfolding expandable_def
  proof (intro allI impI)
    fix e :: real assume e: "0 < e"
    define e' where "e' = e / (2 * (MM + 1))"
    have e'0: "0 < e'" unfolding e'_def using e M0 by simp
    have e'e: "e' \<le> e / 2" unfolding e'_def using e M0 by (simp add: field_simps)
    obtain d where d1: "1 < d"
      and cl: "\<And>i. 1 < i \<Longrightarrow> i < d \<Longrightarrow>
          (\<forall>x. norm (R i *v x - x) \<le> e' * norm x) \<and> norm (b i) \<le> e'"
      using conv[OF e'0] by blast
    define del where "del = min (min (d - 1) 1) e' / 2"
    have del0: "0 < del" unfolding del_def using d1 e'0 by simp
    have deld: "del < d - 1" unfolding del_def using d1 e'0 by simp
    have del1: "del \<le> 1/2" unfolding del_def using d1 e'0 by simp
    have dele: "del \<le> e'" unfolding del_def using d1 e'0 by simp
    define c where "c = 1 + del"
    have c1: "1 < c" unfolding c_def using del0 by simp
    have c2: "c \<le> 2" unfolding c_def using del1 by simp
    have cd: "c < d" unfolding c_def using deld by simp
    have c0: "0 < c" using c1 by linarith
    have ce: "c < 1 + e" unfolding c_def using dele e'e e by linarith
    have orth: "orthogonal_matrix (R c)" using fam[OF c1 c2] by blast
    have Ksub: "K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R c *v x) + b c) ` K)"
      using fam[OF c1 c2] by blast
    have Rcl: "\<And>x. norm (R c *v x - x) \<le> e' * norm x" using cl[OF c1 cd] by blast
    have bcl: "norm (b c) \<le> e'" using cl[OF c1 cd] by blast
    have tR: "orthogonal_matrix (transpose (R c))" using orth by simp
    have normT: "\<And>y. norm (transpose (R c) *v y) = norm y"
      by (rule norm_orthogonal_matrix_vector[OF tR])

    have key: "dist ((1/c) *\<^sub>R (transpose (R c) *v (x - b c))) x \<le> e"
      if xK: "x \<in> K" for x
    proof -
      have nx: "norm x \<le> MM" by (rule MMK[OF xK])
      have inv: "transpose (R c) *v (R c *v x) = x"
      proof -
        have "transpose (R c) *v (R c *v x) = (transpose (R c) ** R c) *v x"
          by (rule matrix_vector_mul_assoc)
        also have "\<dots> = x"
          using orth unfolding orthogonal_matrix_def by simp
        finally show ?thesis .
      qed
      have e1: "transpose (R c) *v x - x = transpose (R c) *v (x - R c *v x)"
        unfolding matrix_vector_mult_diff_distrib inv by (rule refl)
      have b1: "norm (transpose (R c) *v x - x) \<le> e' * MM"
      proof -
        have "norm (transpose (R c) *v x - x) = norm (x - R c *v x)"
          unfolding e1 by (rule normT)
        also have "\<dots> = norm (R c *v x - x)" by (rule norm_minus_commute)
        also have "\<dots> \<le> e' * norm x" by (rule Rcl)
        also have "\<dots> \<le> e' * MM" using nx e'0 by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      have split: "(1/c) *\<^sub>R (transpose (R c) *v (x - b c)) - x
          = (1/c) *\<^sub>R (transpose (R c) *v x - x) + ((1/c) - 1) *\<^sub>R x
            - (1/c) *\<^sub>R (transpose (R c) *v b c)"
        unfolding matrix_vector_mult_diff_distrib
        using c0 by (simp add: algebra_simps)
      have t1: "norm ((1/c) *\<^sub>R (transpose (R c) *v x - x)) \<le> e' * MM"
      proof -
        have "norm ((1/c) *\<^sub>R (transpose (R c) *v x - x))
            = (1/c) * norm (transpose (R c) *v x - x)" using c0 by simp
        also have "\<dots> \<le> 1 * norm (transpose (R c) *v x - x)"
          using c1 by (intro mult_right_mono) auto
        also have "\<dots> \<le> e' * MM" using b1 by simp
        finally show ?thesis .
      qed
      have t2: "norm (((1/c) - 1) *\<^sub>R x) \<le> e' * MM"
      proof -
        have inv1: "1/c \<le> 1" using c0 c1 by (simp add: field_simps)
        have "\<bar>(1/c) - 1\<bar> = (c - 1)/c" using c0 c1 by (simp add: field_simps)
        also have "\<dots> = (c - 1) * (1/c)" by simp
        also have "\<dots> \<le> (c - 1) * 1" using inv1 c1 by (intro mult_left_mono) auto
        also have "\<dots> \<le> e'" unfolding c_def using dele by simp
        finally have absle: "\<bar>(1/c) - 1\<bar> \<le> e'" .
        have "norm (((1/c) - 1) *\<^sub>R x) = \<bar>(1/c) - 1\<bar> * norm x" by simp
        also have "\<dots> \<le> e' * norm x" using absle by (intro mult_right_mono) auto
        also have "\<dots> \<le> e' * MM" using nx e'0 by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      have t3: "norm ((1/c) *\<^sub>R (transpose (R c) *v b c)) \<le> e'"
      proof -
        have nb: "norm (transpose (R c) *v b c) = norm (b c)" by (rule normT)
        have "norm ((1/c) *\<^sub>R (transpose (R c) *v b c))
            = \<bar>1/c\<bar> * norm (transpose (R c) *v b c)" by (rule norm_scaleR)
        also have "\<dots> = (1/c) * norm (b c)" using c0 nb by simp
        also have "\<dots> \<le> 1 * norm (b c)" using c1 by (intro mult_right_mono) auto
        also have "\<dots> \<le> e'" using bcl by simp
        finally show ?thesis .
      qed
      have "dist ((1/c) *\<^sub>R (transpose (R c) *v (x - b c))) x
          = norm ((1/c) *\<^sub>R (transpose (R c) *v x - x) + ((1/c) - 1) *\<^sub>R x
                  - (1/c) *\<^sub>R (transpose (R c) *v b c))"
        unfolding dist_norm split by (rule refl)
      also have "\<dots> \<le> norm ((1/c) *\<^sub>R (transpose (R c) *v x - x) + ((1/c) - 1) *\<^sub>R x)
                     + norm ((1/c) *\<^sub>R (transpose (R c) *v b c))"
        by (rule norm_triangle_ineq4)
      also have "\<dots> \<le> (norm ((1/c) *\<^sub>R (transpose (R c) *v x - x))
                        + norm (((1/c) - 1) *\<^sub>R x))
                     + norm ((1/c) *\<^sub>R (transpose (R c) *v b c))"
        using norm_triangle_ineq by (intro add_right_mono)
      also have "\<dots> \<le> (e' * MM + e' * MM) + e'" using t1 t2 t3 by linarith
      also have "\<dots> = e' * (2 * MM + 1)" by (simp add: algebra_simps)
      also have "\<dots> \<le> e' * (2 * (MM + 1))" using e'0 by (intro mult_left_mono) auto
      also have "\<dots> = e" unfolding e'_def using M0 by simp
      finally show ?thesis .
    qed
    show "\<exists>R b c. orthogonal_matrix R \<and> 1 < c \<and> c < 1 + e
        \<and> K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
        \<and> (\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (x - b))) x \<le> e)"
      by (intro exI[of _ "R c"] exI[of _ "b c"] exI[of _ c] conjI
            orth c1 ce Ksub ballI key)
  qed
qed


section \<open>\<open>F\<close>, \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> over symmetric matrices\<close>

text \<open>Definition 3.1 evaluates \<open>F\<^sub>*\<close> and \<open>F\<^sup>*\<close> on \<open>\<real>\<^sup>n \<times> \<bbbS>\<^sup>n\<close>, the envelopes being
  taken there; the formalisation takes them over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  The paper's own
  envelopes are the following.\<close>

definition ell_op_lsc_sym ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<Rightarrow> (real^'n^'n) \<Rightarrow> ereal" where
  "ell_op_lsc_sym k L p M =
     (SUP e \<in> {0<..}. INF w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}.
        ell_op_pair k L w)"

definition ell_op_usc_sym ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) \<Rightarrow> (real^'n^'n) \<Rightarrow> ereal" where
  "ell_op_usc_sym k L p M =
     (INF e \<in> {0<..}. SUP w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}.
        ell_op_pair k L w)"

text \<open>At every symmetric \<open>M\<close> --- the only place Definition 3.1 evaluates them,
  at the Hessian of a test function --- the two pairs of envelopes agree, because
  \<open>F\<close> reads only the symmetric part of \<open>M\<close> (@{thm [source] ell_op_sym_part}) and
  \<open>N \<mapsto> (N + N\<^sup>T)/2\<close> moves no matrix away from a symmetric one.\<close>

(*<*)
lemma sym_part_closer:
  fixes M N :: "real^'n::finite^'n"
  assumes "transpose M = M"
  shows "dist ((1/2) *\<^sub>R (N + transpose N)) M \<le> dist N M"
proof -
  have "(1/2) *\<^sub>R (N + transpose N) - M = (1/2) *\<^sub>R ((N - M) + transpose (N - M))"
    using assms
    by (simp add: vec_eq_iff transpose_def algebra_simps)
  then have "norm ((1/2) *\<^sub>R (N + transpose N) - M)
      \<le> (1/2) * (norm (N - M) + norm (transpose (N - M)))"
    by (simp add: norm_triangle_ineq)
  then show ?thesis by (simp add: dist_norm norm_transpose_matrix)
qed

lemma sym_part_in_ball:
  fixes M N :: "real^'n::finite^'n"
  assumes M: "transpose M = M" and w: "(q, N) \<in> ball (p, M) e"
  shows "(q, (1/2) *\<^sub>R (N + transpose N)) \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}"
proof -
  have "dist (p, M) (q, (1/2) *\<^sub>R (N + transpose N)) \<le> dist (p, M) (q, N)"
    using sym_part_closer[OF M, of N]
    by (simp add: dist_Pair_Pair dist_commute real_sqrt_le_mono power_mono)
  moreover have "transpose ((1/2) *\<^sub>R (N + transpose N)) = (1/2) *\<^sub>R (N + transpose N)"
    by (simp add: transpose_add transpose_scalar add.commute)
  ultimately show ?thesis using w by auto
qed

lemma ell_op_pair_sym_part:
  "ell_op_pair k L (q, (1/2) *\<^sub>R (N + transpose N)) = ell_op_pair k L (q, N)"
  by (simp add: ell_op_pair_def ell_op_sym_part[symmetric])
(*>*)

theorem ell_op_lsc_sym_eq:
  fixes M :: "real^'n::finite^'n"
  assumes M: "transpose M = M"
  shows "ell_op_lsc_sym k L p M = ell_op_lsc k L p M"
  unfolding ell_op_lsc_sym_def ell_op_lsc_def
proof (rule SUP_cong[OF refl], rule antisym)
  fix e :: real
  show "(INF w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}. ell_op_pair k L w)
      \<le> (INF w \<in> ball (p, M) e. ell_op_pair k L w)"
  proof (rule INF_mono)
    fix w assume "w \<in> ball (p, M) e"
    then obtain q N where w: "w = (q, N)" "(q, N) \<in> ball (p, M) e" by (cases w) auto
    show "\<exists>w'\<in>ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}.
        ell_op_pair k L w' \<le> ell_op_pair k L w"
      by (intro bexI[OF _ sym_part_in_ball[OF M w(2)]])
         (simp add: w(1) ell_op_pair_sym_part)
  qed
  show "(INF w \<in> ball (p, M) e. ell_op_pair k L w)
      \<le> (INF w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}. ell_op_pair k L w)"
    by (rule INF_superset_mono) auto
qed

theorem ell_op_usc_sym_eq:
  fixes M :: "real^'n::finite^'n"
  assumes M: "transpose M = M"
  shows "ell_op_usc_sym k L p M = ell_op_usc k L p M"
  unfolding ell_op_usc_sym_def ell_op_usc_def
proof (rule INF_cong[OF refl], rule antisym)
  fix e :: real
  show "(SUP w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}. ell_op_pair k L w)
      \<le> (SUP w \<in> ball (p, M) e. ell_op_pair k L w)"
    by (rule SUP_subset_mono) auto
  show "(SUP w \<in> ball (p, M) e. ell_op_pair k L w)
      \<le> (SUP w \<in> ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}. ell_op_pair k L w)"
  proof (rule SUP_mono)
    fix w assume "w \<in> ball (p, M) e"
    then obtain q N where w: "w = (q, N)" "(q, N) \<in> ball (p, M) e" by (cases w) auto
    show "\<exists>w'\<in>ball (p, M) e \<inter> UNIV \<times> {N. transpose N = N}.
        ell_op_pair k L w \<le> ell_op_pair k L w'"
      by (intro bexI[OF _ sym_part_in_ball[OF M w(2)]])
         (simp add: w(1) ell_op_pair_sym_part)
  qed
qed


section \<open>The spectral conditions and the explicit form of \<open>F\<close>\<close>

text \<open>Eq. (1.9) bounds the \<open>(n-k)\<close>-th largest eigenvalue from below.  The
  formalisation states it through the Courant--Fischer characterisation
  \<^const>\<open>eigen_lb\<close>; for symmetric \<open>a\<close> that is exactly a bound on the \<open>m\<close>-th
  largest eigenvalue \<open>eigval m a\<close>, the difference of consecutive Ky Fan sums.\<close>

theorem eigen_lb_reading:
  fixes a :: "real^'n::finite^'n"
  assumes "transpose a = a" and "0 < m" and "m \<le> CARD('n)"
  shows "eigen_lb a m \<longleftrightarrow> 1 \<le> eigval m a"
  by (rule eigen_lb_iff_eigval_ge[OF assms])

text \<open>Eq. (3.5), the explicit form of \<open>F\<close> away from \<open>p = 0\<close> in terms of the
  ordered eigenvalues of the matrix \<open>M\<^sub>p\<close> of Eq. (3.4):\<close>

text \<open>@{thm [display] Mp_def}\<close>

theorem eq_3_5:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L p M
      = - (1/2) * (L * (\<Sum>i\<in>{1..CARD('n)}. max (eigval i (Mp p M)) 0)
                   + (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i (Mp p M)) 0))"
  using ell_op_eq_half_bracket[OF sym p L k]
    bracket_eq_sum[OF transpose_Mp[OF sym], of "CARD('n) - k" L]
  by simp


section \<open>Lemma 2.1\<close>

text \<open>The constraint set of Eq. (1.5) is the convex hull of the sufficiently
  volatile matrices.\<close>

theorem lemma_2_1:
  assumes "k < CARD('n::finite)"
  shows "convex hull (suff_volatile k) = (Pi_constraint k :: (real^'n^'n) set)"
  by (intro equalityI lemma_2_1_easy lemma_2_1_exact[OF assms])


section \<open>The uniqueness hypothesis is not vacuous\<close>

theorem convex_sets_are_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes "compact K" and "convex K" and "interior K \<noteq> {}"
  shows "expandable K"
  by (rule convex_expandable[OF assms])


section \<open>The literal reading of Eq. (1.5)\<close>

text \<open>Read with idempotent rather than orthogonal-projection \<open>P\<close>, Eq. (1.5) takes
  its infimum over the following set.\<close>

definition Pi_lit_set :: "real^'n::finite^'n \<Rightarrow> nat \<Rightarrow> real set" where
  "Pi_lit_set a m = {trace (a ** P) | P. P ** P = P \<and> trace P = real m}"

text \<open>The identity satisfies the literal constraint, so the literal \<open>S\<close> is not
  empty.\<close>

theorem literal_reading_keeps_identity:
  "\<forall>m. k < m \<longrightarrow> m \<le> CARD('n::finite) \<longrightarrow>
      (\<forall>t \<in> Pi_lit_set (mat 1 :: real^'n^'n) m. real (m - k) \<le> t)"
  by (auto simp: Pi_lit_set_def)

(*<*)
lemma outer_prod_mult_right:
  fixes A :: "real^'n::finite^'n"
  shows "outer_prod u v ** A = outer_prod u (v v* A)"
  by (simp add: outer_prod_def matrix_matrix_mult_def vector_matrix_mult_def
      vec_eq_iff sum_distrib_left mult_ac)

lemma outer_prod_zero_left [simp]: "outer_prod 0 v = 0"
  and outer_prod_zero_right [simp]: "outer_prod u 0 = 0"
  by (simp_all add: outer_prod_def vec_eq_iff)

text \<open>Adding a rank-one term \<open>u v\<^sup>T\<close> with \<open>v \<bullet> u = 1\<close> to an idempotent \<open>D\<close>
  that annihilates \<open>u\<close> on the right and \<open>v\<^sup>T\<close> on the left keeps it idempotent
  (oblique, not necessarily orthogonal, projection).\<close>

lemma idempotent_add_outer_prod:
  fixes D :: "real^'n::finite^'n"
  assumes DD: "D ** D = D" and Du: "D *v u = 0" and vD: "v v* D = 0"
    and vu: "v \<bullet> u = 1"
  shows "(D + outer_prod u v) ** (D + outer_prod u v) = D + outer_prod u v"
proof -
  have "(D + outer_prod u v) ** (D + outer_prod u v)
      = (D ** D + outer_prod u v ** D) + (D ** outer_prod u v + outer_prod u v ** outer_prod u v)"
    by (simp only: matrix_add_ldistrib matrix_add_rdistrib)
  also have "\<dots> = D + outer_prod u v"
    by (simp add: mult_outer_prod outer_prod_mult_right outer_prod_mult DD Du vD vu)
  finally show ?thesis .
qed

lemma trace_add_outer_prod:
  fixes D :: "real^'n::finite^'n"
  shows "trace (D + outer_prod u v) = trace D + v \<bullet> u"
  by (simp add: trace_add inner_commute)

text \<open>The diagonal 0/1 matrix selecting the coordinates in \<open>J\<close>.\<close>

definition coord_proj :: "'n::finite set \<Rightarrow> real^'n^'n" where
  "coord_proj J = (\<chi> r s. if r = s \<and> r \<in> J then 1 else 0)"

lemma coord_proj_idem: "coord_proj J ** coord_proj J = coord_proj (J :: 'n::finite set)"
proof -
  have "(\<Sum>k\<in>UNIV. (if r = k \<and> r \<in> J then 1 else 0) * (if k = s \<and> k \<in> J then 1 else 0))
      = (if r = s \<and> r \<in> J then 1 else (0::real))" for r s :: 'n
  proof -
    have "(\<Sum>k\<in>UNIV. (if r = k \<and> r \<in> J then 1 else 0) * (if k = s \<and> k \<in> J then 1 else 0))
        = (\<Sum>k\<in>UNIV. if k = r then (if r = s \<and> r \<in> J then 1 else 0) else (0::real))"
      by (intro sum.cong refl) auto
    then show ?thesis by simp
  qed
  then show ?thesis
    by (simp add: coord_proj_def matrix_matrix_mult_def vec_eq_iff)
qed

lemma trace_coord_proj: "trace (coord_proj J) = real (card J)"
  by (simp add: coord_proj_def trace_def flip: sum.inter_restrict)

lemma coord_proj_mv:
  assumes "\<forall>k\<in>J. u $ k = 0"
  shows "coord_proj J *v u = 0"
  unfolding vec_eq_iff
proof
  fix r
  have "(\<Sum>s\<in>UNIV. (if r = s \<and> r \<in> J then 1 else 0) * u $ s) = 0"
    using assms by (intro sum.neutral) auto
  then show "(coord_proj J *v u) $ r = 0 $ r"
    by (simp add: coord_proj_def matrix_vector_mult_def)
qed

lemma coord_proj_vm:
  assumes "\<forall>k\<in>J. v $ k = 0"
  shows "v v* coord_proj J = 0"
  unfolding vec_eq_iff
proof
  fix s
  have "(\<Sum>r\<in>UNIV. v $ r * (if r = s \<and> r \<in> J then 1 else 0)) = 0"
    using assms by (intro sum.neutral) auto
  then show "(v v* coord_proj J) $ s = 0 $ s"
    by (simp add: coord_proj_def vector_matrix_mult_def)
qed

text \<open>The family \<open>P\<^sub>t = coord_proj J + u (z + t w)\<^sup>T\<close> consists of idempotents of
  trace \<open>card J + 1\<close>, and \<open>trace (a ** P\<^sub>t)\<close> is affine in \<open>t\<close> with slope
  \<open>w \<bullet> (a *v u) \<noteq> 0\<close>.\<close>

lemma Pi_lit_set_unbounded_witness:
  fixes a :: "real^'n::finite^'n" and u z w :: "real^'n"
  assumes zu: "z \<bullet> u = 1" and wu: "w \<bullet> u = 0" and wau: "w \<bullet> (a *v u) \<noteq> 0"
    and uJ: "\<forall>k\<in>J. u $ k = 0" and zJ: "\<forall>k\<in>J. z $ k = 0" and wJ: "\<forall>k\<in>J. w $ k = 0"
    and cardJ: "card J + 1 = m"
  shows "\<not> bdd_below (Pi_lit_set a m)"
proof
  define D where "D = coord_proj J"
  define d where "d = w \<bullet> (a *v u)"
  define c where "c = trace (a ** D) + z \<bullet> (a *v u)"
  have mem: "c + t * d \<in> Pi_lit_set a m" for t
  proof -
    define v where "v = z + t *\<^sub>R w"
    have vJ: "\<forall>k\<in>J. v $ k = 0"
      using zJ wJ by (simp add: v_def)
    have vu: "v \<bullet> u = 1"
      using zu wu by (simp add: v_def inner_add_left)
    have idem: "(D + outer_prod u v) ** (D + outer_prod u v) = D + outer_prod u v"
      unfolding D_def
      by (rule idempotent_add_outer_prod[OF coord_proj_idem coord_proj_mv[OF uJ]
            coord_proj_vm[OF vJ] vu])
    have tr: "trace (D + outer_prod u v) = real m"
      using cardJ vu by (simp add: trace_add_outer_prod D_def trace_coord_proj)
    have "trace (a ** (D + outer_prod u v)) = trace (a ** D) + v \<bullet> (a *v u)"
      by (simp add: matrix_add_ldistrib trace_add mult_outer_prod inner_commute)
    also have "\<dots> = c + t * d"
      by (simp add: c_def d_def v_def inner_add_left)
    finally have "trace (a ** (D + outer_prod u v)) = c + t * d" .
    with idem tr show ?thesis
      unfolding Pi_lit_set_def by (intro CollectI exI[of _ "D + outer_prod u v"]) simp
  qed
  assume "bdd_below (Pi_lit_set a m)"
  then obtain M where M: "\<And>x. x \<in> Pi_lit_set a m \<Longrightarrow> M \<le> x"
    unfolding bdd_below_def by blast
  have "d \<noteq> 0" using wau by (simp add: d_def)
  then have "c + ((M - c - 1) / d) * d = M - 1"
    by simp
  with M[OF mem[of "(M - c - 1) / d"]] show False
    by simp
qed

text \<open>A matrix that is not a scalar multiple of the identity admits vectors
  \<open>u, z, w\<close> supported on two coordinates with \<open>z \<bullet> u = 1\<close>, \<open>w \<bullet> u = 0\<close>
  and \<open>w \<bullet> (a *v u) \<noteq> 0\<close>.  No symmetry of \<open>a\<close> is needed.\<close>

lemma non_scalar_witness:
  fixes a :: "real^'n::finite^'n"
  assumes ns: "\<forall>c. a \<noteq> c *\<^sub>R mat 1"
  obtains i j :: 'n and u z w :: "real^'n"
  where "i \<noteq> j" "z \<bullet> u = 1" "w \<bullet> u = 0" "w \<bullet> (a *v u) \<noteq> 0"
    "\<forall>k. k \<noteq> i \<longrightarrow> k \<noteq> j \<longrightarrow> u $ k = 0 \<and> z $ k = 0 \<and> w $ k = 0"
proof (cases "\<exists>i j. i \<noteq> j \<and> a $ i $ j \<noteq> 0")
  case True
  then obtain i j where ij: "i \<noteq> j" "a $ i $ j \<noteq> 0" by blast
  show ?thesis
  proof (rule that[OF ij(1), where u = "axis j 1" and z = "axis j 1" and w = "axis i 1"])
    show "axis j 1 \<bullet> axis j (1::real) = 1"
      by (simp add: inner_axis_axis)
    show "axis i 1 \<bullet> axis j (1::real) = 0"
      using ij by (simp add: inner_axis_axis)
    show "axis i 1 \<bullet> (a *v axis j 1) \<noteq> 0"
      using ij by (simp add: inner_axis_one matrix_vector_axis_one)
    show "\<forall>k. k \<noteq> i \<longrightarrow> k \<noteq> j \<longrightarrow>
        axis j 1 $ k = 0 \<and> axis j 1 $ k = 0 \<and> axis i (1::real) $ k = 0"
      by (simp add: axis_def)
  qed
next
  case False
  then have off: "\<And>i j. i \<noteq> j \<Longrightarrow> a $ i $ j = 0" by blast
  obtain i j where ij: "a $ i $ i \<noteq> a $ j $ j"
  proof -
    obtain i0 :: 'n where True by blast
    have "\<exists>i j. a $ i $ i \<noteq> a $ j $ j"
    proof (rule ccontr)
      assume "\<not> (\<exists>i j. a $ i $ i \<noteq> a $ j $ j)"
      then have "a = (a $ i0 $ i0) *\<^sub>R mat 1"
        using off by (auto simp: vec_eq_iff mat_def)
      with ns show False by blast
    qed
    then show ?thesis using that by blast
  qed
  then have "i \<noteq> j" by blast
  show ?thesis
  proof (rule that[OF \<open>i \<noteq> j\<close>, where u = "axis i 1 + axis j 1" and z = "axis i 1"
        and w = "axis i 1 - axis j 1"])
    show "axis i 1 \<bullet> (axis i 1 + axis j (1::real)) = 1"
      using \<open>i \<noteq> j\<close> by (simp add: inner_add_right inner_axis_axis)
    show "(axis i 1 - axis j 1) \<bullet> (axis i 1 + axis j (1::real)) = 0"
      using \<open>i \<noteq> j\<close> by (simp add: inner_add_right inner_diff_left inner_axis_axis)
    show "(axis i 1 - axis j 1) \<bullet> (a *v (axis i 1 + axis j (1::real))) \<noteq> 0"
      using ij off[OF \<open>i \<noteq> j\<close>] off[of j i] \<open>i \<noteq> j\<close>
      by (simp add: matrix_vector_right_distrib inner_diff_left inner_axis_one
          matrix_vector_axis_one)
    show "\<forall>k. k \<noteq> i \<longrightarrow> k \<noteq> j \<longrightarrow> (axis i 1 + axis j (1::real)) $ k = 0 \<and>
        axis i (1::real) $ k = 0 \<and> (axis i 1 - axis j (1::real)) $ k = 0"
      by (simp add: axis_def)
  qed
qed

(*>*)

text \<open>Under the literal reading of Eq. (1.5) (idempotent \<open>P\<close>, not necessarily
  symmetric), the infimum is \<open>-\<infinity>\<close> for every non-scalar \<open>a\<close> and every
  \<open>1 \<le> m < n\<close>.  Symmetry of \<open>a\<close> is not needed.  The remaining hypotheses are
  necessary: for \<open>m = 0\<close> the only idempotent of trace 0 is \<open>0\<close>, for \<open>m = n\<close>
  the only one of full trace is the identity, and for \<open>a = c *\<^sub>R mat 1\<close> the
  set is contained in \<open>{c * m}\<close> (these remarks are not formalised here).\<close>

theorem literal_reading_unbounded:
  fixes a :: "real^'n::finite^'n"
  assumes ns: "\<forall>c. a \<noteq> c *\<^sub>R mat 1" and m1: "1 \<le> m" and mn: "m < CARD('n)"
  shows "\<not> bdd_below (Pi_lit_set a m)"
proof -
  obtain i j u z w where ij: "i \<noteq> j" and zu: "z \<bullet> u = 1" and wu: "w \<bullet> u = 0"
    and wau: "w \<bullet> (a *v u) \<noteq> 0"
    and supp: "\<forall>k. k \<noteq> i \<longrightarrow> k \<noteq> j \<longrightarrow> u $ k = 0 \<and> z $ k = 0 \<and> w $ k = 0"
    by (rule non_scalar_witness[OF ns])
  have "card (UNIV - {i, j} :: 'n set) = CARD('n) - 2"
    using ij by (simp add: card_Diff_subset)
  then have "m - 1 \<le> card (UNIV - {i, j} :: 'n set)"
    using mn by arith
  then obtain J where J: "J \<subseteq> UNIV - {i, j}" "card J = m - 1"
    by (rule obtain_subset_with_card_n)
  show ?thesis
  proof (rule Pi_lit_set_unbounded_witness[OF zu wu wau, of J])
    show "\<forall>k\<in>J. u $ k = 0" "\<forall>k\<in>J. z $ k = 0" "\<forall>k\<in>J. w $ k = 0"
      using J(1) supp by auto
    show "card J + 1 = m"
      using J(2) m1 by simp
  qed
qed

text \<open>So whenever some \<open>m\<close> with \<open>k < m < n\<close> exists, i.e.\ for \<open>k \<le> n - 2\<close>, the
  literal constraint set contains only multiples of the identity, and Lemma 2.1
  fails for it.  The orthogonal reading is the one under which Lemma 2.1 holds.\<close>

(*<*)
end
(*>*)
