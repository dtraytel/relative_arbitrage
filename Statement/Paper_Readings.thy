section \<open>Readings of the paper's wording, checked\<close>

(*<*)
theory Paper_Readings
  imports Theorem_1_1_Statement
begin
(*>*)

text \<open>Three places in \<^cite>\<open>LaiShkolnikovSoner\<close> admit more than one reading, and
  the formalisation had to commit to one.  This theory settles what turns on
  each choice, so that the commitments are checkable rather than asserted.\<close>

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

(*<*)
end
(*>*)
