
(*<*)
theory Operator_Continuity
  imports
    "Symmetric_Matrix_Spectra.Ky_Fan" "Symmetric_Matrix_Spectra.Orthogonal_Projections"
begin

(*>*)

text \<open>
  Formalizes Eqs. (3.4)-(3.6) of \<^cite>\<open>LaiShkolnikovSoner\<close>: the matrix \<open>M\<^sub>p\<close>,
  the closed formula (3.5) for \<open>F\<close>, and Lemma 3.1. For \<open>p \<noteq> 0\<close>,
  Eq. (3.4) defines

    \<open>M\<^sub>p = (I - p p\<^sup>T / \<bar>p\<bar>\<^sup>2) M (I - p p\<^sup>T / \<bar>p\<bar>\<^sup>2)
       + min (lambda\<^sub>n(M), 0) \<bullet> p p\<^sup>T / \<bar>p\<bar>\<^sup>2\<close>

  and \<open>M\<^sub>0 = M\<close>; this is an \<open>n \<times> n\<close> matrix, with no change of dimension,
  and the correction term is chosen so that this eigenvalue sorts to the
  bottom of the spectrum of \<open>M\<^sub>p\<close>, which is what makes Eq. (3.5) a clean
  sum over \<open>i = 1..n\<close>. Since \<open>M\<^sub>p\<close> has the same trace pairing as \<open>M\<close>
  against every feasible \<open>a\<close>, \<open>F(p, M) = F(p, M\<^sub>p)\<close>, while \<open>M\<^sub>p\<close> is
  diagonalisable in a way adapted to \<open>p\<close>.\<close>
section \<open>Elementary matrix algebra not already in the development\<close>

text \<open>\<open>trace_conjugate\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>scaleR_matrix_matrix_left\<close> is HOL-Analysis's \<open>scalar_matrix_assoc\<close>, reversed.\<close>

text \<open>\<open>trace_scaleR_matrix\<close> is \<open>trace_scaleR\<close> from
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

section \<open>The matrix \<open>M\<^sub>p\<close> of Eq. (3.4)\<close>

definition Mp :: "real^'n::finite \<Rightarrow> real^'n^'n \<Rightarrow> real^'n^'n" where
  "Mp p M =
     (if p = 0 then M
      else (mat 1 - rank1proj p) ** M ** (mat 1 - rank1proj p)
           + min (eigval CARD('n) M) 0 *\<^sub>R rank1proj p)"

lemma Mp_zero [simp]: "Mp 0 M = M"
  by (simp add: Mp_def)


lemma Mp_apply_p:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0"
  shows "Mp p M *v p = min (eigval CARD('n) M) 0 *\<^sub>R p"
proof -
  define Q where "Q = (mat 1 - rank1proj p :: real^'n^'n)"
  define c where "c = min (eigval CARD('n) M) 0"
  have Qp: "Q *v p = 0"
    unfolding Q_def
    by (simp add: matrix_vector_mult_diff_rdistrib rank1proj_apply_self[OF p])
  have conj: "(Q ** M ** Q) *v p = 0"
  proof -
    have "(Q ** M ** Q) *v p = Q *v (M *v (Q *v p))"
      by (simp add: matrix_vector_mul_assoc matrix_mul_assoc)
    also have "\<dots> = 0"
      by (simp add: Qp)
    finally show ?thesis .
  qed
  have corr: "(c *\<^sub>R rank1proj p) *v p = c *\<^sub>R p"
    by (simp add: scaleR_matrix_vector_assoc[symmetric]
        rank1proj_apply_self[OF p])
  have MpQ: "Mp p M = Q ** M ** Q + c *\<^sub>R rank1proj p"
    unfolding Mp_def Q_def c_def using p by simp
  have "Mp p M *v p = (Q ** M ** Q) *v p + (c *\<^sub>R rank1proj p) *v p"
    unfolding MpQ by (rule matrix_vector_mult_add_rdistrib)
  also have "\<dots> = c *\<^sub>R p"
    using conj corr by simp
  finally show ?thesis
    unfolding c_def .
qed

text \<open>Consequently \<open>M\<^sub>p\<close> is symmetric whenever \<open>M\<close> is, which every
  eigenvalue lemma in @{theory Symmetric_Matrix_Spectra.Ky_Fan} requires as a
  hypothesis.\<close>

lemma transpose_Mp:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M"
  shows "transpose (Mp p M) = Mp p M"
proof (cases "p = 0")
  case True
  then show ?thesis using sym by simp
next
  case False
  have symQ: "transpose (mat 1 - rank1proj p :: real^'n^'n) = mat 1 - rank1proj p"
    by (rule symmetric_perp_proj)
  have conj: "transpose ((mat 1 - rank1proj p) ** M ** (mat 1 - rank1proj p))
      = (mat 1 - rank1proj p) ** M ** (mat 1 - rank1proj p)"
    by (simp add: matrix_transpose_mul matrix_mul_assoc symQ sym)
  have corr: "transpose (min (eigval CARD('n) M) 0 *\<^sub>R rank1proj p)
      = min (eigval CARD('n) M) 0 *\<^sub>R rank1proj p"
    by (simp add: transpose_scalar transpose_rank1proj)
  show ?thesis
    unfolding Mp_def using False
    by (simp add: transpose_add conj corr)
qed

text \<open>The defining property: \<open>M\<^sub>p\<close> pairs with every feasible \<open>a\<close> exactly as
  \<open>M\<close> does.  Both summands are invisible: the conjugation because \<open>a\<close> is
  supported on \<open>p\<^sup>\<bottom>\<close>, the correction term because
  \<open>tr(p p\<^sup>\<top> a) = p \<bullet> (a p) = 0\<close>.  This is the sentence in the paper just
  before Eq. (3.5).\<close>

theorem trace_Mp:
  fixes M a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and ap: "a *v p = 0"
  shows "trace (Mp p M ** a) = trace (M ** a)"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  define Q where "Q = (mat 1 - rank1proj p :: real^'n^'n)"
  define c where "c = min (eigval CARD('n) M) 0"
  have symQ: "transpose Q = Q"
    unfolding Q_def by (rule symmetric_perp_proj)
  have MpQ: "Mp p M = Q ** M ** Q + c *\<^sub>R rank1proj p"
    unfolding Mp_def Q_def c_def using False by simp
  have QaQ: "Q ** a ** Q = a"
  proof -
    have "Q ** a = a"
      unfolding Q_def by (rule proj_perp_left[OF sym ap])
    then show ?thesis
      unfolding Q_def by (simp add: proj_perp_right[OF sym ap])
  qed
  have conj: "trace ((Q ** M ** Q) ** a) = trace (M ** a)"
  proof -
    have "trace (M ** (transpose Q ** a ** Q)) = trace ((Q ** M ** transpose Q) ** a)"
      by (rule trace_conjugate)
    then have "trace (M ** (Q ** a ** Q)) = trace ((Q ** M ** Q) ** a)"
      by (simp add: symQ)
    then show ?thesis
      by (simp add: QaQ)
  qed
  have corr: "trace ((c *\<^sub>R rank1proj p) ** a) = 0"
    by (simp add: scalar_matrix_assoc[symmetric] trace_scaleR
        trace_rank1proj_mult[OF ap])
  have "trace (Mp p M ** a)
      = trace ((Q ** M ** Q) ** a) + trace ((c *\<^sub>R rank1proj p) ** a)"
    unfolding MpQ by (simp add: matrix_add_rdistrib trace_add)
  also have "\<dots> = trace (M ** a)"
    using conj corr by simp
  finally show ?thesis .
qed

text \<open>Hence \<open>F\<close> does not distinguish \<open>M\<close> from \<open>M\<^sub>p\<close>.\<close>

(*<*)
end
(*>*)
