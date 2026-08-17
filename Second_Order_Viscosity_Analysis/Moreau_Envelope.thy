section \<open>The Moreau envelope\<close>

(*<*)
theory Moreau_Envelope
  imports Rademacher
begin

(*>*)

subsection \<open>The resolvent is differentiable almost everywhere\<close>

text \<open>The proximal map is 1-Lipschitz (\<open>prox_nonexpansive\<close>), so
  Rademacher applies; its differentiability substitutes for second-order
  differentiability of \<open>f\<close> (Minty's device), with \<open>prox_subdiff\<close> the
  bridge back.\<close>

lemma prox_lipschitz:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "norm (prox f y - prox f z) \<le> 1 * norm (y - z)"
proof -
  have "dist (prox f y) (prox f z) \<le> dist y z"
    by (rule prox_nonexpansive[OF cvx])
  thus ?thesis by (simp add: dist_norm)
qed

theorem prox_differentiable_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. (prox f) differentiable (at x)"
  by (rule rademacher_vec_AE[where B = 1]) (rule prox_lipschitz[OF cvx])

text \<open>The resolvent is a globally defined, surjective, 1-Lipschitz map
  differentiable a.e.; Alexandrov's theorem transports that derivative
  back through \<open>prox_subdiff\<close>.\<close>

subsection \<open>Firm nonexpansiveness and the derivative of the resolvent\<close>

text \<open>The resolvent is firmly nonexpansive,
  \<open>|R x - R y|\<^sup>2 \<le> (x - y) \<cdot> (R x - R y)\<close>; differentiating along a line
  makes its derivative positive semidefinite with norm at most one.\<close>

lemma prox_firm_nonexpansive:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "(norm (prox f x - prox f y))\<^sup>2 \<le> (x - y) \<bullet> (prox f x - prox f y)"
proof -
  have s1: "x - prox f x \<in> subdiff f (prox f x)" by (rule prox_subdiff[OF cvx])
  have s2: "y - prox f y \<in> subdiff f (prox f y)" by (rule prox_subdiff[OF cvx])
  have mono: "0 \<le> ((x - prox f x) - (y - prox f y)) \<bullet> (prox f x - prox f y)"
    by (rule subdiff_monotone[OF s1 s2])
  show ?thesis
    using mono by (simp add: power2_norm_eq_inner inner_commute algebra_simps)
qed

lemma has_derivative_dir_limit:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes D: "(F has_derivative D) (at x)"
  shows "((\<lambda>t. (F (x + t *\<^sub>R h) - F x) /\<^sub>R t) \<longlongrightarrow> D h) (at (0::real))"
proof (cases "h = 0")
  case True
  have lin: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have "D 0 = 0" using lin by (simp add: linear_simps(3))
  thus ?thesis unfolding True by simp
next
  case False
  have lin: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have Dlin: "linear D" using lin unfolding bounded_linear_def by simp
  have Dsc: "D (t *\<^sub>R h) = t *\<^sub>R D h" for t
    using Dlin unfolding linear_iff by simp
  have lim0: "((\<lambda>u. norm (F (x + u) - F x - D u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using D unfolding has_derivative_at by blast
  have flim: "filterlim (\<lambda>t::real. t *\<^sub>R h) (at 0) (at 0)"
    unfolding filterlim_at
  proof (intro conjI)
    have "((\<lambda>t::real. t *\<^sub>R h) \<longlongrightarrow> 0 *\<^sub>R h) (at 0)" by (intro tendsto_intros)
    thus "((\<lambda>t::real. t *\<^sub>R h) \<longlongrightarrow> 0) (at 0)" by simp
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus "eventually (\<lambda>t::real. t *\<^sub>R h \<in> UNIV \<and> t *\<^sub>R h \<noteq> 0) (at 0)"
      by (rule eventually_mono) (use False in simp)
  qed
  have comp: "((\<lambda>t. norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) \<longlongrightarrow> 0) (at (0::real))"
    by (rule filterlim_compose[OF lim0 flim])
  have scaled: "((\<lambda>t. (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) * norm h) \<longlongrightarrow> 0 * norm h) (at (0::real))"
    by (intro tendsto_mult comp tendsto_const)
  have ev: "eventually (\<lambda>t. norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)
      = (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) / norm (t *\<^sub>R h)) * norm h)
      (at (0::real))"
  proof -
    have "eventually (\<lambda>t::real. t \<noteq> 0) (at 0)"
      unfolding eventually_at by (intro exI[of _ 1]) auto
    thus ?thesis
    proof (eventually_elim)
      case (elim t)
      hence t: "t \<noteq> 0" .
      have "(F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h
          = (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) /\<^sub>R t"
        using t by (simp add: Dsc scaleR_diff_right)
      hence "norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)
          = norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h)) / \<bar>t\<bar>"
        by (simp add: divide_inverse mult.commute)
      also have "\<dots> = (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
          / norm (t *\<^sub>R h)) * norm h"
        using t False by (simp add: field_simps)
      finally show ?case .
    qed
  qed
  have ev': "eventually (\<lambda>t. (norm (F (x + t *\<^sub>R h) - F x - D (t *\<^sub>R h))
      / norm (t *\<^sub>R h)) * norm h
      = norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h)) (at (0::real))"
    using ev by (rule eventually_mono) simp
  have "((\<lambda>t. norm ((F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h))
      \<longlongrightarrow> 0) (at (0::real))"
    using scaled ev' by (simp add: Lim_transform_eventually)
  hence "((\<lambda>t. (F (x + t *\<^sub>R h) - F x) /\<^sub>R t - D h) \<longlongrightarrow> 0) (at 0)"
    by (simp add: tendsto_norm_zero_iff)
  thus ?thesis by (simp add: Lim_null[symmetric])
qed

text \<open>Wherever the resolvent is differentiable, its derivative \<open>DR\<close>
  satisfies \<open>|DR h|\<^sup>2 \<le> h \<cdot> DR h\<close>, so \<open>DR\<close> is positive semidefinite with
  \<open>\<parallel>DR\<parallel> \<le> 1\<close> \<comment> \<open>equivalently \<open>I - DR\<close> is positive
  semidefinite as well\<close>\<close>

theorem prox_deriv_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "(norm (D h))\<^sup>2 \<le> h \<bullet> D h"
proof -
  define q where "q = (\<lambda>t. (prox f (x + t *\<^sub>R h) - prox f x) /\<^sub>R t)"
  have qlim: "(q \<longlongrightarrow> D h) (at (0::real))"
    unfolding q_def by (rule has_derivative_dir_limit[OF D])
  have est: "(norm (q t))\<^sup>2 \<le> h \<bullet> q t" if t: "0 < t" for t
  proof -
    have firm: "(norm (prox f (x + t *\<^sub>R h) - prox f x))\<^sup>2
        \<le> ((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)"
      by (rule prox_firm_nonexpansive[OF cvx])
    have qeq: "q t = (1/t) *\<^sub>R (prox f (x + t *\<^sub>R h) - prox f x)"
      unfolding q_def by (simp add: divide_inverse)
    have lhs: "(norm (q t))\<^sup>2
        = (norm (prox f (x + t *\<^sub>R h) - prox f x))\<^sup>2 / t\<^sup>2"
      unfolding qeq using t
      by (simp add: power_divide power_mult_distrib power_inverse divide_inverse)
    have rhs: "h \<bullet> q t
        = (((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)) / t\<^sup>2"
    proof -
      have "h \<bullet> q t = (1/t) * (h \<bullet> (prox f (x + t *\<^sub>R h) - prox f x))"
        unfolding qeq by simp
      moreover have "((x + t *\<^sub>R h) - x) \<bullet> (prox f (x + t *\<^sub>R h) - prox f x)
          = t * (h \<bullet> (prox f (x + t *\<^sub>R h) - prox f x))" by simp
      ultimately show ?thesis using t by (simp add: power2_eq_square)
    qed
    show ?thesis unfolding lhs rhs
      using firm t by (intro divide_right_mono) auto
  qed
  have ev: "eventually (\<lambda>t. (norm (q t))\<^sup>2 \<le> h \<bullet> q t) (at_right (0::real))"
    unfolding eventually_at_right_field
    by (intro exI[of _ 1]) (use est in auto)
  have l1: "((\<lambda>t. (norm (q t))\<^sup>2) \<longlongrightarrow> (norm (D h))\<^sup>2)
      (at_right (0::real))"
    by (intro tendsto_intros tendsto_norm filterlim_mono[OF qlim])
      (auto simp: at_le)
  have l2: "((\<lambda>t. h \<bullet> q t) \<longlongrightarrow> h \<bullet> D h) (at_right (0::real))"
    by (intro tendsto_inner tendsto_const filterlim_mono[OF qlim])
      (auto simp: at_le)
  show ?thesis
    by (rule tendsto_le[OF _ l2 l1]) (use ev in auto)
qed

subsection \<open>The Moreau envelope and its gradient\<close>

text \<open>The envelope \<open>e f x = min\<^sub>y (f y + |x - y|\<^sup>2/2)\<close> is everywhere
  differentiable with gradient \<open>x - prox f x\<close> and quadratic error, so
  \<open>e\<close> is \<open>C\<^sup>1\<close> with a 1-Lipschitz gradient --- the resolvent is \<open>id\<close>
  minus a gradient field.\<close>

definition moreau :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real"
  where "moreau f x = f (prox f x) + (dist x (prox f x))\<^sup>2 / 2"

lemma moreau_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f x \<le> f z + (dist x z)\<^sup>2 / 2"
  unfolding moreau_def by (rule prox_min[OF cvx])

lemma moreau_upper:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f (x + h) \<le> moreau f x + h \<bullet> (x - prox f x) + (norm h)\<^sup>2 / 2"
proof -
  have "moreau f (x + h) \<le> f (prox f x) + (dist (x + h) (prox f x))\<^sup>2 / 2"
    by (rule moreau_le[OF cvx])
  moreover have "(dist (x + h) (prox f x))\<^sup>2
      = (dist x (prox f x))\<^sup>2 + 2 * (h \<bullet> (x - prox f x)) + (norm h)\<^sup>2"
    unfolding dist_norm power2_norm_eq_inner
    by (simp add: algebra_simps inner_commute)
  ultimately show ?thesis unfolding moreau_def by linarith
qed

lemma moreau_lower:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f x \<le> moreau f (x + h) - h \<bullet> (x + h - prox f (x + h))
      + (norm h)\<^sup>2 / 2"
proof -
  have "moreau f x \<le> f (prox f (x + h)) + (dist x (prox f (x + h)))\<^sup>2 / 2"
    by (rule moreau_le[OF cvx])
  moreover have "(dist x (prox f (x + h)))\<^sup>2
      = (dist (x + h) (prox f (x + h)))\<^sup>2
        - 2 * (h \<bullet> (x + h - prox f (x + h))) + (norm h)\<^sup>2"
    unfolding dist_norm power2_norm_eq_inner
    by (simp add: algebra_simps inner_commute)
  ultimately show ?thesis unfolding moreau_def by linarith
qed

theorem moreau_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "(moreau f has_derivative (\<lambda>h. h \<bullet> (x - prox f x))) (at x)"
  unfolding has_derivative_at
proof (intro conjI)
  show "bounded_linear (\<lambda>h. h \<bullet> (x - prox f x))"
    by (rule bounded_linear_inner_left)
  have quad: "norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
      \<le> (5/2) * (norm h)\<^sup>2" for h
  proof -
    have up: "moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        \<le> (norm h)\<^sup>2 / 2"
      using moreau_upper[OF cvx, of x h] by simp
    have "moreau f x \<le> moreau f (x + h) - h \<bullet> (x + h - prox f (x + h))
        + (norm h)\<^sup>2 / 2"
      by (rule moreau_lower[OF cvx])
    hence lo0: "moreau f (x + h) - moreau f x
        \<ge> h \<bullet> (x + h - prox f (x + h)) - (norm h)\<^sup>2 / 2" by simp
    have split: "h \<bullet> (x + h - prox f (x + h))
        = h \<bullet> (x - prox f x) + h \<bullet> (h + prox f x - prox f (x + h))"
      by (simp add: algebra_simps)
    have bnd: "\<bar>h \<bullet> (h + prox f x - prox f (x + h))\<bar>
        \<le> 2 * (norm h)\<^sup>2"
    proof -
      have assoc: "h + prox f x - prox f (x + h)
          = h + (prox f x - prox f (x + h))" by simp
      have "norm (h + prox f x - prox f (x + h))
          \<le> norm h + norm (prox f x - prox f (x + h))"
        unfolding assoc by (rule norm_triangle_ineq)
      moreover have "norm (prox f x - prox f (x + h)) \<le> norm h"
        using prox_lipschitz[OF cvx, of x "x + h"] by simp
      ultimately have "norm (h + prox f x - prox f (x + h)) \<le> 2 * norm h"
        by linarith
      hence "\<bar>h \<bullet> (h + prox f x - prox f (x + h))\<bar>
          \<le> norm h * (2 * norm h)"
        using Cauchy_Schwarz_ineq2[of h "h + prox f x - prox f (x + h)"]
        by (smt (verit) mult_left_mono norm_ge_zero)
      thus ?thesis by (simp add: power2_eq_square)
    qed
    have lo: "moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        \<ge> - (5/2) * (norm h)\<^sup>2" using lo0 split bnd by (simp add: abs_le_iff)
    have nn: "0 \<le> (norm h)\<^sup>2" by simp
    show ?thesis unfolding real_norm_def using up lo nn by linarith
  qed
  have "((\<lambda>h. norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
      / norm h) \<longlongrightarrow> 0) (at 0)"
  proof (rule Lim_transform_bound[where g = "\<lambda>h :: 'a. (5/2) * norm h"])
    show "((\<lambda>h :: 'a. (5/2) * norm h) \<longlongrightarrow> 0) (at 0)"
    proof -
      have "((\<lambda>h :: 'a. (5/2) * norm h) \<longlongrightarrow> (5/2) * norm (0 :: 'a)) (at 0)"
        by (intro tendsto_intros)
      thus ?thesis by simp
    qed
    show "eventually (\<lambda>h :: 'a. norm (norm (moreau f (x + h) - moreau f x
        - h \<bullet> (x - prox f x)) / norm h) \<le> norm ((5/2) * norm h)) (at 0)"
    proof (rule always_eventually, rule allI)
      fix h :: 'a
      show "norm (norm (moreau f (x + h) - moreau f x
          - h \<bullet> (x - prox f x)) / norm h) \<le> norm ((5/2) * norm h)"
      proof (cases "h = 0")
        case True thus ?thesis by simp
      next
        case False
        have "norm (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x))
            / norm h \<le> ((5/2) * (norm h)\<^sup>2) / norm h"
          using quad[of h] False by (intro divide_right_mono) auto
        also have "\<dots> = (5/2) * norm h"
          using False by (simp add: power2_eq_square)
        finally show ?thesis using False by simp
      qed
    qed
  qed
  thus "((\<lambda>h. norm (moreau f (x + h) - moreau f x
      - h \<bullet> (x - prox f x)) / norm h) \<longlongrightarrow> 0) (at 0)" .
qed

subsection \<open>Second-order differentiability of the Moreau envelope\<close>

text \<open>The Moreau envelope of a finite convex function is twice
  differentiable a.e., with positive semidefinite Hessian \<open>I - DR\<close>,
  combining the everywhere-valid gradient formula with a.e.
  differentiability of the resolvent.\<close>

lemma prox_deriv_norm_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "norm (D h) \<le> norm h"
proof -
  have psd: "(norm (D h))\<^sup>2 \<le> h \<bullet> D h" by (rule prox_deriv_psd[OF cvx D])
  have cs: "h \<bullet> D h \<le> norm h * norm (D h)"
    using Cauchy_Schwarz_ineq2[of h "D h"] by linarith
  have "(norm (D h))\<^sup>2 \<le> norm h * norm (D h)" using psd cs by linarith
  thus ?thesis
    by (cases "D h = 0") (auto simp: power2_eq_square mult_le_cancel_right)
qed

lemma moreau_hessian_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "0 \<le> h \<bullet> (h - D h)"
proof -
  have "h \<bullet> D h \<le> norm h * norm (D h)"
    using Cauchy_Schwarz_ineq2[of h "D h"] by linarith
  also have "\<dots> \<le> norm h * norm h"
    using prox_deriv_norm_le[OF cvx D] by (intro mult_left_mono) auto
  also have "\<dots> = h \<bullet> h"
    by (simp add: power2_eq_square[symmetric] power2_norm_eq_inner)
  finally show ?thesis by (simp add: inner_diff_right)
qed

lemma moreau_grad_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>y. y - prox f y) has_derivative (\<lambda>h. h - D h)) (at x)"
  by (intro has_derivative_diff has_derivative_ident D)

theorem moreau_twice_differentiable_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A
      \<and> (\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y))
      \<and> ((\<lambda>y. y - prox f y) has_derivative A) (at x)
      \<and> (\<forall>h. 0 \<le> h \<bullet> A h)"
proof -
  have grad: "\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y)"
    using moreau_has_derivative[OF cvx] by blast
  show ?thesis
  proof (rule eventually_mono[OF prox_differentiable_AE[OF cvx]])
    fix x :: 'a assume "(prox f) differentiable (at x)"
    then obtain D where D: "(prox f has_derivative D) (at x)"
      unfolding differentiable_def by blast
    have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
    have blA: "bounded_linear (\<lambda>h. h - D h)"
      using blD by (intro bounded_linear_sub bounded_linear_ident)
    have hess: "((\<lambda>y. y - prox f y) has_derivative (\<lambda>h. h - D h)) (at x)"
      by (rule moreau_grad_has_derivative[OF D])
    have psd: "0 \<le> h \<bullet> (h - D h)" for h
      by (rule moreau_hessian_psd[OF cvx D])
    show "\<exists>A. bounded_linear A
        \<and> (\<forall>y. (moreau f has_derivative (\<lambda>h. h \<bullet> (y - prox f y))) (at y))
        \<and> ((\<lambda>y. y - prox f y) has_derivative A) (at x)
        \<and> (\<forall>h. 0 \<le> h \<bullet> A h)"
      using blA grad hess psd by blast
  qed
qed

subsection \<open>Integral representation of the envelope's increments\<close>

text \<open>The bridge to a genuine second-order Taylor expansion: since the
  envelope's gradient is known everywhere, the increment along a segment
  is its integral along the segment (fundamental theorem of calculus),
  and feeding in the gradient's first-order expansion produces the
  quadratic term.\<close>

lemma moreau_line_vector_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. moreau f (x + s *\<^sub>R h)) has_vector_derivative
      (h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))) (at s within T)"
proof -
  have inner': "((\<lambda>t. x + t *\<^sub>R h) has_derivative (\<lambda>t. t *\<^sub>R h)) (at s within T)"
    by (auto intro!: derivative_eq_intros)
  have outer: "(moreau f has_derivative
      (\<lambda>k. k \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))
      (at (x + s *\<^sub>R h) within (\<lambda>t. x + t *\<^sub>R h) ` T)"
    using moreau_has_derivative[OF cvx] by (rule has_derivative_at_withinI)
  have "((\<lambda>s. moreau f (x + s *\<^sub>R h)) has_derivative
      (\<lambda>t. (t *\<^sub>R h) \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))
      (at s within T)"
    by (rule diff_chain_within[OF inner' outer, unfolded comp_def])
  moreover have "(\<lambda>t. (t *\<^sub>R h) \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      = (\<lambda>t. t *\<^sub>R (h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h))))"
    by (rule ext) simp
  ultimately show ?thesis unfolding has_vector_derivative_def by simp
qed

theorem moreau_ftc:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      has_integral (moreau f (x + h) - moreau f x)) {0..1}"
proof -
  have "((\<lambda>s. h \<bullet> ((x + s *\<^sub>R h) - prox f (x + s *\<^sub>R h)))
      has_integral (moreau f (x + 1 *\<^sub>R h) - moreau f (x + 0 *\<^sub>R h))) {0..1}"
    by (rule fundamental_theorem_of_calculus)
      (auto intro!: moreau_line_vector_derivative[OF cvx])
  thus ?thesis by simp
qed

text \<open>Integrating the gradient's first-order expansion over the segment
  produces \<open>h \<cdot> G x + (h \<cdot> A h)/2\<close>, the factor \<open>1/2\<close> being exactly
  \<open>\<integral>\<^sub>0\<^sup>1 s ds\<close>.\<close>

lemma has_integral_affine_unit:
  fixes c d :: real
  shows "((\<lambda>s. c + s * d) has_integral (c + d/2)) {0..1}"
proof -
  have "((\<lambda>s. c + s * d) has_integral
      ((c * 1 + d * 1\<^sup>2 / 2) - (c * 0 + d * 0\<^sup>2 / 2))) {0..1}"
  proof (rule fundamental_theorem_of_calculus)
    show "(0::real) \<le> 1" by simp
    fix s :: real assume "s \<in> {0..1}"
    show "((\<lambda>s. c * s + d * s\<^sup>2 / 2) has_vector_derivative (c + s * d))
        (at s within {0..1})"
      unfolding has_vector_derivative_def
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma has_integral_gradient_model:
  fixes h :: "'a::euclidean_space"
  assumes A: "bounded_linear A"
  shows "((\<lambda>s. h \<bullet> (g + A (s *\<^sub>R h)))
      has_integral (h \<bullet> g + (h \<bullet> A h) / 2)) {0..1}"
proof -
  have lin: "linear A" using A unfolding bounded_linear_def by simp
  have pt: "h \<bullet> (g + A (s *\<^sub>R h)) = (h \<bullet> g) + s * (h \<bullet> A h)" for s
  proof -
    have "A (s *\<^sub>R h) = s *\<^sub>R A h" using lin unfolding linear_iff by simp
    thus ?thesis by (simp add: inner_add_right)
  qed
  have "((\<lambda>s. (h \<bullet> g) + s * (h \<bullet> A h))
      has_integral ((h \<bullet> g) + (h \<bullet> A h)/2)) {0..1}"
    by (rule has_integral_affine_unit)
  thus ?thesis by (simp add: pt)
qed

subsection \<open>Second-order Taylor expansion of the envelope\<close>

text \<open>The envelope's increment and the model quadratic are both integrals
  over the segment, differing pointwise by at most \<open>\<epsilon>\<parallel>h\<parallel>\<close> once
  \<open>\<parallel>h\<parallel>\<close> is small, uniformly since \<open>\<parallel>s h\<parallel> \<le> \<parallel>h\<parallel>\<close>; integrating over the
  unit interval keeps the bound.\<close>

theorem moreau_second_order_taylor:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  define e2 where "e2 = \<epsilon>/2"
  have e2: "0 < e2" using \<epsilon> by (simp add: e2_def)
  define G where "G = (\<lambda>y :: 'a. y - prox f y)"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have Gx: "G x = x - prox f x" by (simp add: G_def)
  have Ah: "A h = h - D h" for h by (simp add: A_def)
  have GA: "(G has_derivative A) (at x)"
    unfolding G_def A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A"
    by (rule has_derivative_bounded_linear[OF GA])
  have "((\<lambda>u. norm (G (x + u) - G x - A u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by blast
  from tendstoD[OF this e2] obtain \<delta> where \<delta>: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta>
      \<Longrightarrow> dist (norm (G (x + u) - G x - A u) / norm u) 0 < e2"
    unfolding eventually_at by blast
  have small: "norm (G (x + u) - G x - A u) \<le> e2 * norm u"
    if u: "norm u < \<delta>" for u
  proof (cases "u = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    have "norm (G (x + u) - G x - A u) / norm u < e2"
      using db[OF False] u by (simp add: dist_norm)
    thus ?thesis using False by (simp add: divide_less_eq)
  qed
  have main: "\<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar> \<le> e2"
    if h: "h \<noteq> 0" "norm h < \<delta>" for h
  proof -
    have i1: "((\<lambda>s. h \<bullet> G (x + s *\<^sub>R h))
        has_integral (moreau f (x + h) - moreau f x)) (cbox 0 1)"
      using moreau_ftc[OF cvx, of h x] unfolding G_def by simp
    have i2: "((\<lambda>s. h \<bullet> (G x + A (s *\<^sub>R h)))
        has_integral (h \<bullet> G x + (h \<bullet> A h) / 2)) (cbox 0 1)"
      using has_integral_gradient_model[OF blA, of h "G x"] by simp
    have i3: "((\<lambda>s. h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
        has_integral ((moreau f (x + h) - moreau f x)
          - (h \<bullet> G x + (h \<bullet> A h) / 2))) (cbox 0 1)"
      by (rule has_integral_diff[OF i1 i2])
    have bnd: "norm (h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
        \<le> e2 * (norm h)\<^sup>2" if s: "s \<in> cbox (0::real) 1" for s
    proof -
      have s01: "0 \<le> s" "s \<le> 1" using s by auto
      have nsh: "norm (s *\<^sub>R h) \<le> norm h"
      proof -
        have "norm (s *\<^sub>R h) = s * norm h" using s01 by simp
        also have "\<dots> \<le> 1 * norm h" using s01 by (intro mult_right_mono) auto
        finally show ?thesis by simp
      qed
      have "h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h))
          = h \<bullet> (G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h))"
        by (simp add: inner_diff_right inner_add_right)
      hence "norm (h \<bullet> G (x + s *\<^sub>R h) - h \<bullet> (G x + A (s *\<^sub>R h)))
          \<le> norm h * norm (G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h))"
        using Cauchy_Schwarz_ineq2[of h "G (x + s *\<^sub>R h) - G x - A (s *\<^sub>R h)"]
        by simp
      also have "\<dots> \<le> norm h * (e2 * norm (s *\<^sub>R h))"
        using small[of "s *\<^sub>R h"] nsh h(2) by (intro mult_left_mono) auto
      also have "\<dots> \<le> norm h * (e2 * norm h)"
        using nsh e2 by (intro mult_left_mono mult_left_mono) auto
      finally show ?thesis by (simp add: power2_eq_square algebra_simps)
    qed
    have "norm ((moreau f (x + h) - moreau f x)
        - (h \<bullet> G x + (h \<bullet> A h) / 2))
        \<le> e2 * (norm h)\<^sup>2 * content (cbox (0::real) 1)"
      using e2 by (intro has_integral_bound[OF _ i3 bnd]) auto
    hence err: "\<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h)) / 2\<bar> \<le> e2 * (norm h)\<^sup>2"
      unfolding Gx[symmetric] Ah[symmetric] by simp
    have hpos: "0 < (norm h)\<^sup>2" using h(1) by simp
    show ?thesis using err hpos by (simp add: divide_le_eq)
  qed
  show "eventually (\<lambda>h. dist ((moreau f (x + h) - moreau f x
      - h \<bullet> (x - prox f x) - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0 < \<epsilon>)
      (at 0)"
    unfolding eventually_at
  proof (intro exI[of _ \<delta>] conjI)
    show "0 < \<delta>" by (rule \<delta>)
    show "\<forall>h\<in>UNIV. h \<noteq> 0 \<and> dist h 0 < \<delta>
        \<longrightarrow> dist ((moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
            - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0 < \<epsilon>"
    proof (intro ballI impI)
      fix h :: 'a assume "h \<noteq> 0 \<and> dist h 0 < \<delta>"
      hence h: "h \<noteq> 0" "norm h < \<delta>" by (auto simp: dist_norm)
      have le: "\<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar> \<le> e2"
        by (rule main[OF h])
      have "dist ((moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0
          = \<bar>(moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
            - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2\<bar>"
        by (simp add: dist_real_def)
      also have "\<dots> \<le> e2" by (rule le)
      also have "e2 < \<epsilon>" using \<epsilon> by (simp add: e2_def)
      finally show "dist ((moreau f (x + h) - moreau f x
          - h \<bullet> (x - prox f x) - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) 0
          < \<epsilon>" .
    qed
  qed
qed

subsection \<open>Alexandrov's theorem for the Moreau envelope\<close>

text \<open>Alexandrov's theorem for the \<open>C\<^sup>1\<^sup>,\<^sup>1\<close> envelope: almost every point
  admits a second-order Taylor expansion with positive semidefinite
  quadratic form.  Transporting the expansion to \<open>f\<close> itself along the
  resolvent remains.\<close>

theorem moreau_alexandrov_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule eventually_mono[OF prox_differentiable_AE[OF cvx]])
  fix x :: 'a assume "(prox f) differentiable (at x)"
  then obtain D where D: "(prox f has_derivative D) (at x)"
    unfolding differentiable_def by blast
  have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have blA: "bounded_linear (\<lambda>h. h - D h)"
    using blD by (intro bounded_linear_sub bounded_linear_ident)
  have psd: "0 \<le> h \<bullet> (h - D h)" for h
    by (rule moreau_hessian_psd[OF cvx D])
  have tay: "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule moreau_second_order_taylor[OF cvx D])
  show "\<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using blA psd tay by blast
qed


(*<*)
end
(*>*)
