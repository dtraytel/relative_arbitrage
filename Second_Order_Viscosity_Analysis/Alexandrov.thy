section \<open>Alexandrov's theorem\<close>

(*<*)
theory Alexandrov
  imports Moreau_Envelope
begin

(*>*)

subsection \<open>Second differences\<close>

text \<open>The second difference \<open>\<Delta>(u,v) = e(x+u+v) - e(x+u) - e(x+v) + e(x)\<close>
  is trivially symmetric in \<open>u\<close> and \<open>v\<close>, while the fundamental theorem of
  calculus expresses it as a difference of two gradient integrals along
  parallel segments; comparing the two, after inserting the gradient's
  first-order expansion, forces \<open>u \<cdot> A v = v \<cdot> A u\<close>.\<close>

lemma second_difference_symmetric:
  fixes g :: "'a::ab_group_add \<Rightarrow> real"
  shows "g (x + u + v) - g (x + u) - g (x + v) + g x
       = g (x + v + u) - g (x + v) - g (x + u) + g x"
  by (simp add: add.commute add.left_commute)

theorem moreau_second_difference_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "moreau f (x + v + u) - moreau f (x + v)
       - (moreau f (x + u) - moreau f x)
       = integral {0..1} (\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u)
           - prox f (x + v + s *\<^sub>R u)))
       - integral {0..1} (\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))"
proof -
  have i1: "((\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u) - prox f (x + v + s *\<^sub>R u)))
      has_integral (moreau f (x + v + u) - moreau f (x + v))) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have i2: "((\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))
      has_integral (moreau f (x + u) - moreau f x)) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have e1: "integral {0..1} (\<lambda>s. u \<bullet> ((x + v + s *\<^sub>R u)
      - prox f (x + v + s *\<^sub>R u))) = moreau f (x + v + u) - moreau f (x + v)"
    by (rule integral_unique[OF i1])
  have e2: "integral {0..1} (\<lambda>s. u \<bullet> ((x + s *\<^sub>R u) - prox f (x + s *\<^sub>R u)))
      = moreau f (x + u) - moreau f x"
    by (rule integral_unique[OF i2])
  show ?thesis unfolding e1 e2 by simp
qed

text \<open>Along the two parallel segments the linear part of the gradient's
  increment is exactly \<open>t \<cdot> A v\<close>, independent of the segment parameter
  \<open>s\<close>; what is left over is a difference of two first-order remainders.\<close>

lemma linear_parallel_increment:
  fixes A :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
  shows "A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) - A (s *\<^sub>R (t *\<^sub>R u)) = t *\<^sub>R A v"
proof -
  have "A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) = A (t *\<^sub>R v) + A (s *\<^sub>R (t *\<^sub>R u))"
    using lin unfolding linear_iff by simp
  moreover have "A (t *\<^sub>R v) = t *\<^sub>R A v"
    using lin unfolding linear_iff by simp
  ultimately show ?thesis by simp
qed

lemma gradient_increment_decomp:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
  shows "G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G (x + s *\<^sub>R (t *\<^sub>R u))
       = t *\<^sub>R A v
         + ((G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G x
             - A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
           - (G (x + s *\<^sub>R (t *\<^sub>R u)) - G x - A (s *\<^sub>R (t *\<^sub>R u))))"
proof -
  have "t *\<^sub>R A v = A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) - A (s *\<^sub>R (t *\<^sub>R u))"
    by (rule linear_parallel_increment[OF lin, symmetric])
  thus ?thesis by simp
qed

text \<open>Pointwise on the segment, the integrand differs from
  \<open>t\<^sup>2 (u \<cdot> A v)\<close> by at most \<open>\<epsilon> t\<^sup>2 \<parallel>u\<parallel>(\<parallel>v\<parallel> + 2\<parallel>u\<parallel>)\<close>, so the second
  difference divided by \<open>t\<^sup>2\<close> converges to \<open>u \<cdot> A v\<close>.\<close>

lemma second_difference_integrand_bound:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
    and rem: "\<And>w. norm w < \<delta> \<Longrightarrow> norm (G (x + w) - G x - A w) \<le> e2 * norm w"
    and e2: "0 \<le> e2"
    and w1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and w2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and s: "0 \<le> s" "s \<le> 1"
  shows "\<bar>(t *\<^sub>R u) \<bullet> (G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
        - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v)\<bar>
      \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
proof -
  define R1 where "R1 = G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G x
      - A (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))"
  define R2 where "R2 = G (x + s *\<^sub>R (t *\<^sub>R u)) - G x - A (s *\<^sub>R (t *\<^sub>R u))"
  have decomp: "G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))) - G (x + s *\<^sub>R (t *\<^sub>R u))
      = t *\<^sub>R A v + (R1 - R2)"
    unfolding R1_def R2_def by (rule gradient_increment_decomp[OF lin])
  have main: "(t *\<^sub>R u) \<bullet> (G (x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
      - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v) = t * (u \<bullet> (R1 - R2))"
    unfolding decomp by (simp add: power2_eq_square algebra_simps)
  have n1: "norm R1 \<le> e2 * norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))"
    unfolding R1_def by (rule rem[OF w1])
  have n2: "norm R2 \<le> e2 * norm (s *\<^sub>R (t *\<^sub>R u))"
    unfolding R2_def by (rule rem[OF w2])
  have b2: "norm (s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * norm u"
  proof -
    have "norm (s *\<^sub>R (t *\<^sub>R u)) = s * (\<bar>t\<bar> * norm u)"
      using s by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * (\<bar>t\<bar> * norm u)"
      using s by (intro mult_right_mono) auto
    finally show ?thesis by simp
  qed
  have b1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * (norm v + norm u)"
  proof -
    have "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        \<le> norm (t *\<^sub>R v) + norm (s *\<^sub>R (t *\<^sub>R u))"
      by (rule norm_triangle_ineq)
    thus ?thesis using b2 by (simp add: algebra_simps)
  qed
  have r1: "norm R1 \<le> e2 * (\<bar>t\<bar> * (norm v + norm u))"
  proof -
    have "e2 * norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        \<le> e2 * (\<bar>t\<bar> * (norm v + norm u))"
      by (rule mult_left_mono[OF b1 e2])
    thus ?thesis using n1 by linarith
  qed
  have r2: "norm R2 \<le> e2 * (\<bar>t\<bar> * norm u)"
  proof -
    have "e2 * norm (s *\<^sub>R (t *\<^sub>R u)) \<le> e2 * (\<bar>t\<bar> * norm u)"
      by (rule mult_left_mono[OF b2 e2])
    thus ?thesis using n2 by linarith
  qed
  have nRR: "norm (R1 - R2) \<le> e2 * (\<bar>t\<bar> * (norm v + 2 * norm u))"
  proof -
    have "norm (R1 - R2) \<le> norm R1 + norm R2" by (rule norm_triangle_ineq4)
    thus ?thesis using r1 r2 by (simp add: algebra_simps)
  qed
  have inner_b: "\<bar>u \<bullet> (R1 - R2)\<bar>
      \<le> norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u)))"
  proof -
    have "\<bar>u \<bullet> (R1 - R2)\<bar> \<le> norm u * norm (R1 - R2)"
      using Cauchy_Schwarz_ineq2[of u "R1 - R2"] by simp
    also have "\<dots> \<le> norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u)))"
      by (rule mult_left_mono[OF nRR]) simp
    finally show ?thesis .
  qed
  have "\<bar>t * (u \<bullet> (R1 - R2))\<bar>
      \<le> \<bar>t\<bar> * (norm u * (e2 * (\<bar>t\<bar> * (norm v + 2 * norm u))))"
    unfolding abs_mult by (rule mult_left_mono[OF inner_b]) simp
  also have "\<dots> = e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
    by (simp add: power2_eq_square abs_mult[symmetric] algebra_simps)
  finally show ?thesis unfolding main .
qed

subsection \<open>Symmetry of the Hessian\<close>

text \<open>Integrating the pointwise bound gives the limit
  \<open>\<Delta>(t)/t\<^sup>2 \<rightarrow> u \<cdot> A v\<close>, and trivial symmetry of the second difference
  then forces \<open>u \<cdot> A v = v \<cdot> A u\<close>.\<close>
text \<open>The same bound in the left-associated form \<open>moreau_ftc\<close> actually
  produces, kept separate so \<open>simp\<close> does not distribute the inner
  product and lose the shape.\<close>

lemma second_difference_integrand_bound_left:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear A"
    and rem: "\<And>w. norm w < \<delta> \<Longrightarrow> norm (G (x + w) - G x - A w) \<le> e2 * norm w"
    and e2: "0 \<le> e2"
    and w1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and w2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
    and s: "0 \<le> s" "s \<le> 1"
  shows "\<bar>(t *\<^sub>R u) \<bullet> (G (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - G (x + s *\<^sub>R (t *\<^sub>R u))) - t\<^sup>2 * (u \<bullet> A v)\<bar>
      \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
proof -
  have assoc: "x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)
      = x + (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))" by (simp add: add.assoc)
  show ?thesis
    unfolding assoc
    by (rule second_difference_integrand_bound[OF lin rem e2 w1 w2 s])
qed
text \<open>The second difference as a single integral, in exactly the shape
  the pointwise bound expects.\<close>

lemma moreau_second_difference_has_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
        - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))
      has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v)
        - (moreau f (x + t *\<^sub>R u) - moreau f x))) {0..1}"
proof -
  have i1: "((\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
      - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))))
      has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v))) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have i2: "((\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + s *\<^sub>R (t *\<^sub>R u))
      - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
      has_integral (moreau f (x + t *\<^sub>R u) - moreau f x)) {0..1}"
    by (rule moreau_ftc[OF cvx])
  have eq: "(\<lambda>s. (t *\<^sub>R u) \<bullet> ((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
      - (t *\<^sub>R u) \<bullet> ((x + s *\<^sub>R (t *\<^sub>R u))
        - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
      = (\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))"
    by (rule ext) (simp only: inner_diff_right)
  show ?thesis
    using has_integral_diff[OF i1 i2] unfolding eq by simp
qed
theorem moreau_second_difference_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "((\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have GA: "((\<lambda>z :: 'a. z - prox f z) has_derivative A) (at x)"
    unfolding A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A" by (rule has_derivative_bounded_linear[OF GA])
  have linA: "linear A" using blA unfolding bounded_linear_def by simp
  define C where "C = norm u * (norm v + 2 * norm u) + 1"
  have C: "0 < C" by (simp add: C_def add_nonneg_pos)
  define e2 where "e2 = (\<epsilon>/2) / C"
  have e2: "0 < e2" using \<epsilon> C by (simp add: e2_def)
  have "((\<lambda>w. norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
      / norm w) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by simp
  from tendstoD[OF this e2] obtain \<delta> where \<delta>: "0 < \<delta>"
    and db: "\<And>w. w \<noteq> 0 \<Longrightarrow> dist w 0 < \<delta>
      \<Longrightarrow> dist (norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
          / norm w) 0 < e2"
    unfolding eventually_at by blast
  have rem: "norm ((x + w - prox f (x + w)) - (x - prox f x) - A w)
      \<le> e2 * norm w" if w: "norm w < \<delta>" for w
  proof (cases "w = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    have "norm ((x + w - prox f (x + w)) - (x - prox f x) - A w) / norm w < e2"
      using db[OF False] w by (simp add: dist_norm)
    thus ?thesis using False by (simp add: divide_less_eq)
  qed
  define M where "M = norm v + 2 * norm u + 1"
  have M: "0 < M" by (simp add: M_def add_nonneg_pos)
  define \<delta>' where "\<delta>' = \<delta> / M"
  have \<delta>': "0 < \<delta>'" using \<delta> M by (simp add: \<delta>'_def)
  have main: "\<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2 - u \<bullet> A v\<bar> \<le> \<epsilon>/2"
    if t: "t \<noteq> 0" "\<bar>t\<bar> < \<delta>'" for t
  proof -
    have tM: "\<bar>t\<bar> * M < \<delta>" using t(2) M by (simp add: \<delta>'_def field_simps)
    have iD: "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u)))))
        has_integral (moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x))) {0..1}"
      by (rule moreau_second_difference_has_integral[OF cvx])
    have iC: "((\<lambda>s :: real. t\<^sup>2 * (u \<bullet> A v))
        has_integral (t\<^sup>2 * (u \<bullet> A v))) {0..1}"
      using has_integral_const_real[of "t\<^sup>2 * (u \<bullet> A v)" 0 1] by simp
    have i5: "((\<lambda>s. (t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
        - t\<^sup>2 * (u \<bullet> A v))
        has_integral ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x)) - t\<^sup>2 * (u \<bullet> A v))) {0..1}"
      by (rule has_integral_diff[OF iD iC])
    have pb: "norm ((t *\<^sub>R u) \<bullet> (((x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
          - prox f (x + t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)))
          - ((x + s *\<^sub>R (t *\<^sub>R u)) - prox f (x + s *\<^sub>R (t *\<^sub>R u))))
        - t\<^sup>2 * (u \<bullet> A v))
        \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))"
      if s: "s \<in> cbox (0::real) 1" for s
    proof -
      have s01: "0 \<le> s" "s \<le> 1" using s by auto
      have nb2: "norm (s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * norm u"
      proof -
        have "norm (s *\<^sub>R (t *\<^sub>R u)) = s * (\<bar>t\<bar> * norm u)"
          using s01 by (simp add: abs_mult)
        also have "\<dots> \<le> 1 * (\<bar>t\<bar> * norm u)"
          using s01 by (intro mult_right_mono) auto
        finally show ?thesis by simp
      qed
      have nb1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) \<le> \<bar>t\<bar> * (norm v + norm u)"
      proof -
        have "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u))
            \<le> norm (t *\<^sub>R v) + norm (s *\<^sub>R (t *\<^sub>R u))"
          by (rule norm_triangle_ineq)
        thus ?thesis using nb2 by (simp add: algebra_simps)
      qed
      have lt1: "norm (t *\<^sub>R v + s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
      proof -
        have "\<bar>t\<bar> * (norm v + norm u) \<le> \<bar>t\<bar> * M"
          using t(1) by (intro mult_left_mono) (auto simp: M_def)
        thus ?thesis using nb1 tM by linarith
      qed
      have lt2: "norm (s *\<^sub>R (t *\<^sub>R u)) < \<delta>"
      proof -
        have "\<bar>t\<bar> * norm u \<le> \<bar>t\<bar> * M"
          using t(1) by (intro mult_left_mono) (auto simp: M_def)
        thus ?thesis using nb2 tM by linarith
      qed
      show ?thesis
        using second_difference_integrand_bound_left
          [OF linA rem less_imp_le[OF e2] lt1 lt2 s01] by simp
    qed
    have bound: "norm ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
        - t\<^sup>2 * (u \<bullet> A v))
        \<le> e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u))
          * content (cbox (0::real) 1)"
      using e2 by (intro has_integral_bound[OF _ i5[folded box_real(2)] pb])
        auto
    have tsq: "0 < t\<^sup>2" using t(1) by simp
    have "e2 * t\<^sup>2 * (norm u * (norm v + 2 * norm u)) \<le> e2 * t\<^sup>2 * C"
      using e2 tsq by (intro mult_left_mono) (auto simp: C_def)
    also have "\<dots> = (\<epsilon>/2) * t\<^sup>2" using C by (simp add: e2_def)
    finally have b2: "\<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
        - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
        - t\<^sup>2 * (u \<bullet> A v)\<bar> \<le> (\<epsilon>/2) * t\<^sup>2" using bound by simp
    show ?thesis using b2 tsq by (simp add: field_simps)
  qed
  show "eventually (\<lambda>t. dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
      - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      (u \<bullet> (v - D v)) < \<epsilon>) (at 0)"
    unfolding eventually_at
  proof (intro exI[of _ \<delta>'] conjI)
    show "0 < \<delta>'" by (rule \<delta>')
    show "\<forall>t\<in>UNIV. t \<noteq> 0 \<and> dist t 0 < \<delta>'
        \<longrightarrow> dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
            - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
            (u \<bullet> (v - D v)) < \<epsilon>"
    proof (intro ballI impI)
      fix t :: real assume "t \<noteq> 0 \<and> dist t 0 < \<delta>'"
      hence t: "t \<noteq> 0" "\<bar>t\<bar> < \<delta>'" by (auto simp: dist_real_def)
      have "dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
          - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2) (u \<bullet> (v - D v))
          = \<bar>(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
            - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2 - u \<bullet> A v\<bar>"
        by (simp add: dist_real_def A_def)
      also have "\<dots> \<le> \<epsilon>/2" by (rule main[OF t])
      also have "\<epsilon>/2 < \<epsilon>" using \<epsilon> by simp
      finally show "dist ((moreau f (x + t *\<^sub>R v + t *\<^sub>R u)
          - moreau f (x + t *\<^sub>R v) - (moreau f (x + t *\<^sub>R u) - moreau f x))
          / t\<^sup>2) (u \<bullet> (v - D v)) < \<epsilon>" .
    qed
  qed
qed

text \<open>Symmetry of the Hessian, at last: the second difference is symmetric
  in \<open>u\<close> and \<open>v\<close> for trivial reasons, so the two limits computed from it
  must agree.\<close>

theorem moreau_hessian_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
  shows "u \<bullet> (v - D v) = v \<bullet> (u - D u)"
proof -
  have l1: "((\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
    by (rule moreau_second_difference_limit[OF cvx D])
  have l2: "((\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
      - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> v \<bullet> (u - D u)) (at 0)"
    by (rule moreau_second_difference_limit[OF cvx D])
  have same: "(\<lambda>t. (moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
      - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2)
      = (\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
      - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)"
  proof (rule ext)
    fix t :: real
    have eq: "x + t *\<^sub>R v + t *\<^sub>R u = x + t *\<^sub>R u + t *\<^sub>R v"
      by (simp add: add.commute add.left_commute)
    show "(moreau f (x + t *\<^sub>R v + t *\<^sub>R u) - moreau f (x + t *\<^sub>R v)
        - (moreau f (x + t *\<^sub>R u) - moreau f x)) / t\<^sup>2
        = (moreau f (x + t *\<^sub>R u + t *\<^sub>R v) - moreau f (x + t *\<^sub>R u)
        - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2"
      unfolding eq by (rule arg_cong[where f = "\<lambda>y::real. y / t\<^sup>2"]) simp
  qed
  from l1 have l1': "((\<lambda>t. (moreau f (x + t *\<^sub>R u + t *\<^sub>R v)
      - moreau f (x + t *\<^sub>R u) - (moreau f (x + t *\<^sub>R v) - moreau f x)) / t\<^sup>2)
      \<longlongrightarrow> u \<bullet> (v - D v)) (at 0)"
    unfolding same .
  show ?thesis by (rule tendsto_unique[OF at_neq_bot l1' l2])
qed

text \<open>Alexandrov's theorem for the Moreau envelope, final form: almost
  every point admits a second-order Taylor expansion with bounded,
  symmetric, positive semidefinite quadratic form --- a genuine Hessian.\<close>

theorem moreau_alexandrov_sym_AE:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "AE x in lborel. \<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> (\<forall>u v. u \<bullet> A v = v \<bullet> A u)
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
  have sym: "u \<bullet> (v - D v) = v \<bullet> (u - D u)" for u v
    by (rule moreau_hessian_symmetric[OF cvx D])
  have tay: "((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h)) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule moreau_second_order_taylor[OF cvx D])
  show "\<exists>A. bounded_linear A \<and> (\<forall>h. 0 \<le> h \<bullet> A h)
      \<and> (\<forall>u v. u \<bullet> A v = v \<bullet> A u)
      \<and> ((\<lambda>h. (moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
          - (h \<bullet> A h) / 2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using blA psd sym tay by blast
qed

subsection \<open>Transporting Alexandrov from the envelope to the function\<close>

text \<open>The envelope is a smoothed copy of \<open>f\<close>, reached through the
  resolvent \<open>R = prox f\<close>; transporting the expansion back needs \<open>R\<close>'s
  defining property in reverse --- \<open>R\<close> undoes \<open>id + subdiff f\<close>.\<close>

lemma subdiff_prox:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and p: "p \<in> subdiff f y"
  shows "prox f (y + p) = y"
proof (rule prox_unique[OF cvx, of "prox f (y + p)" "y + p" y])
  show "f (prox f (y + p)) + (dist (y + p) (prox f (y + p)))\<^sup>2/2
      \<le> f z + (dist (y + p) z)\<^sup>2/2" for z
    by (rule prox_min[OF cvx])
next
  fix z :: 'a
  have sd: "f y + p \<bullet> (z - y) \<le> f z" by (rule subdiffD[OF p])
  have rw: "y + p - z = p - (z - y)" by simp
  have exp: "(dist (y + p) z)\<^sup>2
      = (norm p)\<^sup>2 - 2 * (p \<bullet> (z - y)) + (norm (z - y))\<^sup>2"
    unfolding dist_norm rw
    by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
        inner_commute)
  have d1: "(dist (y + p) y)\<^sup>2 = (norm p)\<^sup>2" by (simp add: dist_norm)
  have nn: "0 \<le> (norm (z - y))\<^sup>2" by simp
  show "f y + (dist (y + p) y)\<^sup>2/2 \<le> f z + (dist (y + p) z)\<^sup>2/2"
    unfolding d1 exp using sd nn by argo
qed

text \<open>Subgradients are bounded by difference quotients: pushing a distance
  \<open>r\<close> in the direction of a subgradient must increase \<open>f\<close> by at least
  \<open>r * norm p\<close>.\<close>

lemma subdiff_norm_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes r: "0 < r" and p: "p \<in> subdiff f u"
    and M: "\<And>v. v \<in> cball u r \<Longrightarrow> f v \<le> M"
  shows "norm p \<le> (M - f u) / r"
proof (cases "p = 0")
  case True
  have "f u \<le> M" using M[of u] r by simp
  thus ?thesis unfolding True using r by simp
next
  case False
  hence np: "0 < norm p" by simp
  define v where "v = u + (r / norm p) *\<^sub>R p"
  have "dist v u = \<bar>r / norm p\<bar> * norm p"
    unfolding v_def dist_norm by simp
  also have "\<dots> = r" using np r by simp
  finally have vm: "v \<in> cball u r" by (simp add: dist_commute)
  have "p \<bullet> (v - u) = (r / norm p) * (p \<bullet> p)"
    unfolding v_def by simp
  also have "\<dots> = r * norm p"
    using np by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  finally have pv: "p \<bullet> (v - u) = r * norm p" .
  have "f u + p \<bullet> (v - u) \<le> f v" by (rule subdiffD[OF p])
  hence "f u + r * norm p \<le> M" using M[OF vm] unfolding pv by linarith
  thus ?thesis using r by (simp add: field_simps)
qed

lemma convex_bdd_above_cball:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>M. \<forall>v \<in> cball u r. f v \<le> M"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have "compact (f ` cball u r)"
    by (rule compact_continuous_image[OF continuous_on_subset[OF cf subset_UNIV]
        compact_cball])
  hence "bdd_above (f ` cball u r)"
    by (simp add: compact_imp_bounded bounded_imp_bdd_above)
  hence "f v \<le> Sup (f ` cball u r)" if "v \<in> cball u r" for v
    using that by (intro cSup_upper) auto
  thus ?thesis by blast
qed

lemma convex_bdd_below_cball:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>m. \<forall>v \<in> cball u r. m \<le> f v"
proof -
  have cf: "continuous_on UNIV f"
    by (rule convex_on_continuous[OF open_UNIV cvx])
  have "compact (f ` cball u r)"
    by (rule compact_continuous_image[OF continuous_on_subset[OF cf subset_UNIV]
        compact_cball])
  hence "bdd_below (f ` cball u r)"
    by (simp add: compact_imp_bounded bounded_imp_bdd_below)
  hence "Inf (f ` cball u r) \<le> f v" if "v \<in> cball u r" for v
    using that by (intro cInf_lower) auto
  thus ?thesis by blast
qed

text \<open>The subdifferential is convex, being cut out by linear inequalities.\<close>

lemma convex_subdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes p: "p \<in> subdiff f x" and q: "q \<in> subdiff f x"
    and t: "0 \<le> t" "t \<le> 1"
  shows "(1 - t) *\<^sub>R p + t *\<^sub>R q \<in> subdiff f x"
proof (rule subdiffI)
  fix y
  have 1: "f x + p \<bullet> (y - x) \<le> f y" by (rule subdiffD[OF p])
  have 2: "f x + q \<bullet> (y - x) \<le> f y" by (rule subdiffD[OF q])
  have e: "((1 - t) *\<^sub>R p + t *\<^sub>R q) \<bullet> (y - x)
      = (1 - t) * (p \<bullet> (y - x)) + t * (q \<bullet> (y - x))"
    by (simp add: inner_add_left)
  have "(1 - t) * (f x + p \<bullet> (y - x)) + t * (f x + q \<bullet> (y - x))
      \<le> (1 - t) * f y + t * f y"
    using t 1 2 by (intro add_mono mult_left_mono) auto
  thus "f x + ((1 - t) *\<^sub>R p + t *\<^sub>R q) \<bullet> (y - x) \<le> f y"
    unfolding e by (simp add: algebra_simps)
qed

text \<open>Where the resolvent's derivative is injective, the subdifferential
  downstream is a singleton: two distinct subgradients at \<open>prox f x\<close>
  would make the resolvent constant along a segment, killing its
  derivative's injectivity.\<close>

lemma prox_deriv_inj_subdiff_singleton:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
    and q: "q \<in> subdiff f (prox f x)"
  shows "q = x - prox f x"
proof -
  define y where "y = prox f x"
  define p where "p = x - y"
  define d where "d = q - p"
  have p_sub: "p \<in> subdiff f y" unfolding p_def y_def by (rule prox_subdiff[OF cvx])
  have q_sub: "q \<in> subdiff f y" using q unfolding y_def .
  have const: "prox f (x + t *\<^sub>R d) = y" if t: "0 \<le> t" "t \<le> 1" for t
  proof -
    have "(1 - t) *\<^sub>R p + t *\<^sub>R q \<in> subdiff f y"
      by (rule convex_subdiff[OF p_sub q_sub t])
    hence "prox f (y + ((1 - t) *\<^sub>R p + t *\<^sub>R q)) = y"
      by (rule subdiff_prox[OF cvx])
    moreover have "y + ((1 - t) *\<^sub>R p + t *\<^sub>R q) = x + t *\<^sub>R d"
      unfolding d_def p_def
      by (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  have lim0: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> D d) (at (0::real))"
    by (rule has_derivative_dir_limit[OF D])
  have lim1: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> D d)
      (at_right (0::real))"
    by (rule tendsto_mono[OF at_le[OF subset_UNIV] lim0])
  have ev: "\<forall>\<^sub>F t in at_right (0::real).
      (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t = 0"
  proof (rule eventually_mono[OF eventually_at_right_real[OF zero_less_one]])
    fix t :: real assume "t \<in> {0<..<1}"
    hence t: "0 \<le> t" "t \<le> 1" by auto
    show "(prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t = 0"
      unfolding const[OF t] y_def[symmetric] by simp
  qed
  have lim2: "((\<lambda>t. (prox f (x + t *\<^sub>R d) - prox f x) /\<^sub>R t) \<longlongrightarrow> 0)
      (at_right (0::real))"
    by (rule tendsto_eventually[OF ev])
  have nb: "at_right (0::real) \<noteq> bot"
    using trivial_limit_at_right_real unfolding trivial_limit_def by blast
  have Dd: "D d = 0" by (rule tendsto_unique[OF nb lim1 lim2])
  have "D 0 = 0"
    using has_derivative_bounded_linear[OF D] by (simp add: linear_simps(3))
  with Dd have "D d = D 0" by simp
  hence "d = 0" using injD by (simp add: inj_eq)
  thus ?thesis unfolding d_def p_def y_def by simp
qed


text \<open>The resolvent is continuous, and its fibres over a bounded set are
  bounded, since \<open>z - prox f z\<close> is a subgradient at \<open>prox f z\<close> and
  subgradients are locally bounded.\<close>

lemma prox_lipschitz_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "lipschitz_on 1 UNIV (prox f)"
  by (intro lipschitz_onI) (auto simp: prox_nonexpansive[OF cvx])

lemma continuous_on_prox:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "continuous_on S (prox f)"
  by (rule continuous_on_subset[OF
      lipschitz_on_continuous_on[OF prox_lipschitz_on[OF cvx]] subset_UNIV])

lemma prox_fibre_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "\<exists>C. \<forall>z. dist (prox f z) y \<le> 1 \<longrightarrow> norm (z - prox f z) \<le> C"
proof -
  obtain M where M: "\<And>v. v \<in> cball y 2 \<Longrightarrow> f v \<le> M"
    using convex_bdd_above_cball[OF cvx, of y 2] by blast
  obtain m where m: "\<And>v. v \<in> cball y 1 \<Longrightarrow> m \<le> f v"
    using convex_bdd_below_cball[OF cvx, of y 1] by blast
  have "norm (z - prox f z) \<le> M - m" if zz: "dist (prox f z) y \<le> 1" for z
  proof -
    have sd: "z - prox f z \<in> subdiff f (prox f z)" by (rule prox_subdiff[OF cvx])
    have sub: "f v \<le> M" if "v \<in> cball (prox f z) 1" for v
    proof -
      have "dist v y \<le> dist v (prox f z) + dist (prox f z) y"
        by (rule dist_triangle)
      also have "\<dots> \<le> 2" using that zz by (simp add: dist_commute)
      finally show ?thesis by (intro M) (simp add: dist_commute)
    qed
    have "norm (z - prox f z) \<le> (M - f (prox f z)) / 1"
      by (rule subdiff_norm_le[OF zero_less_one sd sub])
    moreover have "m \<le> f (prox f z)"
      using zz by (intro m) (simp add: dist_commute)
    ultimately show ?thesis by simp
  qed
  thus ?thesis by blast
qed

lemma prox_fibre_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "compact {z. dist (prox f z) y \<le> 1}"
proof (rule compact_eq_bounded_closed[THEN iffD2], intro conjI)
  obtain C where C: "\<And>z. dist (prox f z) y \<le> 1 \<Longrightarrow> norm (z - prox f z) \<le> C"
    using prox_fibre_bounded[OF cvx, of y] by blast
  have "norm z \<le> C + (1 + norm y)" if zz: "dist (prox f z) y \<le> 1" for z
  proof -
    have t1: "norm z \<le> norm (prox f z) + norm (z - prox f z)"
      by (rule norm_triangle_sub)
    have t2: "norm (prox f z) \<le> norm y + norm (prox f z - y)"
      by (rule norm_triangle_sub)
    have t3: "norm (prox f z - y) \<le> 1" using zz by (simp add: dist_norm)
    show ?thesis using t1 t2 t3 C[OF zz] by simp
  qed
  thus "bounded {z. dist (prox f z) y \<le> 1}" by (intro boundedI) auto
next
  have c1: "continuous_on UNIV (\<lambda>z. dist (prox f z) y)"
    by (rule continuous_on_dist[OF continuous_on_prox[OF cvx] continuous_on_const])
  show "closed {z. dist (prox f z) y \<le> 1}"
    by (rule closed_Collect_le[OF c1 continuous_on_const])
qed

text \<open>Local invertibility of the resolvent, by compactness rather than an
  inverse function theorem: on the compact fibre over a unit ball,
  \<open>z \<mapsto> dist (prox f z) y\<close> vanishes only at \<open>x\<close>, so outside any ball
  around \<open>x\<close> it is bounded below by a positive constant.\<close>

lemma prox_local_inverse_continuous:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and sing: "\<And>q. q \<in> subdiff f (prox f x) \<Longrightarrow> q = x - prox f x"
    and e: "0 < \<epsilon>"
  shows "\<exists>\<delta>>0. \<forall>z. dist (prox f z) (prox f x) < \<delta> \<longrightarrow> dist z x < \<epsilon>"
proof -
  define y where "y = prox f x"
  define K where "K = {z. dist (prox f z) y \<le> 1}"
  have Kc: "compact K" unfolding K_def by (rule prox_fibre_compact[OF cvx])
  define L where "L = K \<inter> (- ball x \<epsilon>)"
  have Lc: "compact L"
    unfolding L_def by (intro compact_Int_closed Kc closed_Compl open_ball)
  show ?thesis
  proof (cases "L = {}")
    case True
    have "dist z x < \<epsilon>" if "dist (prox f z) y < 1" for z
    proof -
      have "z \<in> K" using that unfolding K_def by simp
      hence "z \<in> ball x \<epsilon>" using True unfolding L_def by auto
      thus ?thesis by (simp add: dist_commute)
    qed
    thus ?thesis unfolding y_def by (intro exI[of _ 1]) simp
  next
    case False
    have cg: "continuous_on L (\<lambda>z. dist (prox f z) y)"
      by (rule continuous_on_dist[OF continuous_on_prox[OF cvx]
          continuous_on_const])
    obtain z0 where z0: "z0 \<in> L"
      and mn: "\<And>z. z \<in> L \<Longrightarrow> dist (prox f z0) y \<le> dist (prox f z) y"
      using continuous_attains_inf[OF Lc False cg] by blast
    have pos: "0 < dist (prox f z0) y"
    proof (rule ccontr)
      assume "\<not> 0 < dist (prox f z0) y"
      hence pz: "prox f z0 = y" by simp
      have "z0 - prox f z0 \<in> subdiff f (prox f z0)" by (rule prox_subdiff[OF cvx])
      hence "z0 - y \<in> subdiff f (prox f x)" unfolding pz y_def .
      hence "z0 - y = x - prox f x" by (rule sing)
      hence "z0 = x" unfolding y_def by simp
      moreover have "x \<in> ball x \<epsilon>" using e by simp
      ultimately show False using z0 unfolding L_def by simp
    qed
    define \<delta> where "\<delta> = min (dist (prox f z0) y) 1"
    have dpos: "0 < \<delta>" unfolding \<delta>_def using pos by simp
    have "dist z x < \<epsilon>" if dz: "dist (prox f z) y < \<delta>" for z
    proof (rule ccontr)
      assume "\<not> dist z x < \<epsilon>"
      hence "z \<notin> ball x \<epsilon>" by (simp add: dist_commute)
      moreover have "z \<in> K" using dz unfolding K_def \<delta>_def by simp
      ultimately have "z \<in> L" unfolding L_def by simp
      hence "dist (prox f z0) y \<le> dist (prox f z) y" by (rule mn)
      thus False using dz unfolding \<delta>_def by simp
    qed
    thus ?thesis unfolding y_def using dpos by blast
  qed
qed

text \<open>The exact identity behind the transport: writing
  \<open>G z = z - prox f z\<close> for the displacement, the increment of \<open>f\<close>
  between two proximal points, measured against \<open>G x\<close>, equals the
  envelope's increment against the same vector minus half the squared
  increment of \<open>G\<close>; the first-order terms cancel exactly.\<close>

lemma f_increment_exact:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "f (prox f (x + h)) - f (prox f x)
       - (x - prox f x) \<bullet> (prox f (x + h) - prox f x)
       = moreau f (x + h) - moreau f x - (x - prox f x) \<bullet> h
       - (norm ((x + h - prox f (x + h)) - (x - prox f x)))\<^sup>2 / 2"
proof -
  define y where "y = prox f x"
  define w where "w = prox f (x + h)"
  have e1: "moreau f x = f y + (norm (x - y))\<^sup>2/2"
    unfolding moreau_def y_def by (simp add: dist_norm)
  have e2: "moreau f (x + h) = f w + (norm (x + h - w))\<^sup>2/2"
    unfolding moreau_def w_def by (simp add: dist_norm)
  have s1: "(norm (x + h - w))\<^sup>2 = (x + h - w) \<bullet> (x + h - w)"
    by (rule power2_norm_eq_inner)
  have s2: "(norm (x - y))\<^sup>2 = (x - y) \<bullet> (x - y)"
    by (rule power2_norm_eq_inner)
  have s3: "(norm ((x + h - w) - (x - y)))\<^sup>2
      = ((x + h - w) - (x - y)) \<bullet> ((x + h - w) - (x - y))"
    by (rule power2_norm_eq_inner)
  show ?thesis
    unfolding y_def[symmetric] w_def[symmetric] e1 e2 s1 s2 s3
    by (simp add: inner_commute algebra_simps) argo
qed

text \<open>Three quantitative ingredients: the displacement's first-order
  remainder, the envelope's second-order remainder, and a lower bound
  for an injective linear map.\<close>

lemma prox_remainder_small:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes D: "(prox f has_derivative D) (at x)" and \<eta>: "0 < \<eta>"
  shows "\<exists>\<delta>>0. \<forall>h. norm h < \<delta> \<longrightarrow>
      norm ((x + h - prox f (x + h)) - (x - prox f x) - (h - D h)) \<le> \<eta> * norm h"
proof -
  define G where "G = (\<lambda>z :: 'a. z - prox f z)"
  define A where "A = (\<lambda>k :: 'a. k - D k)"
  have GA: "(G has_derivative A) (at x)"
    unfolding G_def A_def by (rule moreau_grad_has_derivative[OF D])
  have blA: "bounded_linear A" by (rule has_derivative_bounded_linear[OF GA])
  have "((\<lambda>u. norm (G (x + u) - G x - A u) / norm u) \<longlongrightarrow> 0) (at 0)"
    using GA unfolding has_derivative_at by blast
  from tendstoD[OF this \<eta>] obtain \<delta> where d: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta>
      \<Longrightarrow> dist (norm (G (x + u) - G x - A u) / norm u) 0 < \<eta>"
    unfolding eventually_at by blast
  have "norm (G (x + h) - G x - A h) \<le> \<eta> * norm h" if hh: "norm h < \<delta>" for h
  proof (cases "h = 0")
    case True
    have "A 0 = 0" using blA by (simp add: linear_simps(3))
    thus ?thesis unfolding True by simp
  next
    case False
    hence nh: "0 < norm h" by simp
    have "norm (G (x + h) - G x - A h) / norm h < \<eta>"
      using db[OF False] hh by (simp add: dist_norm)
    thus ?thesis using nh by (simp add: field_simps)
  qed
  thus ?thesis unfolding G_def A_def using d by blast
qed

lemma moreau_taylor_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)" and \<eta>: "0 < \<eta>"
  shows "\<exists>\<delta>>0. \<forall>h. norm h < \<delta> \<longrightarrow>
      \<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2\<bar> \<le> \<eta> * (norm h)\<^sup>2"
proof -
  define T where "T = (\<lambda>h. moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
      - (h \<bullet> (h - D h))/2)"
  have "((\<lambda>h. T h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding T_def by (rule moreau_second_order_taylor[OF cvx D])
  from tendstoD[OF this \<eta>] obtain \<delta> where d: "0 < \<delta>"
    and db: "\<And>u. u \<noteq> 0 \<Longrightarrow> dist u 0 < \<delta> \<Longrightarrow> dist (T u / (norm u)\<^sup>2) 0 < \<eta>"
    unfolding eventually_at by blast
  have "\<bar>T h\<bar> \<le> \<eta> * (norm h)\<^sup>2" if hh: "norm h < \<delta>" for h
  proof (cases "h = 0")
    case True
    show ?thesis unfolding True T_def by simp
  next
    case False
    hence nh: "0 < (norm h)\<^sup>2" by simp
    have "\<bar>T h / (norm h)\<^sup>2\<bar> < \<eta>"
      using db[OF False] hh by (simp add: dist_norm)
    hence "\<bar>T h\<bar> / (norm h)\<^sup>2 < \<eta>" by simp
    thus ?thesis using nh by (simp add: field_simps)
  qed
  thus ?thesis unfolding T_def using d by blast
qed

lemma inj_linear_bounded_below:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes bl: "bounded_linear D" and injD: "inj D"
  shows "\<exists>K>0. \<forall>u. norm u \<le> K * norm (D u)"
proof -
  have lin: "linear D" using bl by (rule bounded_linear.linear)
  obtain D' where lin': "linear D'" and inv: "D' \<circ> D = id"
    using linear_injective_left_inverse[OF lin injD] by blast
  obtain K where K: "\<And>v. norm (D' v) \<le> K * norm v"
    using lin' linear_bounded by blast
  have K1: "\<And>v. norm (D' v) \<le> (max K 1) * norm v"
    using K by (meson max.cobounded1 mult_right_mono norm_ge_zero order_trans)
  have "norm u \<le> (max K 1) * norm (D u)" for u
  proof -
    have "u = D' (D u)" using inv by (simp add: pointfree_idE)
    thus ?thesis using K1[of "D u"] by simp
  qed
  thus ?thesis by (intro exI[of _ "max K 1"]) auto
qed

text \<open>The algebraic heart of the transport: with \<open>A u = u - D u\<close> and
  \<open>B u = D' u - u\<close>, the quadratic forms seen by the envelope at \<open>h\<close> and
  by \<open>f\<close> at \<open>k = D h - \<rho>\<close> differ only by terms carrying a factor \<open>\<rho>\<close> ---
  the leading terms \<open>D h \<cdot> A h\<close> cancel identically.\<close>

lemma taylor_remainder_identity:
  fixes D D' :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin': "linear D'" and inv: "D' (D h) = h"
  shows "h \<bullet> (h - D h) - (norm ((h - D h) + \<rho>))\<^sup>2
       - (D h - \<rho>) \<bullet> (D' (D h - \<rho>) - (D h - \<rho>))
       = - ((h - D h) \<bullet> \<rho>) - (norm \<rho>)\<^sup>2
       + D h \<bullet> (D' \<rho> - \<rho>) - \<rho> \<bullet> (D' \<rho> - \<rho>)"
proof -
  have e1: "D' (D h - \<rho>) = h - D' \<rho>"
    using linear_diff[OF lin'] inv by simp
  show ?thesis
    unfolding e1 power2_norm_eq_inner
    by (simp add: inner_diff_left inner_diff_right inner_add_left
        inner_add_right inner_commute)
qed

text \<open>The transport: where the resolvent is differentiable with injective
  derivative, \<open>f\<close> itself has a second-order expansion at the
  corresponding proximal point, with quadratic form \<open>B = D' - id\<close>;
  every step from \<open>h\<close> to \<open>k = D h - \<rho>\<close> is controlled by the single
  remainder \<open>\<rho>\<close>, and compactness guarantees \<open>h\<close> is small whenever \<open>k\<close>
  is.\<close>

theorem f_taylor_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
    and lin': "linear D'" and inv: "\<And>u. D' (D u) = u"
  shows "((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof (rule tendstoI)
  fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
  have blD: "bounded_linear D" by (rule has_derivative_bounded_linear[OF D])
  have blA: "bounded_linear (\<lambda>u. u - D u)"
    by (intro bounded_linear_sub bounded_linear_ident blD)
  have blD': "bounded_linear D'" using lin' by (simp add: linear_conv_bounded_linear)
  have blB: "bounded_linear (\<lambda>u. D' u - u)"
    by (intro bounded_linear_sub bounded_linear_ident blD')
  obtain NA where NA0: "0 < NA" and NAb: "\<And>u. norm (u - D u) \<le> norm u * NA"
    using bounded_linear.pos_bounded[OF blA] by blast
  obtain NB where NB0: "0 < NB" and NBb: "\<And>u. norm (D' u - u) \<le> norm u * NB"
    using bounded_linear.pos_bounded[OF blB] by blast
  obtain K where K0: "0 < K" and Kb: "\<And>u. norm u \<le> K * norm (D u)"
    using inj_linear_bounded_below[OF blD injD] by blast
  define C where "C = 2 + NA + 2*NB"
  have C0: "0 < C" unfolding C_def using NA0 NB0 by simp
  define \<eta> where "\<eta> = min (min 1 (1/(2*K))) (\<epsilon>/(C * 8 * K\<^sup>2))"
  have \<eta>1: "\<eta> \<le> 1" and \<eta>K: "\<eta> \<le> 1/(2*K)" and \<eta>e: "\<eta> \<le> \<epsilon>/(C * 8 * K\<^sup>2)"
    unfolding \<eta>_def by auto
  have \<eta>0: "0 < \<eta>" unfolding \<eta>_def using K0 \<epsilon> C0 by simp
  obtain \<delta>1 where \<delta>1: "0 < \<delta>1"
    and B1: "\<And>h. norm h < \<delta>1 \<Longrightarrow>
      norm ((x + h - prox f (x + h)) - (x - prox f x) - (h - D h)) \<le> \<eta> * norm h"
    using prox_remainder_small[OF D \<eta>0] by blast
  obtain \<delta>2 where \<delta>2: "0 < \<delta>2"
    and B2: "\<And>h. norm h < \<delta>2 \<Longrightarrow>
      \<bar>moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2\<bar> \<le> \<eta> * (norm h)\<^sup>2"
    using moreau_taylor_bound[OF cvx D \<eta>0] by blast
  define \<delta>0 where "\<delta>0 = min \<delta>1 \<delta>2"
  have \<delta>00: "0 < \<delta>0" unfolding \<delta>0_def using \<delta>1 \<delta>2 by simp
  have sing: "\<And>q. q \<in> subdiff f (prox f x) \<Longrightarrow> q = x - prox f x"
    by (rule prox_deriv_inj_subdiff_singleton[OF cvx D injD])
  obtain \<delta>3 where \<delta>3: "0 < \<delta>3"
    and B3: "\<And>z. dist (prox f z) (prox f x) < \<delta>3 \<Longrightarrow> dist z x < \<delta>0"
    using prox_local_inverse_continuous[OF cvx sing \<delta>00] by blast
  have main: "dist ((f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) 0 < \<epsilon>"
    if k0: "k \<noteq> 0" and kd: "dist k 0 < \<delta>3" for k
  proof -
    define Nm where "Nm = f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
        - (k \<bullet> (D' k - k))/2"
    have nk: "0 < norm k" using k0 by simp
    obtain q where q: "q \<in> subdiff f (prox f x + k)"
      using subdiff_nonempty[OF cvx] by blast
    define h where "h = (prox f x + k) + q - x"
    have xh: "x + h = (prox f x + k) + q" unfolding h_def by simp
    have ph: "prox f (x + h) = prox f x + k"
      unfolding xh by (rule subdiff_prox[OF cvx q])
    have "dist (prox f (x + h)) (prox f x) < \<delta>3"
      unfolding ph using kd by (simp add: dist_norm)
    hence "dist (x + h) x < \<delta>0" by (rule B3)
    hence nh: "norm h < \<delta>0" by (simp add: dist_norm)
    have nh1: "norm h < \<delta>1" using nh unfolding \<delta>0_def by simp
    have nh2: "norm h < \<delta>2" using nh unfolding \<delta>0_def by simp
    define g where "g = (x + h - prox f (x + h)) - (x - prox f x)"
    define \<rho> where "\<rho> = g - (h - D h)"
    have n\<rho>: "norm \<rho> \<le> \<eta> * norm h"
      unfolding \<rho>_def g_def by (rule B1[OF nh1])
    have gh: "g = h - k" unfolding g_def ph by simp
    have kD: "k = D h - \<rho>" unfolding \<rho>_def gh by simp
    have g\<rho>: "g = (h - D h) + \<rho>" unfolding \<rho>_def by simp
    have inc: "f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
        = moreau f (x + h) - moreau f x - (x - prox f x) \<bullet> h - (norm g)\<^sup>2/2"
      using f_increment_exact[OF cvx, of x h] unfolding ph gh by simp
    define T where "T = moreau f (x + h) - moreau f x - h \<bullet> (x - prox f x)
        - (h \<bullet> (h - D h))/2"
    have nT: "\<bar>T\<bar> \<le> \<eta> * (norm h)\<^sup>2" unfolding T_def by (rule B2[OF nh2])
    define Rm where "Rm = h \<bullet> (h - D h) - (norm g)\<^sup>2 - k \<bullet> (D' k - k)"
    have N: "Nm = T + Rm/2"
      unfolding Nm_def T_def Rm_def using inc by (simp add: inner_commute) argo
    have rid: "Rm = - ((h - D h) \<bullet> \<rho>) - (norm \<rho>)\<^sup>2
        + D h \<bullet> (D' \<rho> - \<rho>) - \<rho> \<bullet> (D' \<rho> - \<rho>)"
      unfolding Rm_def g\<rho> kD by (rule taylor_remainder_identity[OF lin' inv])
    have nh0: "0 \<le> norm h" by simp
    have n\<rho>0: "0 \<le> norm \<rho>" by simp
    have n1: "\<bar>(h - D h) \<bullet> \<rho>\<bar> \<le> NA * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>(h - D h) \<bullet> \<rho>\<bar> \<le> norm (h - D h) * norm \<rho>"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> (norm h * NA) * (\<eta> * norm h)"
        using NAb[of h] n\<rho> n\<rho>0 NA0 nh0 by (intro mult_mono) auto
      finally show ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have n2: "(norm \<rho>)\<^sup>2 \<le> \<eta> * (norm h)\<^sup>2"
    proof -
      have "(norm \<rho>)\<^sup>2 \<le> (\<eta> * norm h)\<^sup>2"
        using n\<rho> n\<rho>0 by (intro power_mono) auto
      also have "\<dots> = \<eta> * (\<eta> * (norm h)\<^sup>2)" by (simp add: power2_eq_square field_simps)
      also have "\<dots> \<le> 1 * (\<eta> * (norm h)\<^sup>2)"
        using \<eta>1 \<eta>0 by (intro mult_right_mono) auto
      finally show ?thesis by simp
    qed
    have nDh: "norm (D h) \<le> norm h" by (rule prox_deriv_norm_le[OF cvx D])
    have n3: "\<bar>D h \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>D h \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> norm (D h) * norm (D' \<rho> - \<rho>)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm h * (\<eta> * norm h * NB)"
        using nDh NBb[of \<rho>] n\<rho> NB0 nh0 n\<rho>0
        by (intro mult_mono order_trans[OF NBb[of \<rho>]] mult_right_mono) auto
      finally show ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have n4: "\<bar>\<rho> \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have "\<bar>\<rho> \<bullet> (D' \<rho> - \<rho>)\<bar> \<le> norm \<rho> * norm (D' \<rho> - \<rho>)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm \<rho> * (norm \<rho> * NB)"
        using NBb[of \<rho>] n\<rho>0 by (intro mult_left_mono) auto
      also have "\<dots> = NB * (norm \<rho>)\<^sup>2" by (simp add: power2_eq_square field_simps)
      also have "\<dots> \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n2 NB0 by (intro mult_left_mono) auto
      finally show ?thesis .
    qed
    have nRm: "\<bar>Rm\<bar> \<le> (NA + 1 + 2*NB) * (\<eta> * (norm h)\<^sup>2)"
    proof -
      have a1: "(h - D h) \<bullet> \<rho> \<le> NA * (\<eta> * (norm h)\<^sup>2)"
        and a1': "- ((h - D h) \<bullet> \<rho>) \<le> NA * (\<eta> * (norm h)\<^sup>2)"
        using n1 by (simp_all add: abs_le_iff)
      have a3: "D h \<bullet> (D' \<rho> - \<rho>) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        and a3': "- (D h \<bullet> (D' \<rho> - \<rho>)) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n3 by (simp_all add: abs_le_iff)
      have a4: "\<rho> \<bullet> (D' \<rho> - \<rho>) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        and a4': "- (\<rho> \<bullet> (D' \<rho> - \<rho>)) \<le> NB * (\<eta> * (norm h)\<^sup>2)"
        using n4 by (simp_all add: abs_le_iff)
      have a2: "0 \<le> (norm \<rho>)\<^sup>2" by simp
      have dexp: "(NA + 1 + 2*NB) * (\<eta> * (norm h)\<^sup>2)
          = NA * (\<eta> * (norm h)\<^sup>2) + (\<eta> * (norm h)\<^sup>2)
            + 2 * (NB * (\<eta> * (norm h)\<^sup>2))"
        by (simp add: algebra_simps)
      show ?thesis unfolding rid dexp
        using a1 a1' a2 a3 a3' a4 a4' n2 by (intro abs_leI; linarith)
    qed
    have nN: "\<bar>Nm\<bar> \<le> C * (\<eta> * (norm h)\<^sup>2)"
      unfolding N C_def using nT nRm NA0 NB0 \<eta>0 nh0 by (simp add: field_simps)
    have hk: "norm h \<le> 2 * K * norm k"
    proof -
      have Dh: "D h = k + \<rho>" using kD by simp
      have "norm h \<le> K * norm (D h)" by (rule Kb)
      also have "\<dots> = K * norm (k + \<rho>)" unfolding Dh ..
      also have "\<dots> \<le> K * (norm k + norm \<rho>)"
        using K0 by (intro mult_left_mono norm_triangle_ineq) auto
      also have "\<dots> \<le> K * (norm k + \<eta> * norm h)"
        using n\<rho> K0 by (intro mult_left_mono add_left_mono) auto
      finally have step: "norm h \<le> K * norm k + (K * \<eta>) * norm h"
        by (simp add: field_simps)
      have "K * \<eta> \<le> 1/2" using \<eta>K K0 by (simp add: field_simps)
      hence "(K * \<eta>) * norm h \<le> (1/2) * norm h"
        using nh0 by (intro mult_right_mono) auto
      with step show ?thesis by argo
    qed
    have hk2: "(norm h)\<^sup>2 \<le> 4 * K\<^sup>2 * (norm k)\<^sup>2"
    proof -
      have "(norm h)\<^sup>2 \<le> (2 * K * norm k)\<^sup>2"
        using hk nh0 by (intro power_mono) auto
      thus ?thesis by (simp add: power2_eq_square field_simps)
    qed
    have "C * (\<eta> * (norm h)\<^sup>2) \<le> C * (\<eta> * (4 * K\<^sup>2 * (norm k)\<^sup>2))"
      using hk2 C0 \<eta>0 by (intro mult_left_mono) auto
    also have "\<dots> = (C * 8 * K\<^sup>2) * \<eta> * ((norm k)\<^sup>2 / 2)"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> \<le> \<epsilon> * ((norm k)\<^sup>2 / 2)"
      using \<eta>e C0 K0 nk by (intro mult_right_mono) (auto simp: field_simps)
    finally have fin: "\<bar>Nm\<bar> \<le> \<epsilon> * ((norm k)\<^sup>2 / 2)"
      using nN by linarith
    have nk2: "0 < (norm k)\<^sup>2" using nk by simp
    have "\<bar>Nm\<bar> / (norm k)\<^sup>2 \<le> (\<epsilon> * ((norm k)\<^sup>2 / 2)) / (norm k)\<^sup>2"
      using fin by (intro divide_right_mono) auto
    also have "\<dots> = \<epsilon>/2" using nk2 by (simp add: field_simps)
    also have "\<dots> < \<epsilon>" using \<epsilon> by simp
    finally have "\<bar>Nm\<bar> / (norm k)\<^sup>2 < \<epsilon>" .
    hence "dist (Nm / (norm k)\<^sup>2) 0 < \<epsilon>" by (simp add: dist_real_def)
    thus ?thesis unfolding Nm_def .
  qed
  show "\<forall>\<^sub>F k in at (0::'a). dist ((f (prox f x + k) - f (prox f x)
      - (x - prox f x) \<bullet> k - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) 0 < \<epsilon>"
    unfolding eventually_at using \<delta>3 main by blast
qed

text \<open>The transported form \<open>B = D' - id\<close> inherits symmetry and positive
  semidefiniteness from the resolvent's derivative, so it really is a
  Hessian.\<close>

lemma linear_inj_two_sided_inverse:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lD: "linear D" and injD: "inj D"
  shows "\<exists>D'. linear D' \<and> (\<forall>u. D' (D u) = u) \<and> (\<forall>u. D (D' u) = u)"
proof -
  obtain D' where lin': "linear D'" and inv: "D' \<circ> D = id"
    using linear_injective_left_inverse[OF lD injD] by blast
  have left: "D' (D u) = u" for u using inv by (simp add: pointfree_idE)
  have surjD: "surj D"
    by (rule linear_injective_imp_surjective[OF lD injD]) simp
  have right: "D (D' u) = u" for u
  proof -
    obtain b where ub: "u = D b" using surjD unfolding surj_def by blast
    show ?thesis unfolding ub left ..
  qed
  show ?thesis using lin' left right by blast
qed

lemma prox_deriv_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
  shows "u \<bullet> D v = v \<bullet> D u"
proof -
  have "u \<bullet> (v - D v) = v \<bullet> (u - D u)"
    by (rule moreau_hessian_symmetric[OF cvx D])
  thus ?thesis by (simp add: inner_diff_right inner_commute)
qed

lemma transported_form_symmetric:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
    and right: "\<And>w. D (D' w) = w"
  shows "u \<bullet> (D' v - v) = v \<bullet> (D' u - u)"
proof -
  have "u \<bullet> D' v = D (D' u) \<bullet> D' v" unfolding right ..
  also have "\<dots> = D' v \<bullet> D (D' u)" by (rule inner_commute)
  also have "\<dots> = D' u \<bullet> D (D' v)" by (rule prox_deriv_symmetric[OF cvx D])
  also have "\<dots> = D' u \<bullet> v" unfolding right ..
  also have "\<dots> = v \<bullet> D' u" by (rule inner_commute)
  finally have "u \<bullet> D' v = v \<bullet> D' u" .
  thus ?thesis by (simp add: inner_diff_right inner_commute)
qed

lemma transported_form_psd:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f" and D: "(prox f has_derivative D) (at x)"
    and right: "\<And>w. D (D' w) = w"
  shows "0 \<le> k \<bullet> (D' k - k)"
proof -
  define h where "h = D' k"
  have Dh: "D h = k" unfolding h_def by (rule right)
  have "k \<bullet> (D' k - k) = D h \<bullet> (h - D h)"
    unfolding h_def[symmetric] Dh ..
  also have "\<dots> = h \<bullet> D h - (norm (D h))\<^sup>2"
    by (simp add: inner_diff_right power2_norm_eq_inner inner_commute)
  also have "0 \<le> \<dots>" using prox_deriv_psd[OF cvx D, of h] by simp
  finally show ?thesis by simp
qed

text \<open>Packaging the local statement: where the resolvent is differentiable
  with injective derivative, \<open>f\<close> has a genuine second-order expansion at
  the corresponding proximal point.\<close>

theorem f_alexandrov_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
    and D: "(prox f has_derivative D) (at x)"
    and injD: "inj D"
  shows "\<exists>B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
      \<and> ((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
          - (k \<bullet> B k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have lD: "linear D"
    using has_derivative_bounded_linear[OF D] by (rule bounded_linear.linear)
  obtain D' where lin': "linear D'" and left: "\<And>u. D' (D u) = u"
    and right: "\<And>u. D (D' u) = u"
    using linear_inj_two_sided_inverse[OF lD injD] by blast
  have blD': "bounded_linear D'" using lin' by (simp add: linear_conv_bounded_linear)
  have blB: "bounded_linear (\<lambda>u. D' u - u)"
    by (intro bounded_linear_sub bounded_linear_ident blD')
  have psd: "0 \<le> k \<bullet> (D' k - k)" for k
    by (rule transported_form_psd[OF cvx D right])
  have sym: "u \<bullet> (D' v - v) = v \<bullet> (D' u - u)" for u v
    by (rule transported_form_symmetric[OF cvx D right])
  have lim: "((\<lambda>k. (f (prox f x + k) - f (prox f x) - (x - prox f x) \<bullet> k
      - (k \<bullet> (D' k - k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (rule f_taylor_limit[OF cvx D injD lin' left])
  show ?thesis using blB psd sym lim by blast
qed

text \<open>Two auxiliaries for the measure-theoretic assembly: a non-injective
  linear endomorphism has range of deficient dimension, and an
  almost-everywhere statement for the Borel measure yields a negligible
  exceptional set.\<close>

lemma dim_range_lt_of_not_inj:
  fixes D :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lD: "linear D" and ninj: "\<not> inj D"
  shows "dim (D ` UNIV) < DIM('a)"
proof -
  have nsurj: "\<not> surj D"
  proof
    assume s: "surj D"
    have "inj D" using lD s by (rule linear_surjective_imp_injective) simp
    with ninj show False ..
  qed
  have sub: "subspace (D ` UNIV)"
    using lD subspace_UNIV by (rule linear_subspace_image)
  have le: "dim (D ` UNIV) \<le> DIM('a)" by (rule dim_subset_UNIV)
  have "dim (D ` UNIV) \<noteq> DIM('a)"
  proof
    assume "dim (D ` UNIV) = DIM('a)"
    hence "span (D ` UNIV) = UNIV" by (simp add: dim_eq_full)
    moreover have "span (D ` UNIV) = D ` UNIV" using sub by simp
    ultimately have "D ` UNIV = UNIV" by simp
    thus False using nsurj by simp
  qed
  with le show ?thesis by simp
qed

lemma AE_lborel_negligible:
  fixes P :: "'a::euclidean_space \<Rightarrow> bool"
  assumes ae: "AE x in lborel. P x"
  shows "negligible {x. \<not> P x}"
proof -
  obtain N where N: "N \<in> null_sets lborel"
    and sub: "{x \<in> space lborel. \<not> P x} \<subseteq> N"
    using ae unfolding eventually_ae_filter by blast
  have "N \<in> null_sets lebesgue" using N by (rule null_sets_completionI)
  hence "negligible N" by (simp add: negligible_iff_null_sets)
  moreover have "{x. \<not> P x} \<subseteq> N" using sub by simp
  ultimately show ?thesis by (rule negligible_subset)
qed

subsection \<open>Alexandrov's theorem\<close>

text \<open>Alexandrov's theorem: a finite convex function on a Euclidean space
  is twice differentiable almost everywhere, with a bounded, symmetric,
  positive semidefinite second-order Taylor expansion outside a
  negligible set.

  The proof runs through the Minty resolvent: every point \<open>y\<close> is
  \<open>prox f z\<close> for some \<open>z\<close> (surjectivity of \<open>id + subdiff f\<close>), and where
  the resolvent is differentiable with injective derivative the
  expansion is available.  The exceptional points --- where the
  resolvent fails to be differentiable (Rademacher), or its derivative is
  singular (Sard) --- form two negligible sets.\<close>

theorem convex_alexandrov:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV f"
  shows "negligible {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
      \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
proof -
  define Bad where "Bad = {z. \<not> (\<exists>D. (prox f has_derivative D) (at z) \<and> inj D)}"
  define Nd where "Nd = {z :: 'a. \<not> (prox f) differentiable (at z)}"
  define Sg where "Sg = {z :: 'a. (prox f) differentiable (at z)
      \<and> \<not> inj (frechet_derivative (prox f) (at z))}"
  have BadSub: "Bad \<subseteq> Nd \<union> Sg"
  proof
    fix z assume z: "z \<in> Bad"
    show "z \<in> Nd \<union> Sg"
    proof (cases "(prox f) differentiable (at z)")
      case False
      thus ?thesis unfolding Nd_def by simp
    next
      case True
      hence "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z)"
        by (simp add: frechet_derivative_works)
      hence "\<not> inj (frechet_derivative (prox f) (at z))"
        using z unfolding Bad_def by blast
      thus ?thesis unfolding Sg_def using True by simp
    qed
  qed
  have negNd: "negligible Nd"
    unfolding Nd_def by (rule AE_lborel_negligible[OF prox_differentiable_AE[OF cvx]])
  have negNdIm: "negligible (prox f ` Nd)"
  proof (rule negligible_locally_Lipschitz_image[OF order_refl negNd])
    fix z :: 'a assume "z \<in> Nd"
    have "\<forall>w \<in> Nd \<inter> UNIV. norm (prox f w - prox f z) \<le> 1 * norm (w - z)"
      using prox_lipschitz[OF cvx] by blast
    thus "\<exists>T B. open T \<and> z \<in> T
        \<and> (\<forall>w \<in> Nd \<inter> T. norm (prox f w - prox f z) \<le> B * norm (w - z))"
      by blast
  qed
  have negSgIm: "negligible (prox f ` Sg)"
  proof (rule baby_Sard[OF order_refl])
    fix z :: 'a assume z: "z \<in> Sg"
    hence dz: "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z)"
      unfolding Sg_def by (simp add: frechet_derivative_works)
    show "(prox f has_derivative frechet_derivative (prox f) (at z)) (at z within Sg)"
      by (rule has_derivative_at_withinI[OF dz])
    have lz: "linear (frechet_derivative (prox f) (at z))"
      using has_derivative_bounded_linear[OF dz] by (rule bounded_linear.linear)
    have nz: "\<not> inj (frechet_derivative (prox f) (at z))"
      using z unfolding Sg_def by simp
    show "dim (frechet_derivative (prox f) (at z) ` UNIV) < DIM('a)"
      by (rule dim_range_lt_of_not_inj[OF lz nz])
  qed
  have negBadIm: "negligible (prox f ` Bad)"
  proof (rule negligible_subset[of "prox f ` Nd \<union> prox f ` Sg"])
    show "negligible (prox f ` Nd \<union> prox f ` Sg)"
      using negNdIm negSgIm by (rule negligible_Un)
    show "prox f ` Bad \<subseteq> prox f ` Nd \<union> prox f ` Sg"
      using BadSub by (auto simp: image_Un[symmetric])
  qed
  show ?thesis
  proof (rule negligible_subset[OF negBadIm])
    show "{y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
        \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
        \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0))} \<subseteq> prox f ` Bad"
    proof
      fix y :: 'a
      assume "y \<in> {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
          \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
          \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0))}"
      hence nP: "\<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
          \<and> (\<forall>u v. u \<bullet> B v = v \<bullet> B u)
          \<and> ((\<lambda>k. (f (y + k) - f y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0))" by simp
      obtain q where q: "q \<in> subdiff f y" using subdiff_nonempty[OF cvx] by blast
      have pz: "prox f (y + q) = y" by (rule subdiff_prox[OF cvx q])
      have "y + q \<in> Bad"
      proof (rule ccontr)
        assume "y + q \<notin> Bad"
        then obtain D where D: "(prox f has_derivative D) (at (y + q))" and iD: "inj D"
          unfolding Bad_def by blast
        obtain B where B: "bounded_linear B" "\<forall>k. 0 \<le> k \<bullet> B k"
          "\<forall>u v. u \<bullet> B v = v \<bullet> B u"
          and lim: "((\<lambda>k. (f (prox f (y + q) + k) - f (prox f (y + q))
              - ((y + q) - prox f (y + q)) \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
              \<longlongrightarrow> 0) (at 0)"
          using f_alexandrov_at[OF cvx D iD] by blast
        have lim': "((\<lambda>k. (f (y + k) - f y - q \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0)"
          using lim unfolding pz by simp
        show False using nP B lim' by blast
      qed
      thus "y \<in> prox f ` Bad" using pz by (metis image_eqI)
    qed
  qed
qed

text \<open>The form Crandall--Ishii consumes: a semiconvex function is twice
  differentiable a.e.  Subtracting the quadratic shifts the gradient by
  \<open>c *\<^sub>R y\<close> and the Hessian by \<open>c\<close> times the identity, leaving the
  remainder untouched; positive semidefiniteness is lost.\<close>

corollary semiconvex_alexandrov:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and c :: real
  assumes cvx: "convex_on UNIV (\<lambda>x. u x + (c/2) * (norm x)\<^sup>2)"
  shows "negligible {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
proof (rule negligible_subset[OF convex_alexandrov[OF cvx]])
  show "{y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}
    \<subseteq> {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
  proof (rule subsetI, rule CollectI, rule notI, erule CollectE, erule notE)
    fix y :: 'a
    assume "\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)"
    then obtain p B where blB: "bounded_linear B"
      and symB: "\<And>v w. v \<bullet> B w = w \<bullet> B v"
      and lim: "((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)" by blast
    have blB': "bounded_linear (\<lambda>w. B w - c *\<^sub>R w)"
      by (intro bounded_linear_sub blB bounded_linear_scaleR_right)
    have symB': "v \<bullet> (B w - c *\<^sub>R w) = w \<bullet> (B v - c *\<^sub>R v)" for v w
      using symB[of v w] by (simp add: inner_diff_right inner_commute)
    have eq: "(\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2)
        = (\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)"
    proof (rule ext)
      fix k :: 'a
      have sq: "(norm (y + k))\<^sup>2 = (norm y)\<^sup>2 + 2*(y \<bullet> k) + (norm k)\<^sup>2"
        by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
            inner_commute)
      have i1: "(p - c *\<^sub>R y) \<bullet> k = p \<bullet> k - c * (y \<bullet> k)"
        by (simp add: inner_diff_left)
      have i2: "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
        by (simp add: inner_diff_right power2_norm_eq_inner)
      have num: "u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2
          = u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2"
        unfolding sq i1 i2 by argo
      show "(u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2
          = (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2"
        unfolding num ..
    qed
    have "((\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
        - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      unfolding eq by (rule lim)
    thus "\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
        \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0)"
      using blB' symB' by blast
  qed
qed

text \<open>The same statement, propagating the psd clause \<open>convex_alexandrov\<close>
  establishes: with \<open>W = \<lambda>w. B w - c *\<^sub>R w\<close>, the identity
  \<open>k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c \<parallel>k\<parallel>\<^sup>2\<close> gives the lower bound
  \<open>-c \<parallel>k\<parallel>\<^sup>2 \<le> k \<bullet> W k\<close> for free, which a compactness argument over a
  family of Hessians needs.\<close>

corollary semiconvex_alexandrov_bounded:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and c :: real
  assumes cvx: "convex_on UNIV (\<lambda>x. u x + (c/2) * (norm x)\<^sup>2)"
  shows "negligible {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> B k)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
proof (rule negligible_subset[OF convex_alexandrov[OF cvx]])
  show "{y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> B k)
      \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}
    \<subseteq> {y. \<not> (\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0))}"
  proof (rule subsetI, rule CollectI, rule notI, erule CollectE, erule notE)
    fix y :: 'a
    assume "\<exists>p B. bounded_linear B \<and> (\<forall>k. 0 \<le> k \<bullet> B k)
      \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
      \<and> ((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)"
    then obtain p B where blB: "bounded_linear B"
      and psdB: "\<forall>k. 0 \<le> k \<bullet> B k"
      and symB: "\<forall>v w. v \<bullet> B w = w \<bullet> B v"
      and lim: "((\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
          - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
          \<longlongrightarrow> 0) (at 0)" by blast
    have blB': "bounded_linear (\<lambda>w. B w - c *\<^sub>R w)"
      by (intro bounded_linear_sub blB bounded_linear_scaleR_right)
    have symB': "v \<bullet> (B w - c *\<^sub>R w) = w \<bullet> (B v - c *\<^sub>R v)" for v w
      using symB by (simp add: inner_diff_right inner_commute)
    have lowB': "- (c * (norm k)\<^sup>2) \<le> k \<bullet> (B k - c *\<^sub>R k)" for k
    proof -
      have split: "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
        by (simp add: inner_diff_right power2_norm_eq_inner)
      have "0 \<le> k \<bullet> B k" using psdB by blast
      then show ?thesis unfolding split by linarith
    qed
    have eq: "(\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2)
        = (\<lambda>k. (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)"
    proof (rule ext)
      fix k :: 'a
      have sq: "(norm (y + k))\<^sup>2 = (norm y)\<^sup>2 + 2*(y \<bullet> k) + (norm k)\<^sup>2"
        by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
            inner_commute)
      have i1: "(p - c *\<^sub>R y) \<bullet> k = p \<bullet> k - c * (y \<bullet> k)"
        by (simp add: inner_diff_left)
      have i2: "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
        by (simp add: inner_diff_right power2_norm_eq_inner)
      have num: "u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2
          = u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2"
        unfolding sq i1 i2 by argo
      show "(u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
            - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2
          = (u (y + k) + (c/2) * (norm (y + k))\<^sup>2
            - (u y + (c/2) * (norm y)\<^sup>2) - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2"
        unfolding num ..
    qed
    have "((\<lambda>k. (u (y + k) - u y - (p - c *\<^sub>R y) \<bullet> k
        - (k \<bullet> (B k - c *\<^sub>R k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      unfolding eq by (rule lim)
    thus "\<exists>p B. bounded_linear B \<and> (\<forall>v w. v \<bullet> B w = w \<bullet> B v)
        \<and> (\<forall>k. - (c * (norm k)\<^sup>2) \<le> k \<bullet> B k)
        \<and> ((\<lambda>k. (u (y + k) - u y - p \<bullet> k - (k \<bullet> B k)/2) / (norm k)\<^sup>2)
            \<longlongrightarrow> 0) (at 0)"
      using blB' symB' lowB' by blast
  qed
qed


(*<*)
end
(*>*)
