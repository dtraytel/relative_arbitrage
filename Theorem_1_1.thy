section \<open>Theorem 1.1: the assembly point\<close>

text \<open>
  The join of the development (STATUS.md, task 28). Theorem 1.1 of
  arXiv:2512.17702 asserts that the value function \<open>v\<close> of Eq. (1.6) is the
  unique upper semicontinuous viscosity solution of Eq. (1.9)--(1.10) with
  zero boundary values. Its full proof requires Section 2 (Lemmas 2.2/2.3 and
  Proposition 2.4, task 25), Section 4's uniqueness (task 26) and Section 5's
  continuity (task 27). This theory collects the parts provable TODAY, for
  the ball \<open>K = cball 0 r\<close> where Section 4 is unconditional:

  \<^item> the value-function upper bound \<open>v \<le> ball_v\<close> everywhere (the \<open>\<le>\<close> half of
    the identification of \<open>v\<close>, via Example 3.1's optimal-boundary analysis);
  \<^item> the boundary identification \<open>v = ball_v = 0\<close> on the sphere;
  \<^item> the uniqueness clause: ANY continuous viscosity solution with \<open>ball_v\<close>'s
    boundary data coincides with \<open>ball_v\<close> on the ball — so once the DPP
    machinery of task 25 delivers that \<open>v\<close> is a viscosity solution with the
    right boundary data and the matching lower bound, Theorem 1.1 for the
    ball follows by instantiating the third clause at \<open>u = v\<close>.

  What is missing, and where it comes from: upper semicontinuity of \<open>v\<close> and
  the viscosity property (Prop 2.4 via Lemmas 2.2/2.3); the lower bound
  \<open>ball_v \<le> v\<close> at interior points (the martingale construction of
  Section 3.1, which needs weak existence for Eq. (3.11)); and general
  compact \<open>K\<close> (Theorem 4.2(a), behind Crandall--Ishii).

  STATUS OF THE THIRD ITEM (2026-07-31). \<open>Comparison_Assembly\<close> is now imported,
  and it carries the Crandall--Ishii development: Rademacher, Alexandrov,
  Jensen's lemma, the theorem on sums, the envelope calculus, and the closing
  chain of Theorem 4.2(a). Its endpoint is
  \<open>comparison_supconv_sequence_complete\<close>, which derives \<open>False\<close> from the two
  viscosity properties together with a SEQUENCE of Jensen applications: for
  each index, a doubled maximiser, its Alexandrov jet, and the point at which
  each sup-convolution is attained, plus convergence of the four resulting
  sequences and \<open>p \<noteq> 0\<close> at the limit.

  What still blocks general \<open>K\<close> is therefore not the Crandall--Ishii analysis
  but the CONSTRUCTION that feeds it: producing that sequence from the doubling
  of \<open>\<theta> u\<close> against \<open>w\<close> on \<open>K \<times> K\<close>, with a shrinking Jensen tilt. The
  existence ingredients for it are proved (\<open>doubling_maximiser_exists\<close>,
  \<open>doubling_complete\<close>, \<open>doubled_supconv_jet_exists\<close>); what is not written is
  their instantiation as a single indexed family.

  NOTE on imports: Value\_Function (probabilistic chain) and
  Relative\_Arbitrage\_Comparison (Envelopes chain) share draft ancestors, so
  this theory is BATCH-ONLY, like Path\_Tightness\_Market. (Adding
  \<open>Comparison_Assembly\<close> as a third import does NOT change that: it builds
  green. Note also that the analogous "batch-only" claim once recorded for
  \<open>Comparison_Assembly\<close> itself was simply WRONG -- PIDE holds that theory
  fine -- so this note should be re-tested rather than trusted.)
\<close>

theory Theorem_1_1
  imports Value_Function Relative_Arbitrage_Comparison Comparison_Assembly
begin

theorem theorem_1_1_ball_fragment:
  fixes x0 :: "real^'n::finite" and u :: "real^'n \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
  shows "val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
    and "norm x0 = r \<Longrightarrow> val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
    and "continuous_on (cball 0 r) u \<Longrightarrow>
         visc_sol k L (ball (0::real^'n) r) u \<Longrightarrow>
         (\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r \<Longrightarrow>
            u y = ball_v r k y) \<Longrightarrow>
         x0 \<in> ball (0::real^'n) r \<Longrightarrow> u x0 = ball_v r k x0"
proof -
  show "val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
    by (rule val_fn_le_ball_v)
  show "norm x0 = r \<Longrightarrow> val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
    by (rule val_fn_boundary)
  assume cu: "continuous_on (cball 0 r) u"
    and u: "visc_sol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r \<Longrightarrow>
        u y = ball_v r k y"
    and x0: "x0 \<in> ball (0::real^'n) r"
  have sub: "visc_subsol k L (ball (0::real^'n) r) u"
    and sup: "visc_supersol k L (ball (0::real^'n) r) u"
    using u by (auto simp: visc_sol_def)
  have le: "u x0 \<le> ball_v r k x0"
    by (rule visc_subsol_le_ball_v[OF k L r cu sub _ x0]) (simp add: bd)
  have ge: "ball_v r k x0 \<le> u x0"
    by (rule ball_v_le_visc_supersol[OF k L r cu sup _ x0]) (simp add: bd)
  from le ge show "u x0 = ball_v r k x0" by simp
qed

end
