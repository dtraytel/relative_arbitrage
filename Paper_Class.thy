(*
  Title:   Paper_Class.thy
  Content: The class P_x of Eq. (1.7) of arXiv:2512.17702, encoded as
           laws of the PAIR (X, <X>) on the path space, following the
           paper's own proof of Lemma 2.3: the covariation is carried
           as a second, uniformly Lipschitz path component whose
           difference quotients lie in the compact convex constraint
           set S = Pi_constraint k \<inter> {eigen_ub L} (Lemma 2.1 =
           lemma_2_1_exact identifies S with the convex hull of the
           unconvexified sufficient-volatility set (1.4)).

           This file provides the DEFINITIONAL layer of plan item NC-1
           (see PLAN_THEOREM_1_1.md \<section>NC); the closedness of the class
           (NC-2/3/4) and the bridge to the stopped_market witnesses
           build on it.

  STATUS:  written while the PIDE session awaited a restart; verify
           green before extending.
*)

theory Paper_Class
  imports Path_Space Exit_Semicontinuity Relative_Arbitrage_Convexity
begin

section \<open>The constraint set of Eq. (1.5) with the technical cap\<close>

definition sconstraint :: "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite^'n) set" where
  "sconstraint k L = Pi_constraint k \<inter> {a. eigen_ub a L}"

text \<open>First NC-2 obligations on this set (prove after the PIDE
  restart): \<open>convex (sconstraint k L)\<close> (the partial traces are concave
  — see the proof of \<open>lemma_2_1_exact\<close> — and the \<open>eigen_ub\<close> cap is an
  intersection of half-spaces), \<open>closed (sconstraint k L)\<close>, and
  boundedness (trace \<le> n L), giving compactness.\<close>

section \<open>The pair path space and its coordinate processes\<close>

text \<open>Paths take values in \<open>real^'n \<times> real^'n^'n\<close>: the process together
  with its running covariation.  \<open>path_law\<close>, \<open>path_metric\<close> and the
  tightness machinery are polymorphic in the value type, so the whole
  Section-2 toolchain applies verbatim.\<close>

definition outerp :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "outerp x = (\<chi> i j. x $ i * x $ j)"

abbreviation pair_proc ::
  "real \<Rightarrow> (real \<Rightarrow> real^'n::finite \<times> real^'n^'n)
     \<Rightarrow> real^'n \<times> real^'n^'n"
  where "pair_proc t \<omega> \<equiv> \<omega> t"

abbreviation pairX ::
  "real \<Rightarrow> (real \<Rightarrow> real^'n::finite \<times> real^'n^'n) \<Rightarrow> real^'n"
  where "pairX t \<omega> \<equiv> fst (\<omega> t)"

abbreviation pairY ::
  "real \<Rightarrow> (real \<Rightarrow> real^'n::finite \<times> real^'n^'n) \<Rightarrow> real^'n^'n"
  where "pairY t \<omega> \<equiv> snd (\<omega> t)"

section \<open>The class \<open>P\<^sub>x\<close> of Eq. (1.7), capped at horizon \<open>T\<close>\<close>

text \<open>Operational reading of (1.7), equivalent by compensator
  uniqueness: a law of the pair \<open>(X, Y)\<close> under which \<open>X\<close> is a
  martingale from \<open>x\<close>, \<open>Y\<close> starts at \<open>0\<close> with difference quotients in
  the constraint set (hence \<open>Y\<close> is Lipschitz with a.e. derivative in
  \<open>S\<close> by Lebesgue differentiation, NC-4), and \<open>X X\<^sup>T - Y\<close> is a
  martingale, so \<open>Y\<close> IS the quadratic covariation.  The horizon cap at
  \<open>T\<close> is invisible for \<open>T\<close> beyond the uniform exit-time bound
  (paper's Lemma 1.9 / Eq. (3.10)); the bridge is part of NC-1.\<close>

definition paper_pair_class ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n::finite
     \<Rightarrow> ((real \<Rightarrow> real^'n \<times> real^'n^'n) measure) set"
  where
  "paper_pair_class k L T x = {Q.
     prob_space Q \<and>
     sets Q = sets (borel_of (mtopology_of (path_metric T
       :: (real \<Rightarrow> real^'n \<times> real^'n^'n) metric))) \<and>
     (AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and>
     (AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s))
          \<in> sconstraint k L) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0 (\<lambda>t \<omega>. fst (\<omega> t)) \<and>
     martingale Q
       (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
       (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))}"

section \<open>The value function of Eq. (1.6), capped at horizon \<open>T\<close>\<close>

definition paper_v ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "paper_v k L T K x =
     Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
       ` paper_pair_class k L T x)"

end
