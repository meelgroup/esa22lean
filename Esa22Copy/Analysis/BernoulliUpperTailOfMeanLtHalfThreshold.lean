import Arlib.Probability.Chernoff
import Esa22Copy.Analysis.BernoulliMgfTwoAnalyticBound
import Esa22Copy.Analysis.BernoulliPatternUpperMgfTwo
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# A threshold upper tail from the complete Bernoulli pattern law

This file is the distributional bridge needed when an algorithmic PMF is known through
the probability of every Boolean membership pattern, rather than presented definitionally
as Arlib's finite product probability space.
-/

namespace Esa22Copy

open scoped BigOperators

/--
INTERNAL: an exact independent Bernoulli pattern law and a mean below half the threshold
imply the fixed-threshold upper-tail estimate.
-/
theorem bernoulli_upper_tail_of_mean_lt_half_threshold
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (μ : PMF Ω) (success : Ω → I → Bool) (k T : Nat)
    (hlaw : ∀ wanted : I → Bool,
      μ.toOuterMeasure
          {ω | ∀ a : I, success ω a = true ↔ wanted a = true} =
        ∏ a : I,
          if wanted a = true then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹)
    (hmean : (Fintype.card I : Real) * (2 : Real)⁻¹ ^ k < (T : Real) / 2) :
    (μ.toOuterMeasure
      {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
        2 * Real.exp (-(T : Real) / 6) := by
  calc
    (μ.toOuterMeasure
        {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
        (2 : Real)⁻¹ ^ T *
          (1 + (2 : Real)⁻¹ ^ k) ^ Fintype.card I :=
      bernoulli_pattern_upper_mgf_two μ success k T hlaw
    _ ≤ Real.exp (-(T : Real) / 6) :=
      bernoulli_mgf_two_analytic_bound (Fintype.card I) k T hmean
    _ ≤ 2 * Real.exp (-(T : Real) / 6) := by
      nlinarith [Real.exp_pos (-(T : Real) / 6)]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · composed the complete-pattern MGF bound with its analytic estimate
* r3 · open · isolated transport from complete Boolean-pattern probabilities to Arlib's product-space Chernoff bound
-/
