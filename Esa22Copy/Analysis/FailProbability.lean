import Esa22Copy.Analysis.RunFailEventEqStateFailure
import Esa22Copy.Analysis.RunStateFailureProbability
import Esa22Copy.Analysis.ThresholdFailureBudget

/-!
# Probability of explicit failure

This is the paper's first-failure union bound: at any one of the `m` stream
positions all threshold-many provisional samples survive thinning with probability
`2⁻ᵗʰʳᵉˢʰᵒˡᵈ`.
-/

namespace Esa22Copy

open scoped ENNReal

/--
PAPER: esa22-final.tex:523-538, Claim `lm:fail`.
-/
theorem fail_probability_le (P : Params) (A : Stream P) :
    Arlib.Approximation.outProbR (run P A) (failEvent P) ≤ P.delta / 8 := by
  rw [run_failEvent_eq_state_failure]
  calc
    ((runState P A).toOuterMeasure {s | FailedState s}).toReal ≤
        ((P.m : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P)).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)))
      · exact runState_failure_probability_le P A
    _ = (P.m : ℝ) * ((1 / 2 : ℝ) ^ threshold P) := by
      simp
    _ ≤ P.delta / 8 := threshold_failure_budget P

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · closed `fail_probability_le` from the step/fold and threshold-budget lemmas
-/
