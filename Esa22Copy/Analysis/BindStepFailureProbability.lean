import Esa22Copy.Analysis.StepFailureProbability

/-!
# A one-step failure bound for an arbitrary input distribution

Integrating the conditional transition estimate over an invariant-supported PMF
increases failure mass by at most one copy of the per-step budget.
-/

namespace Esa22Copy

open scoped ENNReal

/--
INTERNAL: packages the conditional step estimate into the unconditional estimate
needed by the stream-fold induction.
-/
theorem bind_step_failure_probability_le (P : Params) (a : Item P)
    (μ : PMF (State P))
    (hμ : ∀ s ∈ μ.support, StateSpaceInvariant P s) :
    (μ.bind (step P a)).toOuterMeasure {t | FailedState t} ≤
      μ.toOuterMeasure {s | FailedState s} +
        ((2 : ℝ≥0∞)⁻¹) ^ threshold P := by
  classical
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    ∑' s, μ s * (step P a s).toOuterMeasure {t | FailedState t} ≤
        ∑' s, ({s | FailedState s}.indicator μ s +
          μ s * (((2 : ℝ≥0∞)⁻¹) ^ threshold P)) := by
      apply ENNReal.tsum_le_tsum
      intro s
      by_cases hs : s ∈ μ.support
      · have hstep := step_failure_probability_le P a s (hμ s hs)
        by_cases hfailed : FailedState s
        · rw [if_pos hfailed] at hstep
          calc
            μ s * (step P a s).toOuterMeasure {t | FailedState t} ≤ μ s * 1 :=
              mul_le_mul_right hstep (μ s)
            _ ≤ {s | FailedState s}.indicator μ s +
                μ s * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
              simp [Set.indicator, hfailed]
        · rw [if_neg hfailed] at hstep
          calc
            μ s * (step P a s).toOuterMeasure {t | FailedState t} ≤
                μ s * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) :=
              mul_le_mul_right hstep (μ s)
            _ ≤ {s | FailedState s}.indicator μ s +
                μ s * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
              simp [Set.indicator, hfailed]
      · have hz : μ s = 0 := (PMF.apply_eq_zero_iff μ s).2 hs
        simp [hz]
    _ = (∑' s, {s | FailedState s}.indicator μ s) +
        ∑' s, μ s * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := ENNReal.tsum_add
    _ = μ.toOuterMeasure {s | FailedState s} +
        (∑' s, μ s) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
      rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]
    _ = μ.toOuterMeasure {s | FailedState s} +
        ((2 : ℝ≥0∞)⁻¹) ^ threshold P := by simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · integrated the supported conditional estimate by an ENNReal `tsum`
-/
