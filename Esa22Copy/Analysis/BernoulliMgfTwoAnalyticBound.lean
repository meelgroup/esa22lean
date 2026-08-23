import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Analytic bound for the base-two Bernoulli moment estimate

This file turns the elementary moment expression used in a Bernoulli upper-tail
argument into the exponential bound required by the sampling analysis.
-/

namespace Esa22Copy

/--
INTERNAL: the base-two moment bound decays as `exp (-T / 6)` when its Bernoulli mean
is less than half the threshold.
-/
theorem bernoulli_mgf_two_analytic_bound (n k T : Nat)
    (hmean : (n : Real) * (2 : Real)⁻¹ ^ k < (T : Real) / 2) :
    (2 : Real)⁻¹ ^ T * (1 + (2 : Real)⁻¹ ^ k) ^ n ≤
      Real.exp (-(T : Real) / 6) := by
  let p : Real := (2 : Real)⁻¹ ^ k
  have hp : 0 ≤ p := by
    dsimp [p]
    positivity
  have hone : 1 + p ≤ Real.exp p := by
    simpa [add_comm] using Real.add_one_le_exp p
  have hpow : (1 + p) ^ n ≤ Real.exp ((n : Real) * p) := by
    calc
      (1 + p) ^ n ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (by positivity) hone n
      _ = Real.exp ((n : Real) * p) := by
        rw [← Real.exp_nat_mul]
  have hlog : (2 / 3 : Real) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have htwo : (2 : Real)⁻¹ ^ T = Real.exp (-(T : Real) * Real.log 2) := by
    calc
      (2 : Real)⁻¹ ^ T = (Real.exp (-Real.log 2)) ^ T := by
        congr 1
        rw [Real.exp_neg, Real.exp_log]
        norm_num
      _ = Real.exp ((T : Real) * (-Real.log 2)) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (-(T : Real) * Real.log 2) := by ring_nf
  have hexponent :
      -(T : Real) * Real.log 2 + (n : Real) * p ≤ -(T : Real) / 6 := by
    have hT : 0 ≤ (T : Real) := by positivity
    have hm : (n : Real) * p < (T : Real) / 2 := by
      simpa [p] using hmean
    have hTlog : (T : Real) * (2 / 3 : Real) ≤ (T : Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog hT
    linarith
  calc
    (2 : Real)⁻¹ ^ T * (1 + (2 : Real)⁻¹ ^ k) ^ n =
        (2 : Real)⁻¹ ^ T * (1 + p) ^ n := by rfl
    _ ≤ (2 : Real)⁻¹ ^ T * Real.exp ((n : Real) * p) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp (-(T : Real) * Real.log 2 + (n : Real) * p) := by
      rw [htwo, ← Real.exp_add]
    _ ≤ Real.exp (-(T : Real) / 6) := Real.exp_le_exp.mpr hexponent

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · base-two moment estimate bounded by `exp (-T / 6)`
-/
