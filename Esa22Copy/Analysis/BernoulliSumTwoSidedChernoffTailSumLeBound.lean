import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Assemble the one-sided Chernoff estimates

This scalar step weakens the lower-tail exponent to the upper-tail exponent and combines
the two estimates with the paper's factor of two.
-/

namespace Esa22Copy

/--
INTERNAL: Upper and lower Chernoff estimates combine to the common `2 + β` denominator
used by `bernoulliSum_twoSidedChernoff`, for every positive `β`.
-/
theorem bernoulliSum_twoSidedChernoff_tail_sum_le_bound
    (upper lower μ β : Real) (hμ : 0 ≤ μ) (hβ : 0 < β)
    (hupper : upper ≤ Real.exp (-(β ^ 2 * μ) / (2 + β)))
    (hlower : lower ≤ Real.exp (-(β ^ 2 * μ) / 2)) :
    upper + lower ≤ 2 * Real.exp (-(β ^ 2 * μ) / (2 + β)) := by
  have hA : 0 ≤ β ^ 2 * μ := mul_nonneg (sq_nonneg β) hμ
  have h2 : (0 : Real) < 2 := by norm_num
  have hden : (2 : Real) ≤ 2 + β := by linarith
  have hfrac : β ^ 2 * μ / (2 + β) ≤ β ^ 2 * μ / 2 :=
    div_le_div_of_nonneg_left hA h2 hden
  have hexp : Real.exp (-(β ^ 2 * μ) / 2) ≤
      Real.exp (-(β ^ 2 * μ) / (2 + β)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hfrac
  calc
    upper + lower ≤ Real.exp (-(β ^ 2 * μ) / (2 + β)) +
        Real.exp (-(β ^ 2 * μ) / (2 + β)) :=
      add_le_add hupper (hlower.trans hexp)
    _ = 2 * Real.exp (-(β ^ 2 * μ) / (2 + β)) := by ring

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · compared the two nonnegative exponents and combined the resulting bounds
-/
