import Esa22Copy.Model.Prelude

/-!
# Threshold arithmetic for the failure budget

The threshold chosen by the algorithm makes the union-bound expression at most
the paper's allotted failure probability `delta / 8`.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:534-538, the final threshold inequality in Claim `lm:fail`.
-/
theorem threshold_failure_budget (P : Params) :
    (P.m : ℝ) * ((1 / 2 : ℝ) ^ threshold P) ≤ P.delta / 8 := by
  have hm_pos : 0 < (P.m : ℝ) := by
    exact_mod_cast P.hm
  have hm_one : 1 ≤ (P.m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt P.hm))
  have hdelta_pos : 0 < P.delta := P.hdelta.1
  have hdelta_lt_one : P.delta < 1 := P.hdelta.2
  have hx : 1 < 8 * (P.m : ℝ) / P.delta := by
    rw [lt_div_iff₀ hdelta_pos]
    nlinarith
  have hlog_pos : 0 < Real.logb 2 (8 * (P.m : ℝ) / P.delta) :=
    Real.logb_pos (by norm_num) hx
  have heps_sq_pos : 0 < P.eps ^ 2 := sq_pos_of_pos P.heps.1
  have heps_product : 0 ≤ P.eps * (1 - P.eps) :=
    mul_nonneg P.heps.1.le (sub_nonneg.mpr P.heps.2.le)
  have heps_sq_le_one : P.eps ^ 2 ≤ 1 := by
    nlinarith
  have hcoefficient : 1 ≤ 12 / P.eps ^ 2 := by
    rw [le_div_iff₀ heps_sq_pos]
    nlinarith
  have hthreshold :
      Real.logb 2 (8 * (P.m : ℝ) / P.delta) ≤ (threshold P : ℝ) := by
    calc
      Real.logb 2 (8 * (P.m : ℝ) / P.delta) ≤
          (12 / P.eps ^ 2) * Real.logb 2 (8 * (P.m : ℝ) / P.delta) :=
        le_mul_of_one_le_left hlog_pos.le hcoefficient
      _ ≤ (threshold P : ℝ) := by
        unfold threshold
        exact Nat.le_ceil _
  have hpower :
      (1 / 2 : ℝ) ^ threshold P ≤
        (1 / 2 : ℝ) ^ Real.logb 2 (8 * (P.m : ℝ) / P.delta) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)).2 hthreshold
  have hlog_power :
      (1 / 2 : ℝ) ^ Real.logb 2 (8 * (P.m : ℝ) / P.delta) =
        (8 * (P.m : ℝ) / P.delta)⁻¹ := by
    rw [one_div, Real.inv_rpow (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (lt_trans zero_lt_one hx)]
  calc
    (P.m : ℝ) * ((1 / 2 : ℝ) ^ threshold P) ≤
        (P.m : ℝ) *
          ((1 / 2 : ℝ) ^ Real.logb 2 (8 * (P.m : ℝ) / P.delta)) :=
      mul_le_mul_of_nonneg_left hpower hm_pos.le
    _ = (P.m : ℝ) * (8 * (P.m : ℝ) / P.delta)⁻¹ := by rw [hlog_power]
    _ = P.delta / 8 := by
      rw [inv_div]
      field_simp [hm_pos.ne']

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · bounded the logarithm by the ceiling threshold and converted base-two rpow
* r1 · reduced · isolated the ceiling/logarithm calculation from the probability argument
-/
