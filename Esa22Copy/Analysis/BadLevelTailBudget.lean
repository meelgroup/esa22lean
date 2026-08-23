import Esa22Copy.Analysis.CriticalLevel

/-!
# Numerical budget for excessive relaxed levels

The threshold chosen by the algorithm pays for the fixed-prefix upper tail with
budget `delta / (4m)`.
-/

namespace Esa22Copy

/--
INTERNAL: the exponential upper tail at threshold `T` fits the per-prefix
failure budget allocated to excessive relaxed levels.
-/
theorem bad_level_tail_budget (P : Params) :
    2 * Real.exp (-(threshold P : Real) / 6) ≤
      P.delta / (4 * (P.m : Real)) := by
  have heps_pos : 0 < P.eps := P.heps.1
  have heps_le_one : P.eps ≤ 1 := P.heps.2.le
  have hdelta_pos : 0 < P.delta := P.hdelta.1
  have hdelta_lt_one : P.delta < 1 := P.hdelta.2
  have hm_one : (1 : Real) ≤ (P.m : Real) := by
    exact_mod_cast P.hm
  let R : Real := 8 * (P.m : Real) / P.delta
  have hR : 1 < R := by
    dsimp [R]
    apply (lt_div_iff₀ hdelta_pos).2
    nlinarith
  have hlogR_pos : 0 < Real.log R := Real.log_pos hR
  have hlogb_pos : 0 < Real.logb 2 R := Real.logb_pos (by norm_num) hR
  have heps_sq_pos : 0 < P.eps ^ 2 := sq_pos_of_pos heps_pos
  have heps_sq_le_one : P.eps ^ 2 ≤ 1 := by
    simpa [pow_two] using mul_self_le_mul_self heps_pos.le heps_le_one
  have hcoeff : (12 : Real) ≤ 12 / P.eps ^ 2 := by
    apply (le_div_iff₀ heps_sq_pos).2
    nlinarith
  have hthreshold : 12 * Real.logb 2 R ≤ (threshold P : Real) := by
    calc
      12 * Real.logb 2 R ≤
          (12 / P.eps ^ 2) * Real.logb 2 R :=
        mul_le_mul_of_nonneg_right hcoeff hlogb_pos.le
      _ ≤ (threshold P : Real) := by
        simpa [threshold, R] using
          (Nat.le_ceil
            ((12 / P.eps ^ 2) *
              Real.logb 2 (8 * (P.m : Real) / P.delta)))
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ (2 : Real) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlog_le_logb : Real.log R ≤ Real.logb 2 R := by
    rw [Real.logb]
    apply (le_div_iff₀ hlog_two_pos).2
    have hproduct : 0 ≤ Real.log R * (1 - Real.log 2) :=
      mul_nonneg hlogR_pos.le (sub_nonneg.mpr hlog_two_le_one)
    nlinarith
  have hsix_log : 6 * Real.log R ≤ (threshold P : Real) := by
    calc
      6 * Real.log R ≤ 6 * Real.logb 2 R := by
        exact mul_le_mul_of_nonneg_left hlog_le_logb (by norm_num)
      _ ≤ 12 * Real.logb 2 R := by nlinarith
      _ ≤ (threshold P : Real) := hthreshold
  have hneg : -(threshold P : Real) / 6 ≤ -Real.log R := by
    linarith
  have hexp : Real.exp (-(threshold P : Real) / 6) ≤ R⁻¹ := by
    calc
      Real.exp (-(threshold P : Real) / 6) ≤ Real.exp (-Real.log R) :=
        Real.exp_le_exp.mpr hneg
      _ = R⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (lt_trans (by norm_num) hR)]
  have hdelta_ne : P.delta ≠ 0 := ne_of_gt hdelta_pos
  have hm_pos : (0 : Real) < (P.m : Real) := lt_of_lt_of_le (by norm_num) hm_one
  have hm_ne : (P.m : Real) ≠ 0 := ne_of_gt hm_pos
  have hR_inv : R⁻¹ = P.delta / (8 * (P.m : Real)) := by
    dsimp [R]
    field_simp
  calc
    2 * Real.exp (-(threshold P : Real) / 6) ≤ 2 * R⁻¹ :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = P.delta / (4 * (P.m : Real)) := by rw [hR_inv]; ring

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · closed the ceiling/log-base numerical budget directly
* r2 · reduced · isolated the ceiling/log-base numerical budget
-/
