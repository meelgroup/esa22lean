import Esa22Copy.Analysis.RunPeak

/-!
# Threshold concentration budget

The ceiling in the threshold definition converts the final exponential tail
into the per-level failure budget `delta / (4m)`.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:764-777, substitution of the threshold into the
Chernoff exponent and allocation of the `delta / 4` budget across levels.
-/
theorem threshold_chernoff_budget (P : Params) :
    2 * Real.exp (-(P.eps ^ 2 * (threshold P : Real)) / 12) ≤
      P.delta / (4 * (P.m : Real)) := by
  have hepssq : 0 < P.eps ^ 2 := sq_pos_of_pos P.heps.1
  have hdelta : 0 < P.delta := P.hdelta.1
  have hm : 0 < (P.m : Real) := by exact_mod_cast P.hm
  let x : Real := 8 * (P.m : Real) / P.delta
  have hxone : 1 < x := by
    dsimp [x]
    rw [lt_div_iff₀ hdelta]
    have hmone : 1 ≤ (P.m : Real) := by exact_mod_cast P.hm
    nlinarith [P.hdelta.2]
  have hx : 0 < x := zero_lt_one.trans hxone
  have hceil :
      (12 / P.eps ^ 2) * Real.logb 2 x ≤ (threshold P : Real) := by
    unfold threshold
    exact Nat.le_ceil _
  have hlog_budget :
      Real.logb 2 x ≤ P.eps ^ 2 * (threshold P : Real) / 12 := by
    calc
      Real.logb 2 x =
          P.eps ^ 2 * ((12 / P.eps ^ 2) * Real.logb 2 x) / 12 := by
        field_simp [ne_of_gt P.heps.1]
      _ ≤ P.eps ^ 2 * (threshold P : Real) / 12 := by
        gcongr
  have hlogtwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogtwo_le : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hlogb_ge : Real.log x ≤ Real.logb 2 x := by
    rw [Real.logb, le_div_iff₀ hlogtwo_pos]
    exact mul_le_of_le_one_right (Real.log_nonneg hxone.le) hlogtwo_le
  have hexp :
      Real.exp (-(P.eps ^ 2 * (threshold P : Real)) / 12) ≤ 1 / x := by
    calc
      Real.exp (-(P.eps ^ 2 * (threshold P : Real)) / 12) ≤
          Real.exp (-(Real.logb 2 x)) :=
        Real.exp_le_exp.mpr (by linarith [hlog_budget])
      _ ≤ Real.exp (-(Real.log x)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlogb_ge)
      _ = 1 / x := by
        rw [Real.exp_neg, Real.exp_log hx]
        simp [one_div]
  calc
    2 * Real.exp (-(P.eps ^ 2 * (threshold P : Real)) / 12) ≤
        2 * (1 / x) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = P.delta / (4 * (P.m : Real)) := by
      dsimp [x]
      field_simp
      norm_num

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · converted the base-two threshold logarithm to the natural exponential budget
-/
