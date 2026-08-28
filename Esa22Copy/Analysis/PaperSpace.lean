import Esa22Copy.Interface.Pseudocode

/-!
# The displayed asymptotic item-space bound

This is the closed analytic bookkeeping proposition corresponding to the paper's
threshold times its per-item bit charge.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:507-508, the displayed worst-case item-space calculation.
-/
theorem paperItemSpaceBigO_proof : PaperItemSpaceBigO := by
  refine ⟨98, by norm_num, ?_⟩
  intro P hn hm
  have heps : 0 < P.eps := P.heps.1
  have heps0 : P.eps ≠ 0 := ne_of_gt heps
  have hdelta : 0 < P.delta := P.hdelta.1
  have hdelta0 : P.delta ≠ 0 := ne_of_gt hdelta
  have hnreal : (2 : Real) ≤ P.n := by exact_mod_cast hn
  have hmreal : (2 : Real) ≤ P.m := by exact_mod_cast hm
  have hn0 : (P.n : Real) ≠ 0 := by positivity
  have hm0 : (P.m : Real) ≠ 0 := by positivity
  have hlogTwo : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have hlogEight : Real.logb 2 8 = 3 := by
    calc
      Real.logb 2 8 = Real.logb 2 ((2 : Real) ^ 3) := by norm_num
      _ = (3 : Nat) * Real.logb 2 2 := Real.logb_pow 2 2 3
      _ = 3 := by rw [hlogTwo]; norm_num
  have hlogn : 1 ≤ Real.logb 2 (P.n : Real) := by
    rw [← hlogTwo]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hnreal
  have hlogm : 1 ≤ Real.logb 2 (P.m : Real) := by
    rw [← hlogTwo]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hmreal
  have hdeltaInv : 1 < P.delta⁻¹ := (one_lt_inv₀ hdelta).2 P.hdelta.2
  have hlogdelta : 0 ≤ Real.logb 2 P.delta⁻¹ :=
    (Real.logb_pos (by norm_num) hdeltaInv).le
  have hsum : 1 ≤
      Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹ := by linarith
  have hE : 1 ≤ P.eps⁻¹ ^ 2 :=
    one_le_pow₀ (le_of_lt ((one_lt_inv₀ heps).2 P.heps.2))
  have hlogarg :
      Real.logb 2 (8 * (P.m : Real) / P.delta) =
        3 + Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹ := by
    rw [div_eq_mul_inv, Real.logb_mul (mul_ne_zero (by norm_num) hm0)
      (inv_ne_zero hdelta0), Real.logb_mul (by norm_num) hm0, hlogEight]
  have hlogargUpper :
      Real.logb 2 (8 * (P.m : Real) / P.delta) ≤
        4 * (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) := by
    rw [hlogarg]
    nlinarith
  have hlogargNonneg : 0 ≤ Real.logb 2 (8 * (P.m : Real) / P.delta) := by
    rw [hlogarg]
    linarith
  have hepsScale : 12 / P.eps ^ 2 = 12 * (P.eps⁻¹ ^ 2) := by
    field_simp
  have hthresholdReal :
      ((threshold P : Nat) : Real) ≤
        49 * (P.eps⁻¹ ^ 2) *
          (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) := by
    unfold threshold
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg (by positivity : 0 ≤ 12 / P.eps ^ 2) hlogargNonneg)
    have hmain :
        (12 / P.eps ^ 2) * Real.logb 2 (8 * (P.m : Real) / P.delta) ≤
          48 * (P.eps⁻¹ ^ 2) *
            (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) := by
      calc
        (12 / P.eps ^ 2) * Real.logb 2 (8 * (P.m : Real) / P.delta) =
            12 * (P.eps⁻¹ ^ 2) * Real.logb 2 (8 * (P.m : Real) / P.delta) := by
          rw [hepsScale]
        _ ≤ 12 * (P.eps⁻¹ ^ 2) *
            (4 * (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹)) :=
          mul_le_mul_of_nonneg_left hlogargUpper (by positivity)
        _ = 48 * (P.eps⁻¹ ^ 2) *
            (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) := by ring
    have hone : 1 ≤ (P.eps⁻¹ ^ 2) *
        (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) := by
      calc
        (1 : Real) = 1 * 1 := by norm_num
        _ ≤ (P.eps⁻¹ ^ 2) *
            (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹) :=
          mul_le_mul hE hsum (by norm_num) (zero_le_one.trans hE)
    linarith
  have hitemReal : ((itemBits P : Nat) : Real) ≤
      2 * Real.logb 2 (P.n : Real) := by
    unfold itemBits
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (P.n : Real) by linarith)
    linarith
  unfold paperSpaceScale
  rw [Nat.cast_mul]
  calc
    (threshold P : Real) * (itemBits P : Real) ≤
        (49 * (P.eps⁻¹ ^ 2) *
          (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹)) *
        (2 * Real.logb 2 (P.n : Real)) :=
      mul_le_mul hthresholdReal hitemReal (by positivity) (by positivity)
    _ = 98 * (P.eps⁻¹ ^ 2 * Real.logb 2 (P.n : Real) *
        (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹)) := by ring

end Esa22Copy
