import Esa22Copy.Analysis.CriticalLevel
import Esa22Copy.Analysis.RunPeak

/-!
# Expected sample size below the critical level

The floor/logarithm definition of the critical level ensures that every lower
dyadic level has expected sample size at least one quarter of the threshold.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:752-763, the lower bound on the fixed-level expected
sample size for levels below the critical cutoff.
-/
theorem criticalLevel_mean_ge (P : Params) (A : Stream P)
    (hlarge : threshold P ≤ F0 A) (k : Nat)
    (hk : k ≤ criticalLevel P A) :
    (threshold P : Real) / 4 ≤
      (F0 A : Real) * (1 / 2 : Real) ^ k := by
  have hthreshold : 0 < (threshold P : Real) := by
    exact_mod_cast threshold_pos P
  have hF0 : 0 < (F0 A : Real) := by
    have hnat : 0 < F0 A := (threshold_pos P).trans_le hlarge
    exact_mod_cast hnat
  let x : Real := 4 * (F0 A : Real) / (threshold P : Real)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hxone : 1 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hthreshold]
    have hcast : (threshold P : Real) ≤ (F0 A : Real) := by
      exact_mod_cast hlarge
    linarith
  have hcritical : (criticalLevel P A : Real) ≤ Real.logb 2 x := by
    unfold criticalLevel
    change (Nat.floor (Real.logb 2 x) : Real) ≤ Real.logb 2 x
    exact Nat.floor_le (Real.logb_nonneg (by norm_num) hxone)
  have hkcast : (k : Real) ≤ (criticalLevel P A : Real) := by
    exact_mod_cast hk
  have hpow : (2 : Real) ^ k ≤ x := by
    rw [← Real.rpow_natCast]
    exact (Real.le_logb_iff_rpow_le (by norm_num) hx).mp
      (hkcast.trans hcritical)
  have hpowpos : 0 < (2 : Real) ^ k := by positivity
  rw [div_pow]
  norm_num only [one_pow]
  rw [mul_one_div]
  rw [le_div_iff₀ hpowpos]
  calc
    (threshold P : Real) / 4 * 2 ^ k ≤
        (threshold P : Real) / 4 * x :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (F0 A : Real) := by
      dsimp [x]
      field_simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · converted the floor/log-base-two cutoff to the expected-sample lower bound
-/
