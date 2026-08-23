import Esa22Copy.Analysis.CriticalLevel
import Esa22Copy.Analysis.RunPeak

/-!
# Mean at the critical sampling level

The floor defining the critical level puts the expected fixed-level sample
strictly below one half of the threshold.  This is the real-arithmetic input to
the upper-tail estimate.
-/

namespace Esa22Copy

/--
INTERNAL: the floor/logarithm definition makes the mean at the critical level
strictly smaller than half the threshold.
-/
theorem criticalLevel_mean_bound (P : Params) (A : Stream P)
    (hlarge : threshold P ≤ F0 A) :
    (F0 A : Real) * (2 : Real)⁻¹ ^ criticalLevel P A <
      (threshold P : Real) / 2 := by
  have hthreshold : 0 < (threshold P : Real) := by
    exact_mod_cast threshold_pos P
  have hlarge' : (threshold P : Real) ≤ (F0 A : Real) := by
    exact_mod_cast hlarge
  have hF0 : 0 < (F0 A : Real) := hthreshold.trans_le hlarge'
  have hx : 0 < 4 * (F0 A : Real) / (threshold P : Real) := by
    positivity
  have hlog :
      Real.logb 2 (4 * (F0 A : Real) / (threshold P : Real)) <
        (criticalLevel P A : Real) + 1 := by
    rw [criticalLevel]
    exact Nat.lt_floor_add_one _
  have hpower :
      4 * (F0 A : Real) / (threshold P : Real) <
        (2 : Real) ^ ((criticalLevel P A : Real) + 1) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hx).mp hlog
  rw [Real.rpow_add_one (by norm_num), Real.rpow_natCast] at hpower
  have hnum :
      (F0 A : Real) * 2 <
        (threshold P : Real) * (2 : Real) ^ criticalLevel P A := by
    have hcross := (div_lt_iff₀ hthreshold).mp hpower
    nlinarith
  rw [inv_pow]
  exact
    (div_lt_div_iff₀ (pow_pos (by norm_num) (criticalLevel P A))
      (by norm_num : (0 : Real) < 2)).2 hnum

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · converted the strict floor bound through `logb` and positive-denominator algebra
* r2 · reduced · isolated the strict mean bound implied by the floor definition
-/
