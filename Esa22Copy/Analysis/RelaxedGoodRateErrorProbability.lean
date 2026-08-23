import Esa22Copy.Analysis.CriticalLevelMeanGe
import Esa22Copy.Analysis.LevelSampleErrorProbabilityLe
import Esa22Copy.Analysis.RelaxedGoodRateUnionBound
import Esa22Copy.Analysis.RelaxedLevelSliceLeFixedSampleError
import Esa22Copy.Analysis.ThresholdChernoffBudget

/-!
# Fixed-level error probability for the relaxed estimator

On levels at most the critical level, the adaptive final error event is covered
by a union of unconditional fixed-level deviation events.  Applying independent
Bernoulli concentration at each fixed level and summing the finitely many
positive reachable levels gives `delta / 4`.
-/

namespace Esa22Copy

/--
INTERNAL: the all-fixed-level relative-error bound below the critical sampling
level; the event is deliberately not conditioned on the adaptive final level.
-/
theorem relaxed_good_rate_error_probability_le (P : Params) (A : Stream P)
    (hlarge : threshold P ≤ F0 A) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
      P.delta / 4 := by
  calc
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
        (P.m : Real) * (P.delta / (4 * (P.m : Real))) := by
      apply relaxed_good_rate_union_bound P A
      intro k hkpos hkstream hkcritical
      calc
        Arlib.Approximation.outProbR (relaxedRunCost P A)
            ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤
            ((freshLevelCoins P).toOuterMeasure
              (fixedLevelErrorEvent P A k)).toReal :=
          relaxed_level_slice_le_fixed_sample_error P A k hkstream
        _ ≤ 2 * Real.exp
            (-(P.eps ^ 2 *
              ((F0 A : Real) * (1 / 2 : Real) ^ k)) / 3) :=
          levelSample_error_probability_le P A k hkpos hkstream
        _ ≤ 2 * Real.exp
            (-(P.eps ^ 2 * (threshold P : Real)) / 12) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          have hmean := criticalLevel_mean_ge P A hlarge k hkcritical
          nlinarith [sq_nonneg P.eps]
        _ ≤ P.delta / (4 * (P.m : Real)) :=
          threshold_chernoff_budget P
    _ = P.delta / 4 := by
      have hm : (P.m : Real) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.hm)
      field_simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · reduced · proved the support, coupling, cutoff, and threshold steps; left
  multiplicative concentration and the finite positive-level union isolated
* r2 · reduced · isolated coupling, multiplicative concentration, cutoff arithmetic,
  threshold budgeting, and the finite positive-level union
* r1 · open · isolated the unconditional all-fixed-level tail required by `relaxed_error_probability_le`
-/
