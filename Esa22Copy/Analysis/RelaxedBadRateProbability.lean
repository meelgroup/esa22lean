import Esa22Copy.Analysis.CriticalLevel
import Esa22Copy.Analysis.BadLevelTailBudget
import Esa22Copy.Analysis.CriticalLevelMeanBound
import Esa22Copy.Analysis.LevelSampleCardGeThresholdLe
import Esa22Copy.Analysis.RelaxedRunBadLevelPrefixRecurrence

/-!
# Excessive-level probability for the relaxed estimator

This is the first-crossing half of the relaxed-error argument.  A final level
above the critical level must be witnessed by a threshold-sized fixed-level
sample at an earlier prefix; a union bound over prefixes and an upper-tail bound
then give `delta / 4`.
-/

namespace Esa22Copy

/--
INTERNAL: the first-crossing and fixed-level upper-tail bound for levels above
the critical sampling level.
-/
theorem relaxed_bad_rate_probability_le (P : Params) (A : Stream P)
    (hlarge : threshold P ≤ F0 A) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        {s | criticalLevel P A < s.level} ≤ P.delta / 4 := by
  let b : Real := 2 * Real.exp (-(threshold P : Real) / 6)
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hprefixCard (i : Fin (P.m + 1)) :
      (prefixDistinct A i).card ≤ F0 A := by
    apply Finset.card_le_card
    intro a ha
    simp only [prefixDistinct, Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    simp only [distinctSet, Finset.mem_image]
    exact ⟨j, Finset.mem_univ j, rfl⟩
  have htail (hk : criticalLevel P A ≤ P.m) (i : Fin (P.m + 1)) :
      ((freshLevelCoins P).toOuterMeasure
        {coins | threshold P ≤
          (levelSample coins A (criticalLevel P A) i).card}).toReal ≤ b := by
    exact levelSample_card_ge_threshold_le P A i (criticalLevel P A)
      (F0 A) (threshold P) hk (hprefixCard i)
      (criticalLevel_mean_bound P A hlarge)
  have hfirst := relaxedRun_bad_level_prefix_recurrence P A
    (criticalLevel P A) b hb htail
  calc
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        {s | criticalLevel P A < s.level} ≤ (P.m : Real) * b := hfirst
    _ ≤ (P.m : Real) * (P.delta / (4 * (P.m : Real))) := by
      gcongr
      exact bad_level_tail_budget P
    _ = P.delta / 4 := by
      have hm : (P.m : Real) ≠ 0 := by exact_mod_cast (ne_of_gt P.hm)
      field_simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the headline from four isolated first-crossing, tail, and arithmetic obligations
* r1 · open · isolated the first-crossing tail required by `relaxed_error_probability_le`
-/
