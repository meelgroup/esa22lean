import Esa22Copy.Analysis.ProbabilityModel
import Esa22Copy.Analysis.RelaxedBadRateProbability
import Esa22Copy.Analysis.RelaxedGoodRateErrorProbability
import Arlib.Approximation.Hoeffding

/-!
# Concentration of the relaxed estimator

The proof obligation combines the first-crossing tail above the critical level with
fixed-level relative-error tails below it, exactly as in Claims 4 and 5 of the paper.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:697-777, Claim `lm:error-fail` and its two tail bounds.
-/
theorem relaxed_error_probability_le (P : Params) (A : Stream P)
    (hlarge : threshold P ≤ F0 A) :
    Arlib.Approximation.outProbR (relaxedRunCost P A) (relaxedErrorEvent P A) ≤
      P.delta / 2 := by
  have hcover : relaxedErrorEvent P A ⊆
      {s | criticalLevel P A < s.level} ∪
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) := by
    intro s hs
    by_cases hlevel : s.level ≤ criticalLevel P A
    · exact Or.inr ⟨hlevel, hs⟩
    · exact Or.inl (Nat.lt_of_not_ge hlevel)
  calc
    Arlib.Approximation.outProbR (relaxedRunCost P A) (relaxedErrorEvent P A) ≤
        Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | criticalLevel P A < s.level} ∪
            ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A)) :=
      Arlib.Approximation.outProbR_mono _ hcover
    _ ≤ Arlib.Approximation.outProbR (relaxedRunCost P A)
          {s | criticalLevel P A < s.level} +
        Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) :=
      Arlib.Approximation.outProbR_union_le _ _ _
    _ ≤ P.delta / 4 + P.delta / 4 :=
      add_le_add
        (relaxed_bad_rate_probability_le P A hlarge)
        (relaxed_good_rate_error_probability_le P A hlarge)
    _ = P.delta / 2 := by ring

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · repaired · supplied `hlarge` to the repaired bad-rate and good-rate bounds
* r1 · reduced · closed the headline by the high-level and low-level-error union bound
-/
