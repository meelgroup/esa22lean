import Esa22Copy.Analysis.ProbabilityModel
import Esa22Copy.Analysis.RelaxedCoupling
import Esa22Copy.Analysis.RelaxedRunPrefixBadLevelBound
import Esa22Copy.Analysis.RelaxedRunPrefixLevelLe

/-!
# First-crossing union bound for relaxed levels

An adaptive level can first exceed `k` only at one of the stream prefixes, and
that crossing requires the corresponding fixed-level prefix sample to reach the
threshold.  This packages iteration of that recurrence over all `m` prefixes.
-/

namespace Esa22Copy

/--
INTERNAL: uniformly bounding every fixed-level prefix crossing event bounds the
final excessive-level event by `m` times that bound.
-/
theorem relaxedRun_bad_level_prefix_recurrence (P : Params) (A : Stream P)
    (k : Nat) (b : Real) (hb : 0 ≤ b)
    (htail : k ≤ P.m → ∀ i : Fin (P.m + 1),
      ((freshLevelCoins P).toOuterMeasure
        {coins | threshold P ≤ (levelSample coins A k i).card}).toReal ≤ b) :
    Arlib.Approximation.outProbR (relaxedRunCost P A) {s | k < s.level} ≤
      (P.m : Real) * b := by
  have hprefix : relaxedRunPrefix P A (Fin.last P.m) = relaxedRun P A := by
    unfold relaxedRunPrefix relaxedRun
    change ((List.ofFn A).take P.m).foldlM _ _ =
      (List.ofFn A).foldlM _ _
    rw [List.take_of_length_le (by simp)]
  have hterminal :
      Arlib.Approximation.outProbR (relaxedRunCost P A) {s | k < s.level} =
        ((relaxedRunPrefix P A (Fin.last P.m)).toOuterMeasure
          {s | k < s.level}).toReal := by
    rw [Arlib.Approximation.outProbR_def]
    unfold Arlib.Approximation.outProb relaxedRunCost
    rw [PMF.toOuterMeasure_map_apply]
    rw [← hprefix]
    rfl
  rw [hterminal]
  by_cases hk : k ≤ P.m
  · exact relaxedRunPrefix_bad_level_bound P A k b hk (htail hk) P.m
      (Nat.le_refl P.m)
  · have hzero :
        (relaxedRunPrefix P A (Fin.last P.m)).toOuterMeasure
            {s | k < s.level} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff]
      apply Set.disjoint_left.2
      intro s hs hbad
      change k < s.level at hbad
      have hlevel := relaxedRunPrefix_level_le P A (Fin.last P.m) s hs
      have hmk : P.m < k := Nat.lt_of_not_ge hk
      simp only [Fin.val_last] at hlevel
      omega
    rw [hzero]
    exact mul_nonneg (Nat.cast_nonneg P.m) hb

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · reduced · closed the headline from the one-step recurrence, its proved
  induction wrapper, the terminal-law rewrite, and the reachable-level invariant
* r2 · reduced · packaged the iterated first-crossing recurrence and union bound
-/
