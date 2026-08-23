import Esa22Copy.Analysis.FailProbability
import Esa22Copy.Analysis.NonfailCoupling
import Esa22Copy.Analysis.RelaxedError
import Esa22Copy.Analysis.SmallStream
import Arlib.Approximation.Hoeffding

/-!
# Assembly of the estimator's accuracy bound

The small-stream branch is exact.  In the other branch, error is split into explicit
failure and error without failure, then the latter is transported to the relaxed run.
-/

namespace Esa22Copy

/--
INTERNAL: event algebra assembling the three quantitative probability bounds.
-/
theorem run_accuracy_of_error_bounds (P : Params) (A : Stream P)
    (hfail : Arlib.Approximation.outProbR (run P A) (failEvent P) ≤ P.delta / 8)
    (hnonfail : Arlib.Approximation.outProbR (run P A)
        (errorEvent P A \ failEvent P) ≤
      Arlib.Approximation.outProbR (relaxedRunCost P A) (relaxedErrorEvent P A))
    (hrelaxed : Arlib.Approximation.outProbR (relaxedRunCost P A)
        (relaxedErrorEvent P A) ≤ P.delta / 2) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (run P A) (accurateEvent P A) := by
  have hsubset : errorEvent P A ⊆
      failEvent P ∪ (errorEvent P A \ failEvent P) := by
    intro output herror
    by_cases hfail' : output ∈ failEvent P
    · exact Or.inl hfail'
    · exact Or.inr ⟨herror, hfail'⟩
  have herror : Arlib.Approximation.outProbR (run P A) (errorEvent P A) ≤ P.delta := by
    calc
      Arlib.Approximation.outProbR (run P A) (errorEvent P A) ≤
          Arlib.Approximation.outProbR (run P A)
            (failEvent P ∪ (errorEvent P A \ failEvent P)) :=
        Arlib.Approximation.outProbR_mono _ hsubset
      _ ≤ Arlib.Approximation.outProbR (run P A) (failEvent P) +
          Arlib.Approximation.outProbR (run P A) (errorEvent P A \ failEvent P) :=
        Arlib.Approximation.outProbR_union_le _ _ _
      _ ≤ P.delta / 8 + P.delta / 2 := add_le_add hfail (hnonfail.trans hrelaxed)
      _ ≤ P.delta := by nlinarith [P.hdelta.1]
  rw [errorEvent, Arlib.Approximation.outProbR_compl] at herror
  linarith

/--
PAPER: esa22-final.tex:500-519, correctness part of the main theorem.
-/
theorem run_accuracy (P : Params) (A : Stream P) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (run P A) (accurateEvent P A) := by
  by_cases hlarge : threshold P ≤ F0 A
  · exact run_accuracy_of_error_bounds P A
      (fail_probability_le P A)
      (nonfail_error_le_relaxed_error P A)
      (relaxed_error_probability_le P A hlarge)
  · exact small_stream_accuracy P A (Nat.lt_of_not_ge hlarge)

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · repaired · split on `threshold P ≤ F0 A`; the large branch supplies the
  hypothesis added to `relaxed_error_probability_le`, and the complementary branch uses
  deterministic small-stream exactness
-/
