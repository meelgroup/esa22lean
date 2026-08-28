import Esa22Copy.Analysis.FailedState

/-!
# Relating internal and output failure events

Packaging the final state with its charged cost does not change whether the
finished answer is `none`.
-/

namespace Esa22Copy

/--
INTERNAL: unfolds `run` and identifies its output failure event with internal failure.
-/
theorem run_failEvent_eq_state_failure (P : Params) (A : Stream P) :
    Arlib.Approximation.outProbR (run P A) (failEvent P) =
      ((runState P A).toOuterMeasure {s | FailedState s}).toReal := by
  unfold Arlib.Approximation.outProbR Arlib.Approximation.outProb
  rw [run, PMF.toOuterMeasure_bind_apply]
  congr 1
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro s
  change (runState P A) s *
      (PMF.pure (finish s, 0)).toOuterMeasure
        {p | p.1 ∈ failEvent P} =
    {s | FailedState s}.indicator (runState P A) s
  rw [PMF.toOuterMeasure_pure_apply]
  by_cases h : finish s = none <;>
    simp [failEvent, FailedState, h]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · expanded the final bind and matched the failure indicators pointwise
-/
