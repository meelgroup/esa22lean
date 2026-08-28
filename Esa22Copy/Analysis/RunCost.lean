import Esa22Copy.Interface.Pseudocode

/-!
# Exact cost payload of a completed run

The natural-number component returned by `run` is definitionally the peak sample
cardinality multiplied by the per-item bit charge.
-/

namespace Esa22Copy

/--
INTERNAL: the payload's second component is `Arlib.Approximation.outProbR`'s cost
slot, and this development puts nothing in it.

It used to hold `peakSamples * itemBits P` — the space claim, as a number the
model maintained by hand.  Space is now `Arlib.Computation.worstSpace` applied to
`estimator`, so there is nothing for a payload to carry and carrying something
would be the defect `IsFPRAS.pinnedTime_of_cost_zero` records.
-/
theorem run_cost_eq (P : Params) (A : Stream P) (outcome : Answer × Nat)
    (houtcome : outcome ∈ (run P A).support) :
    outcome.2 = 0 := by
  rw [run, PMF.mem_support_bind_iff] at houtcome
  obtain ⟨s, _, hs⟩ := houtcome
  change outcome ∈ (PMF.pure (finish s, 0)).support at hs
  rw [PMF.mem_support_pure_iff] at hs
  subst outcome
  rfl

end Esa22Copy
