import Esa22Copy.Model.Pseudocode

/-!
# Exact cost payload of a completed run

The natural-number component returned by `run` is definitionally the peak sample
cardinality multiplied by the per-item bit charge.
-/

namespace Esa22Copy

/--
INTERNAL: exposes the exact cost payload inserted by the final `pure` in `run`.
-/
theorem run_cost_eq (P : Params) (A : Stream P) (outcome : RunOutput P × Nat)
    (houtcome : outcome ∈ (run P A).support) :
    outcome.2 = outcome.1.peakSamples * itemBits P := by
  rw [run, PMF.mem_support_bind_iff] at houtcome
  obtain ⟨s, _, hs⟩ := houtcome
  change outcome ∈
    (PMF.pure (finish s, (finish s).peakSamples * itemBits P)).support at hs
  rw [PMF.mem_support_pure_iff] at hs
  subst outcome
  rfl

end Esa22Copy
