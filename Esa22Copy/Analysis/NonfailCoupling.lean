import Esa22Copy.Analysis.RunStateRelaxedRunNonfailCoupling
import Esa22Copy.Analysis.FinishNonfailErrorIffRelaxedError
import Esa22Copy.Analysis.OutProbRLeOfSupportedCoupling

/-!
# Original-to-relaxed nonfailure coupling

Until an all-survive thinning produces bottom, the original and relaxed algorithms
have identical executions.  This file states only the event-mass inequality needed
by the headline theorem.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:541-552, original nonfailure error is dominated by relaxed error.
-/
theorem nonfail_error_le_relaxed_error (P : Params) (A : Stream P) :
    Arlib.Approximation.outProbR (run P A)
        (errorEvent P A \ failEvent P) ≤
      Arlib.Approximation.outProbR (relaxedRunCost P A) (relaxedErrorEvent P A) := by
  obtain ⟨κ, hfst, hsnd, hrel⟩ := runState_relaxedRun_nonfail_coupling P A
  let lift : State P × RelaxedState P →
      (RunOutput P × Nat) × (RelaxedState P × Nat) := fun z =>
    ((finish z.1, (finish z.1).peakSamples * itemBits P), (z.2, 0))
  let κ' := κ.map lift
  apply outProbR_le_of_supported_coupling
    (run P A) (relaxedRunCost P A)
    (errorEvent P A \ failEvent P) (relaxedErrorEvent P A) κ'
  · calc
      κ'.map Prod.fst =
          (κ.map Prod.fst).map (fun s =>
            (finish s, (finish s).peakSamples * itemBits P)) := by
        simp only [κ', lift, PMF.map_comp, Function.comp_def]
      _ = (runState P A).map (fun s =>
            (finish s, (finish s).peakSamples * itemBits P)) := by rw [hfst]
      _ = run P A := by rfl
  · calc
      κ'.map Prod.snd = (κ.map Prod.snd).map (fun r => (r, 0)) := by
        simp only [κ', lift, PMF.map_comp, Function.comp_def]
      _ = (relaxedRun P A).map (fun r => (r, 0)) := by rw [hsnd]
      _ = relaxedRunCost P A := rfl
  · intro z hz hzerror
    obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact (finish_nonfail_error_iff_relaxed_error (hrel q hq) hzerror.2).1
      hzerror.1

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · closed the headline inequality from the isolated step and run couplings
-/
