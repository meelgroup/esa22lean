import Esa22Copy.Analysis.BindFoldlMFailureProbability

/-!
# Failure union bound over the stream fold

The probability of reaching the absorbing failed state after `m` transitions is
at most `m` times the conditional probability of a new failure.
-/

namespace Esa22Copy

open scoped ENNReal

/--
PAPER: esa22-final.tex:523-538, the union-bound step in Claim `lm:fail`.
-/
theorem runState_failure_probability_le (P : Params) (A : Stream P) :
    (runState P A).toOuterMeasure {s | FailedState s} ≤
      (P.m : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
  have hinit : ∀ s ∈ (PMF.pure (initialState P)).support,
      StateSpaceInvariant P s := by
    intro s hs
    rw [PMF.mem_support_pure_iff] at hs
    subst s
    exact ⟨Nat.zero_le _, fun _ => threshold_pos P⟩
  have h := bind_foldlM_failure_probability_le P (List.ofFn A)
    (PMF.pure (initialState P)) hinit
  have hnot : ¬ FailedState (initialState P) := by
    simp [FailedState, finish, initialState]
  have hpure : (PMF.pure (initialState P)).toOuterMeasure
      {s | FailedState s} = 0 := by
    rw [PMF.toOuterMeasure_pure_apply]
    exact if_neg hnot
  rw [hpure] at h
  simpa [runState] using h

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · integrated the one-step estimate over the invariant-preserving stream fold
* r1 · reduced · isolated the `foldlM` union bound over the conditional step estimate
-/
