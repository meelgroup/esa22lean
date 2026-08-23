import Esa22Copy.Analysis.BindStepFailureProbability

/-!
# Failure accumulation over a monadic list fold

The failure mass after processing a list is bounded by the starting failure mass
plus one per-step budget for every list element.
-/

namespace Esa22Copy

open scoped ENNReal

/--
INTERNAL: generalized fold induction carrying an invariant-supported starting PMF.
-/
theorem bind_foldlM_failure_probability_le (P : Params)
    (xs : List (Item P)) (μ : PMF (State P))
    (hμ : ∀ s ∈ μ.support, StateSpaceInvariant P s) :
    (μ.bind (fun s => xs.foldlM (fun s a => step P a s) s)).toOuterMeasure
        {t | FailedState t} ≤
      μ.toOuterMeasure {s | FailedState s} +
        (xs.length : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
  induction xs generalizing μ with
  | nil =>
      change (μ.bind fun s => PMF.pure s).toOuterMeasure {t | FailedState t} ≤ _
      rw [PMF.bind_pure]
      simp
  | cons a xs ih =>
      have hbind : ∀ t ∈ (μ.bind (step P a)).support,
          StateSpaceInvariant P t := by
        intro t ht
        rw [PMF.mem_support_bind_iff] at ht
        obtain ⟨s, hs, ht⟩ := ht
        exact step_preserves_space P a (hμ s hs) ht
      have hdist :
          μ.bind (fun s => (a :: xs).foldlM (fun s a => step P a s) s) =
            (μ.bind (step P a)).bind
              (fun s => xs.foldlM (fun s a => step P a s) s) := by
        rw [PMF.bind_bind]
        congr 1
      rw [hdist]
      calc
        ((μ.bind (step P a)).bind
            (fun s => xs.foldlM (fun s a => step P a s) s)).toOuterMeasure
              {t | FailedState t} ≤
            (μ.bind (step P a)).toOuterMeasure {s | FailedState s} +
              (xs.length : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) :=
          ih (μ.bind (step P a)) hbind
        _ ≤ μ.toOuterMeasure {s | FailedState s} +
              ((2 : ℝ≥0∞)⁻¹) ^ threshold P +
              (xs.length : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ threshold P) :=
          add_le_add_left (bind_step_failure_probability_le P a μ hμ) _
        _ = μ.toOuterMeasure {s | FailedState s} +
              ((a :: xs).length : ℝ≥0∞) *
                (((2 : ℝ≥0∞)⁻¹) ^ threshold P) := by
          simp [add_mul, add_assoc, add_comm, add_left_comm]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · generalized over the starting PMF and propagated support invariants
-/
