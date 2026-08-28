import Esa22Copy.Analysis.SpaceBound
import Esa22Copy.Analysis.AccuracyAssembly
import Esa22Copy.Analysis.PaperSpace
import Esa22Copy.Analysis.RunCost
import Esa22Copy.Analysis.RunPeak
import Esa22Copy.Interface.ProgramModel

/-!
# Proof assembly for the ESA 2022 headline theorem

This module combines the probability analysis, the support-wise deterministic space
invariant, and the displayed asymptotic item-space calculation.  The audit surface in
`Model.Theorem` contains only the paper-facing statement and delegates here.

The statement is about `estimatorOutput` — the program of `Model/Program.lean`
with its meters dropped — and `estimatorOutput_eq` is what turns it into the
`Finset` model the analysis below is carried out in.  That rewrite is the only
place the two representations meet.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:500-508, correctness and worst-case item-space of the estimator.
-/
theorem esa22Copy_proof (_hprior : Prior) (P : Params) (A : Stream P) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (estimatorOutput P A) (accurateEvent P A) ∧
    Arlib.Computation.worstSpace Arlib.Computation.Cell.cell 0 (estimator P A)
      ≤ ((threshold P : Nat) : ℕ∞) ∧
    PaperItemSpaceBigO := by
  refine ⟨?_, estimator_worstSpace_le P A, paperItemSpaceBigO_proof⟩
  rw [estimatorOutput_eq]
  by_cases hsmall : F0 A < threshold P
  · exact small_stream_accuracy P A hsmall
  · exact run_accuracy_of_error_bounds P A
      (fail_probability_le P A)
      (nonfail_error_le_relaxed_error P A)
      (relaxed_error_probability_le P A (Nat.le_of_not_gt hsmall))

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · repaired · split on stream size and supplied `threshold P ≤ F0 A` to the
  repaired relaxed-error bound.
* current · factored · deterministic cost/peak and event assembly closed; concentration
  and analytic leaves isolated by module.
-/
