import Arlib.Approximation.Counting

/-!
# Comparing events through a supported coupling

This module packages the generic outer-measure argument used by the
original-to-relaxed simulation.
-/

namespace Esa22Copy

/--
INTERNAL: a coupling whose supported left-event outcomes imply the right event
transfers the corresponding real output-probability inequality.
-/
theorem outProbR_le_of_supported_coupling {α β : Type*}
    (μ : PMF (α × Nat)) (ν : PMF (β × Nat)) (E : Set α) (F : Set β)
    (κ : PMF ((α × Nat) × (β × Nat)))
    (hfst : κ.map Prod.fst = μ) (hsnd : κ.map Prod.snd = ν)
    (hsupport : ∀ z ∈ κ.support, z.1.1 ∈ E → z.2.1 ∈ F) :
    Arlib.Approximation.outProbR μ E ≤
      Arlib.Approximation.outProbR ν F := by
  rw [Arlib.Approximation.outProbR_def, Arlib.Approximation.outProbR_def]
  apply ENNReal.toReal_mono (Arlib.Approximation.outProb_ne_top ν F)
  calc
    Arlib.Approximation.outProb μ E =
        (κ.map Prod.fst).toOuterMeasure {p | p.1 ∈ E} := by
      simp only [Arlib.Approximation.outProb, hfst]
    _ = κ.toOuterMeasure (Prod.fst ⁻¹' {p | p.1 ∈ E}) :=
      PMF.toOuterMeasure_map_apply Prod.fst κ _
    _ ≤ κ.toOuterMeasure (Prod.snd ⁻¹' {p | p.1 ∈ F}) := by
      apply κ.toOuterMeasure_mono
      intro z hz
      exact hsupport z hz.2 hz.1
    _ = (κ.map Prod.snd).toOuterMeasure {p | p.1 ∈ F} :=
      (PMF.toOuterMeasure_map_apply Prod.snd κ _).symm
    _ = Arlib.Approximation.outProb ν F := by
      simp only [Arlib.Approximation.outProb, hsnd]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · added · proved event domination from a supported PMF coupling
-/
