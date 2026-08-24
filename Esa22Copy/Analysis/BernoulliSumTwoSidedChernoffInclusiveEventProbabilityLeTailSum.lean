import Arlib.Probability.Chernoff

/-!
# Split an inclusive two-sided deviation event

This is the event-theoretic step converting an inclusive absolute deviation into the
union of the inclusive upper and lower events accepted by Arlib's one-sided bounds.
-/

namespace Esa22Copy

/--
INTERNAL: Event-union step used by `bernoulliSum_twoSidedChernoff`.
-/
theorem bernoulliSum_twoSidedChernoff_inclusive_event_probability_le_tail_sum
    (P : Arlib.Probability.FinProb) (V : P.Ω → Real) (μ β : Real) :
    P.Pr (Finset.univ.filter fun ω => β * μ ≤ |V ω - μ|) ≤
      P.Pr (Finset.univ.filter fun ω => (1 + β) * μ ≤ V ω) +
      P.Pr (Finset.univ.filter fun ω => V ω ≤ (1 - β) * μ) := by
  have hsub :
      (Finset.univ.filter fun ω => β * μ ≤ |V ω - μ|) ⊆
        (Finset.univ.filter fun ω => (1 + β) * μ ≤ V ω) ∪
          (Finset.univ.filter fun ω => V ω ≤ (1 - β) * μ) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases le_abs.1 hω.2 with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩)
  calc
    P.Pr (Finset.univ.filter fun ω => β * μ ≤ |V ω - μ|) ≤
        P.Pr ((Finset.univ.filter fun ω => (1 + β) * μ ≤ V ω) ∪
          (Finset.univ.filter fun ω => V ω ≤ (1 - β) * μ)) :=
      Arlib.Probability.FinProb.Pr_mono P hsub
    _ ≤ P.Pr (Finset.univ.filter fun ω => (1 + β) * μ ≤ V ω) +
        P.Pr (Finset.univ.filter fun ω => V ω ≤ (1 - β) * μ) :=
      Arlib.Probability.FinProb.Pr_union_le P _ _

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · split the inclusive deviation event with `le_abs` and applied the finite union bound
-/
