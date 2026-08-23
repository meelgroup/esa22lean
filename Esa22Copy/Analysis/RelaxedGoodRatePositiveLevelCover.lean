import Esa22Copy.Analysis.ProbabilityModel
import Esa22Copy.Analysis.CriticalLevel
import Esa22Copy.Analysis.RelaxedZeroLevelErrorProbability
import Esa22Copy.Analysis.RelaxedRunPrefixLevelLe
import Arlib.Approximation.UnionBound
import Arlib.Approximation.Hoeffding

/-!
# Support-aware cover by positive relaxed levels

Only reachable states matter to output probability.  Such final states have
level at most `m`; after removing the probability-zero level-zero error slice,
the good-rate error event is covered by levels `1, ..., m`.
-/

namespace Esa22Copy

/--
INTERNAL: the reachable good-rate error event is probability-dominated by its
finite union of positive level slices.
-/
theorem relaxed_good_rate_positive_level_cover (P : Params) (A : Stream P) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
      Arlib.Approximation.outProbR (relaxedRunCost P A)
        (⋃ j : Fin P.m,
          ({s | s.level = j.val + 1} ∩
            {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A)) := by
  let T : Set (RelaxedState P) :=
    {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A
  let Z : Set (RelaxedState P) :=
    {s | s.level = 0} ∩ relaxedErrorEvent P A
  let U : Set (RelaxedState P) := ⋃ j : Fin P.m,
    ({s | s.level = j.val + 1} ∩
      {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A)
  have hprefix : relaxedRunPrefix P A (Fin.last P.m) = relaxedRun P A := by
    unfold relaxedRunPrefix relaxedRun
    change ((List.ofFn A).take P.m).foldlM _ _ = (List.ofFn A).foldlM _ _
    rw [List.take_of_length_le (by simp)]
  have hlevel : ∀ (p : RelaxedState P × Nat),
      p ∈ (relaxedRunCost P A).support → p.1.level ≤ P.m := by
    intro p hp
    rw [relaxedRunCost, PMF.mem_support_map_iff] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    apply relaxedRunPrefix_level_le P A (Fin.last P.m) s
    rw [hprefix]
    exact hs
  have hsupport :
      {p : RelaxedState P × Nat | p.1 ∈ T} ∩ (relaxedRunCost P A).support ⊆
        {p : RelaxedState P × Nat | p.1 ∈ Z ∪ U} := by
    intro p hp
    rcases hp with ⟨hpT, hpsupport⟩
    change p.1 ∈ T at hpT
    change p.1 ∈ Z ∪ U
    rcases hpT with ⟨hcritical, herror⟩
    by_cases hzero : p.1.level = 0
    · exact Or.inl ⟨hzero, herror⟩
    · apply Or.inr
      have hpos : 0 < p.1.level := Nat.pos_of_ne_zero hzero
      have hle : p.1.level ≤ P.m := hlevel p hpsupport
      let j : Fin P.m := ⟨p.1.level - 1, by omega⟩
      change p.1 ∈ ⋃ j : Fin P.m,
        ({s | s.level = j.val + 1} ∩
          {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A)
      simp only [Set.mem_iUnion]
      exact ⟨j, ⟨⟨by simp [j, Nat.sub_add_cancel hpos], hcritical⟩, herror⟩⟩
  have hcover :
      Arlib.Approximation.outProbR (relaxedRunCost P A) T ≤
        Arlib.Approximation.outProbR (relaxedRunCost P A) (Z ∪ U) := by
    rw [Arlib.Approximation.outProbR_def, Arlib.Approximation.outProbR_def]
    apply ENNReal.toReal_mono (Arlib.Approximation.outProb_ne_top _ _)
    exact (relaxedRunCost P A).toOuterMeasure_mono hsupport
  calc
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) =
        Arlib.Approximation.outProbR (relaxedRunCost P A) T := rfl
    _ ≤ Arlib.Approximation.outProbR (relaxedRunCost P A) (Z ∪ U) := hcover
    _ ≤ Arlib.Approximation.outProbR (relaxedRunCost P A) Z +
        Arlib.Approximation.outProbR (relaxedRunCost P A) U :=
      Arlib.Approximation.outProbR_union_le _ _ _
    _ = Arlib.Approximation.outProbR (relaxedRunCost P A) U := by
      rw [show Arlib.Approximation.outProbR (relaxedRunCost P A) Z = 0 by
        simpa only [Z] using relaxed_zero_level_error_probability P A]
      simp
    _ = Arlib.Approximation.outProbR (relaxedRunCost P A)
        (⋃ j : Fin P.m,
          ({s | s.level = j.val + 1} ∩
            {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A)) := rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · support-aware cover from final level reachability and the zero-level probability lemma
-/
