import Esa22Copy.Analysis.RelaxedGoodRatePositiveLevelCover
import Esa22Copy.Analysis.RelaxedGoodRateUnionBoundFalse
import Arlib.Approximation.UnionBound

/-!
# Finite union over reachable positive relaxed levels

The originally proposed theorem omitted nonnegativity of its common slice
budget and is false; it remains below with the required machine-checked
`DISPROVED` marker.  The repaired theorem adds `0 ≤ b`.  Its finite-union
bookkeeping is closed, conditional only on the separately isolated
level-zero exactness lemma used by the proved support-aware cover.
-/

namespace Esa22Copy

/--
INTERNAL: the original unrestricted bookkeeping statement, retained verbatim
under the project's false-goal protocol and refuted by
`relaxed_good_rate_union_bound_false`.
-/
theorem relaxed_good_rate_union_bound (P : Params) (A : Stream P) (b : Real)
    (hb : 0 ≤ b)
    (hslice : ∀ k : Nat, 0 < k → k ≤ P.m → k ≤ criticalLevel P A →
      Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤ b) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
      (P.m : Real) * b := by
  -- Added `hb : 0 ≤ b`; `relaxed_good_rate_union_bound_false` refutes the
  -- version without this hypothesis.
  sorry

/--
INTERNAL: the corrected finite positive-level union bound, with the necessary
nonnegativity hypothesis on the common slice budget.
-/
theorem relaxed_good_rate_union_bound_nonneg (P : Params) (A : Stream P) (b : Real)
    (hb : 0 ≤ b)
    (hslice : ∀ k : Nat, 0 < k → k ≤ P.m → k ≤ criticalLevel P A →
      Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤ b) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
      (P.m : Real) * b := by
  let F : Fin P.m → Set (RelaxedState P) := fun j =>
    {s | s.level = j.val + 1} ∩
      {s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A
  calc
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
        Arlib.Approximation.outProbR (relaxedRunCost P A) (⋃ j : Fin P.m, F j) := by
      simpa only [F] using relaxed_good_rate_positive_level_cover P A
    _ ≤ ∑ _j : Fin P.m, b := by
      have hunion := Arlib.Approximation.outProbR_biUnion_le_sum
        (relaxedRunCost P A) Finset.univ F (fun _ => b) (by
          intro j _hj
          by_cases hcritical : j.val + 1 ≤ criticalLevel P A
          · refine (Arlib.Approximation.outProbR_mono _ ?_).trans
              (hslice (j.val + 1) (by omega) (by omega) hcritical)
            intro s hs
            exact ⟨hs.1.1, hs.2⟩
          · have hempty : F j = ∅ := by
              ext s
              simp only [F, Set.mem_inter_iff, Set.mem_setOf_eq,
                Set.mem_empty_iff_false, iff_false]
              intro hs
              exact hcritical (hs.1.1 ▸ hs.1.2)
            rw [hempty]
            simpa [Arlib.Approximation.outProbR_def,
              Arlib.Approximation.outProb] using hb)
      simpa using hunion
    _ = (P.m : Real) * b := by simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · disproved/reduced · refuted the missing-nonnegativity statement; proved its repaired form modulo level-zero exactness
* r2 · open · isolated support-aware slicing and elimination of the level-zero error slice
-/
