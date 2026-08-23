import Esa22Copy.Analysis.RepresentedStateAdjacentCrossing

/-!
# Coupling a first bad-level crossing to its fixed-level sample

This module isolates the causal coupling needed for one iteration of the paper's
first-crossing argument.  Unlike the public final-state coupling, it retains both
the predecessor and successor relaxed states together with their common coin table.
-/

namespace Esa22Copy

/--
INTERNAL: a supported successor transition that crosses level `k` either started
above `k` or reached the threshold in the level-`k` sample at the new prefix.
-/
theorem bad_level_crossing_coupling (P : Params) (A : Stream P) (k r : Nat)
    (hk : k ≤ P.m) (hr : r < P.m) :
    ∃ γ : PMF (RelaxedState P × (RelaxedState P × LevelCoins P)),
      γ.map (fun z => z.1) =
          relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_lt hr⟩ ∧
      γ.map (fun z => z.2.1) =
          relaxedRunPrefix P A ⟨r + 1, Nat.succ_lt_succ hr⟩ ∧
      γ.map (fun z => z.2.2) = freshLevelCoins P ∧
      ∀ z ∈ γ.support, k < z.2.1.level →
        k < z.1.level ∨
          threshold P ≤
            (levelSample z.2.2 A k
              ⟨r + 1, Nat.succ_lt_succ hr⟩).card := by
  obtain ⟨before, after, hbefore, hafter, hcrossing⟩ :=
    representedState_adjacent_crossing P A k r hk hr
  let γ : PMF (RelaxedState P × (RelaxedState P × LevelCoins P)) :=
    (freshLevelCoins P).map fun coins => (before coins, (after coins, coins))
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact hbefore
  · rw [PMF.map_comp]
    exact hafter
  · rw [PMF.map_comp]
    change (freshLevelCoins P).map id = freshLevelCoins P
    exact PMF.map_id _
  · intro z hz hlevel
    obtain ⟨coins, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact hcrossing coins hlevel

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · reduced · constructed the requested three-way coupling from the isolated
  common-table adjacent-prefix representation
* r4 · reduced · isolated the missing causal three-way coupling that retains
  predecessor state, successor state, and the common fixed-level coin table
-/
