import Esa22Copy.Analysis.RelaxedCoupling
import Esa22Copy.Analysis.RepresentedStatePrefixInduction
import Esa22Copy.Analysis.RepresentedStatePrefixSuccessorCrossing

/-!
# Adjacent represented states and a bad-level crossing

This module isolates the causal, common-table representation needed for one step of
the paper's first-crossing argument.  Both adjacent relaxed states are driven by the
same level-coin table, so a newly crossed level can be related pathwise to the
corresponding fixed-level sample.
-/

namespace Esa22Copy

/--
INTERNAL: adjacent relaxed prefixes admit a common-table representation in which
crossing above `k` either occurred earlier or was caused by a threshold-sized
level-`k` sample at the new prefix.
-/
theorem representedState_adjacent_crossing (P : Params) (A : Stream P) (k r : Nat)
    (hk : k ≤ P.m) (hr : r < P.m) :
    ∃ before after : LevelCoins P → RelaxedState P,
      (freshLevelCoins P).map before =
          relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_lt hr⟩ ∧
      (freshLevelCoins P).map after =
          relaxedRunPrefix P A ⟨r + 1, Nat.succ_lt_succ hr⟩ ∧
      ∀ coins : LevelCoins P, k < (after coins).level →
        k < (before coins).level ∨
          threshold P ≤
            (levelSample coins A k
              ⟨r + 1, Nat.succ_lt_succ hr⟩).card := by
  let i : Fin (P.m + 1) := ⟨r + 1, Nat.succ_lt_succ hr⟩
  obtain ⟨before, hbefore, hsample, hlevel, hcausal⟩ :=
    representedState_prefix_induction P A i
      (levelSample_prefix_succ P A) (levelSample_succ_level P A)
      (uniform_table_fresh_frontier P) r (by simp [i])
  obtain ⟨after, hafter, _hsampleAfter, _hlevelAfter, _hcausalAfter, hcrossing⟩ :=
    representedState_prefix_successor_crossing P A i
      (levelSample_prefix_succ P A) (levelSample_succ_level P A)
      (uniform_table_fresh_frontier P) r (by simp [i]) before hbefore hsample
      hlevel hcausal
  refine ⟨before, after, ?_, ?_, ?_⟩
  · simpa only [freshLevelCoins, relaxedRunPrefix] using hbefore
  · simpa only [freshLevelCoins, relaxedRunPrefix] using hafter
  · intro coins hbad
    simpa only [i] using hcrossing k hk coins hbad

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r6 · reduced · closed from prefix induction plus the strengthened represented-state
  successor crossing lemma
* r5 · open · isolated the coherent adjacent-prefix representation and its pathwise
  crossing invariant required by `bad_level_crossing_coupling`
-/
