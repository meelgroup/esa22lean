import Esa22Copy.Analysis.RelaxedRunPrefixBadLevelStep

/-!
# Iterated first-crossing bound for relaxed prefixes

Iteration of the one-step recurrence charges at most one fixed-level tail bound
for each processed stream position.
-/

namespace Esa22Copy

/--
INTERNAL: after `r` updates, uniformly bounded first-crossing probabilities sum
to at most `r * b`.
-/
theorem relaxedRunPrefix_bad_level_bound (P : Params) (A : Stream P)
    (k : Nat) (b : Real) (hb : 0 ≤ b) (hk : k ≤ P.m)
    (htail : ∀ i : Fin (P.m + 1),
      ((freshLevelCoins P).toOuterMeasure
        {coins | threshold P ≤ (levelSample coins A k i).card}).toReal ≤ b)
    (r : Nat) (hr : r ≤ P.m) :
    ((relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_le hr⟩).toOuterMeasure
      {s | k < s.level}).toReal ≤ (r : Real) * b := by
  induction r with
  | zero =>
      simp only [relaxedRunPrefix, List.take_zero, List.foldlM_nil]
      rw [show (pure ({ samples := ∅, level := 0 } : RelaxedState P) :
        PMF (RelaxedState P)) = PMF.pure { samples := ∅, level := 0 } by rfl]
      rw [PMF.toOuterMeasure_pure_apply]
      simp
  | succ r ih =>
      have hrlt : r < P.m := Nat.lt_of_succ_le hr
      calc
        ((relaxedRunPrefix P A
            ⟨r + 1, Nat.succ_lt_succ hrlt⟩).toOuterMeasure
            {s | k < s.level}).toReal ≤
            ((relaxedRunPrefix P A
                ⟨r, Nat.lt_succ_of_lt hrlt⟩).toOuterMeasure
                {s | k < s.level}).toReal +
              ((freshLevelCoins P).toOuterMeasure
                {coins | threshold P ≤
                  (levelSample coins A k
                    ⟨r + 1, Nat.succ_lt_succ hrlt⟩).card}).toReal :=
          relaxedRunPrefix_bad_level_step P A k r hk hrlt
        _ ≤ (r : Real) * b + b :=
          add_le_add (ih (Nat.le_of_lt hrlt))
            (htail ⟨r + 1, Nat.succ_lt_succ hrlt⟩)
        _ = (r + 1 : Nat) * b := by
          push_cast
          ring

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · iterated the isolated one-step recurrence over exactly the `r`
  nonempty prefixes
-/
