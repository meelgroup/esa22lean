import Esa22Copy.Analysis.LevelSamplePrefixSucc

/-!
# Congruence of a fixed-level prefix sample

The fixed-level sample through a prefix only inspects rows in that prefix and bit
coordinates strictly below its level.
-/

namespace Esa22Copy

/--
INTERNAL: two coin tables agreeing below a level throughout a prefix produce the same
fixed-level sample on that prefix.
-/
theorem levelSample_eq_of_eq_below (P : Params) (A : Stream P)
    (x y : LevelCoins P) (k : Nat) (i : Fin (P.m + 1))
    (hxy : ∀ (j : Fin P.m) (q : Fin (P.m + 1)),
      j.val < i.val → q.val < k → x j q = y j q) :
    levelSample x A k i = levelSample y A k i := by
  have haccepts (j : Fin P.m) (hj : j.val < i.val) :
      acceptsAt k (x j) = acceptsAt k (y j) := by
    unfold acceptsAt
    split
    next hk =>
      congr 1
      apply List.ext_getElem
      · simp
      · intro q hqx hqy
        have hbounds : q < k ∧ q < P.m + 1 := by
          simpa using hqx
        rw [List.getElem_take, List.getElem_take,
          List.getElem_ofFn, List.getElem_ofFn]
        exact hxy j ⟨q, hbounds.2⟩ hj hbounds.1
    next _ => rfl
  have aux : ∀ (r : Nat) (hr : r ≤ i.val),
      levelSample x A k ⟨r, lt_of_le_of_lt hr i.isLt⟩ =
        levelSample y A k ⟨r, lt_of_le_of_lt hr i.isLt⟩ := by
    intro r
    induction r with
    | zero =>
        intro hr
        rfl
    | succ r ih =>
        intro hr
        have hrm : r < P.m := by omega
        have hri : r < i.val := by omega
        rw [levelSample_prefix_succ P A x k r hrm,
          levelSample_prefix_succ P A y k r hrm]
        rw [ih (by omega)]
        unfold refresh
        rw [haccepts ⟨r, hrm⟩ hri]
  simpa using aux i.val le_rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · proved · inducted over the prefix after proving `acceptsAt` only reads bits below its level
-/
