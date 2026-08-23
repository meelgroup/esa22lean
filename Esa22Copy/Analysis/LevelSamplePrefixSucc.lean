import Esa22Copy.Model.Pseudocode

/-!
# Fixed-level samples at a successor prefix

Processing one more stream position in Algorithm 3 is exactly one application of
`refresh`, including when the arriving value occurred earlier in the stream.
-/

namespace Esa22Copy

/--
INTERNAL: deterministic successor-prefix equation for the erase-then-insert sample fold.
-/
theorem levelSample_prefix_succ (P : Params) (A : Stream P) (coins : LevelCoins P)
    (k r : Nat) (hr : r < P.m) :
    levelSample coins A k ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      refresh (A ⟨r, hr⟩) k (coins ⟨r, hr⟩)
        (levelSample coins A k ⟨r, Nat.lt_succ_of_lt hr⟩) := by
  simp [levelSample, List.take_add_one, hr]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · reduced the successor prefix to `List.take_add_one` and `foldl_append`
-/
