import Esa22Copy.Model.Pseudocode
import Esa22Copy.Analysis.LevelSampleControllers
import Esa22Copy.Analysis.UniformAcceptsAtInjective

/-!
# Fixed-level sampling law

This file isolates the corrected Algorithm 3 invariant.  A uniform table of all
per-occurrence bit blocks makes the latest occurrence of each distinct prefix item
decide its membership at a fixed level.
-/

namespace Esa22Copy

/--
INTERNAL: the finite product distribution of the per-position bit blocks used by Algorithm 3.
-/
noncomputable def freshLevelCoins (P : Params) : PMF (LevelCoins P) :=
  PMF.uniformOfFintype (LevelCoins P)

/--
PAPER: esa22-final.tex:620-645, corrected fixed-level independent-membership invariant.
-/
theorem levelSample_independent_membership (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) (k : Nat) (hk : k ≤ P.m)
    (wanted : {a // a ∈ prefixDistinct A i} → Bool) :
    (freshLevelCoins P).toOuterMeasure
        {coins | ∀ a : {a // a ∈ prefixDistinct A i},
          (a.1 ∈ levelSample coins A k i) = wanted a} =
      ∏ a : {a // a ∈ prefixDistinct A i},
        if wanted a then ((2 : ENNReal) ^ k)⁻¹ else 1 - ((2 : ENNReal) ^ k)⁻¹ := by
  obtain ⟨controller, hcontroller, hmembership⟩ :=
    levelSample_has_injective_controllers P A i k
  simpa only [freshLevelCoins, hmembership] using
    uniform_acceptsAt_injective P controller hcontroller k hk wanted

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · split deterministic latest-occurrence control from finite uniform-table counting
-/
