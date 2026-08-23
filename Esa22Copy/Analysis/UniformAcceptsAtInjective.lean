import Esa22Copy.Analysis.AcceptsAtPatternRatio
import Esa22Copy.Analysis.UniformPiInjectivePattern

/-!
# Independent acceptance on injective coordinates

A uniform table of Boolean blocks has the product law for `acceptsAt` constraints
placed at pairwise distinct table coordinates.
-/

namespace Esa22Copy

/--
INTERNAL: finite counting law for `acceptsAt` on pairwise distinct coordinates.
-/
theorem uniform_acceptsAt_injective (P : Params) {I : Type*} [Fintype I]
    (controller : I → Fin P.m) (hcontroller : Function.Injective controller)
    (k : Nat) (hk : k ≤ P.m) (wanted : I → Bool) :
    (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure
        {coins | ∀ a : I,
          (acceptsAt k (coins (controller a)) = true) = (wanted a = true)} =
      ∏ a : I,
        if wanted a then ((2 : ENNReal) ^ k)⁻¹ else 1 - ((2 : ENNReal) ^ k)⁻¹ := by
  rw [uniform_pi_injective_pattern controller hcontroller
    (fun a bits ↦ ((acceptsAt k bits = true) = (wanted a = true)))]
  apply Finset.prod_congr rfl
  intro a _
  exact acceptsAt_pattern_ratio P k hk (wanted a)

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · reduced to injective-coordinate counting and the exact one-block ratio
* r1 · open · isolated finite counting for acceptance constraints on injective coordinates
-/
