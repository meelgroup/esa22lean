import Esa22Copy.Analysis.LevelSampleIndependence
import Esa22Copy.Analysis.BernoulliUpperTailOfMeanLtHalfThreshold
import Esa22Copy.Analysis.LevelSampleCardAsIndicatorCount

/-!
# Upper tail of a fixed-level prefix sample

The exact joint membership law for a prefix is converted here into the one-sided
cardinality estimate used at a first threshold crossing.
-/

namespace Esa22Copy

/--
INTERNAL: independent Bernoulli membership and a mean below `T / 2` give the
fixed-prefix threshold tail used in the bad-level union bound.
-/
theorem levelSample_card_ge_threshold_le (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) (k D T : Nat) (hk : k ≤ P.m)
    (hcard : (prefixDistinct A i).card ≤ D)
    (hmean : (D : Real) * (2 : Real)⁻¹ ^ k < (T : Real) / 2) :
    ((freshLevelCoins P).toOuterMeasure
      {coins | T ≤ (levelSample coins A k i).card}).toReal ≤
        2 * Real.exp (-(T : Real) / 6) := by
  have hp : 0 ≤ (2 : Real)⁻¹ ^ k := by positivity
  have hcardReal : ((prefixDistinct A i).card : Real) ≤ (D : Real) := by
    exact_mod_cast hcard
  have hactualMean :
      (Fintype.card {a // a ∈ prefixDistinct A i} : Real) * (2 : Real)⁻¹ ^ k <
        (T : Real) / 2 := by
    rw [Fintype.card_coe]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcardReal hp) hmean
  have htail :=
    bernoulli_upper_tail_of_mean_lt_half_threshold
      (μ := freshLevelCoins P)
      (success := fun coins a => decide (a.1 ∈ levelSample coins A k i))
      k T (by
        intro wanted
        simpa using levelSample_independent_membership P A i k hk wanted)
      hactualMean
  simpa only [decide_eq_true_eq, levelSample_card_as_indicator_count] using htail

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · reduced · separated deterministic cardinality and Boolean-pattern-to-product Chernoff bridges
* r2 · reduced · isolated the independent-Bernoulli cardinality upper tail
-/
