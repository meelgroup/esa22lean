import Esa22Copy.Analysis.FixedLevelErrorEvent
import Esa22Copy.Analysis.LevelSampleCardAsIndicatorCount

/-!
# Membership-vector form of the fixed-level error event

At the final prefix, counting the sampled set is the same as counting the true
coordinates of its membership vector over the distinct stream items.  This file
also reconciles the integer negative power used by the pseudocode with the natural
power used by the Bernoulli law.
-/

namespace Esa22Copy

/--
INTERNAL: deterministic normalization of the fixed-level error event to the Boolean
membership-count event consumed by finite Bernoulli concentration.
-/
theorem fixedLevelErrorEvent_eq_membership_error (P : Params) (A : Stream P) (k : Nat) :
    fixedLevelErrorEvent P A k =
      {coins |
        ((Finset.univ.filter fun a : {a // a ∈ prefixDistinct A (Fin.last P.m)} =>
            decide (a.1 ∈ levelSample coins A k (Fin.last P.m))).card : Real) /
              ((1 / 2 : Real) ^ k) ∉
          Arlib.relErr P.eps
            (Fintype.card {a // a ∈ prefixDistinct A (Fin.last P.m)} : Real)} := by
  ext coins
  simp only [fixedLevelErrorEvent, Set.mem_setOf_eq]
  rw [levelSample_card_as_indicator_count]
  have hdenom : (2 : Real) ^ (-(k : Int)) = (1 / 2 : Real) ^ k := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  have hprefix : prefixDistinct A (Fin.last P.m) = distinctSet A := by
    ext a
    simp [prefixDistinct, distinctSet]
  have hcard :
      Fintype.card {a // a ∈ prefixDistinct A (Fin.last P.m)} = F0 A := by
    rw [Fintype.card_coe, hprefix]
    rfl
  rw [hdenom, hcard]
  simp only [decide_eq_true_eq]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · normalized the final-prefix cardinality and dyadic-power presentations
-/
