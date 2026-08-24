import Arlib.Probability.IIDProduct

/-!
# Transport a finite Bernoulli weight sum to `FinProb.Pr`

This is the representation bridge between the `ENNReal` weights used by `PMF` and the
real-valued explicit product probability space used by Arlib's Chernoff theorems.
-/

namespace Esa22Copy

open scoped BigOperators ENNReal Classical
open Finset

/--
INTERNAL (`bernoulliSum_twoSidedChernoff`): the real value of a finite sum of independent
Bernoulli product weights is the probability of the same event in `prodSpace`.
-/
theorem bernoulliSum_twoSidedChernoff_product_probability_transport
    {k : Nat} (p : Fin k → Set.Icc (0 : Real) 1)
    (coinMass : Fin k → Bool → Real)
    (hcoinMass : ∀ i b,
      coinMass i b = if b then (p i : Real) else 1 - (p i : Real))
    (h0 : ∀ i b, 0 ≤ coinMass i b)
    (h1 : ∀ i, ∑ b, coinMass i b = 1)
    (E : (Fin k → Bool) → Prop) :
    (∑ wanted : Fin k → Bool,
        (∏ i : Fin k,
          if wanted i then ENNReal.ofReal (p i : Real)
          else ENNReal.ofReal (1 - (p i : Real))) *
        if E wanted then 1 else 0).toReal =
      (Arlib.Probability.prodSpace coinMass h0 h1).toFinProb.Pr
        (Finset.univ.filter E) := by
  classical
  rw [ENNReal.toReal_sum]
  · rw [Arlib.Probability.FinProb.Pr, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro wanted _
    by_cases hE : E wanted
    · simp only [hE, if_true, mul_one]
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      change
        (if wanted i then ENNReal.ofReal (p i : Real)
          else ENNReal.ofReal (1 - (p i : Real))).toReal =
          coinMass i (wanted i)
      rw [hcoinMass i (wanted i)]
      cases wanted i with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ENNReal.toReal_ofReal (sub_nonneg.mpr (p i).property.2)
      | true =>
          simp only [↓reduceIte]
          exact ENNReal.toReal_ofReal (p i).property.1
    · simp [hE]
  · intro wanted _
    by_cases hE : E wanted
    · simp only [hE, if_true, mul_one]
      exact ENNReal.prod_ne_top fun i _ => by
        split <;> exact ENNReal.ofReal_ne_top
    · simp [hE]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · expanded `FinProb.Pr` and transported the finite ENNReal sum termwise
-/
