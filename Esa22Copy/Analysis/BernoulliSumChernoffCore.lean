import Esa22Copy.Model.Pseudocode
import Arlib.Probability.Chernoff
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffRecursiveMassExpansion
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffOuterMeasureOfMassExpansion
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffProductProbabilityTransport
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffProductIndicMean
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffInclusiveEventProbabilityLeTailSum
import Esa22Copy.Analysis.BernoulliSumTwoSidedChernoffTailSumLeBound

/-!
# Chernoff bound for a recursively specified Bernoulli sum

This module is deliberately parameterized by the two PMF constructors.  Their concrete
definitions live in `Model.Theorem`, which imports the proof side, so mentioning those
definitions here would create an import cycle.
-/

namespace Esa22Copy

/--
INTERNAL: the two-sided Chernoff estimate for any PMF family satisfying the concrete
head/tail recursion used by `bernoulliSumPMF`.
-/
theorem bernoulliSum_twoSidedChernoff_core
    (coin : Set.Icc (0 : Real) 1 → PMF Bool)
    (sumLaw : (k : Nat) → (Fin k → Set.Icc (0 : Real) 1) → PMF Real)
    (hcoin : ∀ q b, coin q b =
      (if b then ENNReal.ofReal (q : Real) else ENNReal.ofReal (1 - (q : Real))))
    (hzero : ∀ p : Fin 0 → Set.Icc (0 : Real) 1, sumLaw 0 p = PMF.pure 0)
    (hsucc : ∀ (k : Nat) (p : Fin (k + 1) → Set.Icc (0 : Real) 1),
      sumLaw (k + 1) p =
        (coin (p 0)).bind fun b ↦
          (sumLaw k fun i ↦ p i.succ).bind fun s ↦
            PMF.pure ((if b then 1 else 0) + s))
    (k : Nat) (p : Fin k → Set.Icc (0 : Real) 1)
    (β : Real) (hβ : 0 < β) :
    ((sumLaw k p).toOuterMeasure
      {V | β * (∑ i, (p i : Real)) ≤ |V - ∑ i, (p i : Real)|}).toReal ≤
      2 * Real.exp (- (β ^ 2 * ∑ i, (p i : Real)) / (2 + β)) := by
  classical
  let μ : Real := ∑ i : Fin k, (p i : Real)
  let coinMass : Fin k → Bool → Real := fun i b ↦
    if b then (p i : Real) else 1 - (p i : Real)
  let V : (Fin k → Bool) → Real := fun wanted ↦
    ∑ i : Fin k, if wanted i then (1 : Real) else 0
  have hμ : 0 ≤ μ := by
    dsimp [μ]
    exact Finset.sum_nonneg fun i _ ↦ (p i).property.1
  have hcoinMass : ∀ i b,
      coinMass i b = if b then (p i : Real) else 1 - (p i : Real) := by
    intro i b
    rfl
  have hmass0 : ∀ i b, 0 ≤ coinMass i b := by
    intro i b
    rw [hcoinMass]
    split
    · exact (p i).property.1
    · exact sub_nonneg.mpr (p i).property.2
  have hmass1 : ∀ i, ∑ b, coinMass i b = 1 := by
    intro i
    simp [coinMass]
  have hmass : ∀ x : Real,
      sumLaw k p x =
        ∑ wanted : Fin k → Bool,
          (∏ i : Fin k,
            if wanted i then ENNReal.ofReal (p i : Real)
            else ENNReal.ofReal (1 - (p i : Real))) *
          PMF.pure (V wanted) x := by
    intro x
    simpa [V] using
      bernoulliSum_twoSidedChernoff_recursive_mass_expansion
        coin sumLaw hcoin hzero hsucc k p x
  have houter :=
    bernoulliSum_twoSidedChernoff_outerMeasure_of_mass_expansion
      p (sumLaw k p) hmass {x | β * μ ≤ |x - μ|}
  have htransport :=
    bernoulliSum_twoSidedChernoff_product_probability_transport
      p coinMass hcoinMass hmass0 hmass1
        (fun wanted ↦ β * μ ≤ |V wanted - μ|)
  have hmean :=
    bernoulliSum_twoSidedChernoff_product_indicMean p coinMass hcoinMass
  have hcount (wanted : Fin k → Bool) :
      (Arlib.Probability.indicCount (Finset.univ : Finset (Fin k))
          (fun _ ↦ {true}) wanted : Real) = V wanted := by
    simp [Arlib.Probability.indicCount, V]
  have hupper :
      (Arlib.Probability.prodSpace coinMass hmass0 hmass1).toFinProb.Pr
          (Finset.univ.filter fun wanted ↦ (1 + β) * μ ≤ V wanted) ≤
        Real.exp (- (β ^ 2 * μ) / (2 + β)) := by
    simpa [hmean, hcount] using
      (Arlib.Probability.chernoff_upper coinMass hmass0 hmass1
        (Finset.univ : Finset (Fin k)) (fun _ ↦ {true}) hβ)
  have hlower :
      (Arlib.Probability.prodSpace coinMass hmass0 hmass1).toFinProb.Pr
          (Finset.univ.filter fun wanted ↦ V wanted ≤ (1 - β) * μ) ≤
        Real.exp (- (β ^ 2 * μ) / 2) := by
    simpa [hmean, hcount] using
      (Arlib.Probability.chernoff_lower coinMass hmass0 hmass1
        (Finset.univ : Finset (Fin k)) (fun _ ↦ {true}) hβ)
  have hsplit :=
    bernoulliSum_twoSidedChernoff_inclusive_event_probability_le_tail_sum
      (Arlib.Probability.prodSpace coinMass hmass0 hmass1).toFinProb V μ β
  have hfinal := bernoulliSum_twoSidedChernoff_tail_sum_le_bound
    _ _ μ β hμ hβ hupper hlower
  rw [show {x : Real | β * (∑ i, (p i : Real)) ≤ |x - ∑ i, (p i : Real)|} =
      {x : Real | β * μ ≤ |x - μ|} by rfl, houter]
  calc
    _ = (Arlib.Probability.prodSpace coinMass hmass0 hmass1).toFinProb.Pr
          (Finset.univ.filter fun wanted ↦ β * μ ≤ |V wanted - μ|) := by
        simpa [V] using htransport
    _ ≤ 2 * Real.exp (- (β ^ 2 * μ) / (2 + β)) := hsplit.trans hfinal
    _ = 2 * Real.exp (- (β ^ 2 * ∑ i, (p i : Real)) / (2 + β)) := by rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · transported the recursive PMF expansion to Arlib's finite product space
  and combined its inclusive upper and lower Chernoff bounds
* r3 · factored · isolated the recursive-law concentration theorem to break the
  `Model.Theorem`/`Analysis.TheoremProof` import cycle.
-/
