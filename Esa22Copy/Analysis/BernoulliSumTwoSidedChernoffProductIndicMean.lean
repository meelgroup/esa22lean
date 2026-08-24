import Arlib.Probability.Chernoff

/-!
# Mean of the explicit inhomogeneous Bernoulli product

This isolates the finite-sum normalization needed to put Arlib's `indicMean` into the
mean appearing in the theorem statement.
-/

namespace Esa22Copy

open scoped BigOperators

/--
INTERNAL (`bernoulliSum_twoSidedChernoff`): for coordinate-dependent Bernoulli masses,
the indicator-count mean is the sum of the success rates.
-/
theorem bernoulliSum_twoSidedChernoff_product_indicMean
    {k : Nat} (p : Fin k → Set.Icc (0 : Real) 1)
    (coinMass : Fin k → Bool → Real)
    (hcoinMass : ∀ i b,
      coinMass i b = if b then (p i : Real) else 1 - (p i : Real)) :
    Arlib.Probability.indicMean coinMass (Finset.univ : Finset (Fin k))
        (fun _ => {true}) =
      ∑ i : Fin k, (p i : Real) := by
  simp [Arlib.Probability.indicMean, hcoinMass]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · unfolded `indicMean` and simplified the singleton success event pointwise
-/
