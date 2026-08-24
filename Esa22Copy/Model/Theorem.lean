import Esa22Copy.Model.Prior
import Esa22Copy.Model.Pseudocode
import Esa22Copy.Analysis.TheoremProof
import Esa22Copy.Analysis.BernoulliSumChernoffCore

/-!
# Accuracy and worst-case space of the ESA 2022 distinct-elements estimator
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:500-508.

For every valid parameter block and stream, the estimator is accurate with probability
at least `1 - delta`, every reachable run obeys both deterministic item-only space
bounds, and those exact bounds have the paper's displayed big-O form in its
nondegenerate `n,m ≥ 2` regime.
-/
theorem esa22Copy (hprior : Prior) (P : Params) (A : Stream P) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (run P A) (accurateEvent P A) ∧
    WorstCaseSpace (run P A) (threshold P * itemBits P) ∧
    PaperItemSpaceBigO := by
  exact esa22Copy_proof hprior P A

/-- A Bernoulli PMF at an arbitrary real rate in `[0, 1]`. -/
noncomputable def bernoulliPMF (p : Set.Icc (0 : Real) 1) : PMF Bool :=
  bernoulliPMFModel p

/--
Draw independent Bernoulli variables at the supplied real rates and return their sum.
Independence is the recursive `PMF.bind` composition, rather than a hypothesis about
an external probability space.  The rates are arbitrary reals in `[0, 1]`.
-/
noncomputable def bernoulliSumPMF :
    (k : Nat) → (p : Fin k → Set.Icc (0 : Real) 1) → PMF Real
  | k, p => bernoulliSumPMFModel k p

/--
For independent Bernoulli draws with arbitrary (not necessarily identical) real rates,
the inclusive two-sided relative-deviation event of their sum obeys the paper's
Chernoff bound.  The probability is measured directly on the output law of
`bernoulliSumPMF`, and the statement includes `k = 0`.
-/
theorem bernoulliSum_twoSidedChernoff
    (hprior : Prior) (k : Nat) (p : Fin k → Set.Icc (0 : Real) 1)
    (β : Real) (hβ : 0 < β) :
    ((bernoulliSumPMF k p).toOuterMeasure
      {V | β * (∑ i, (p i : Real)) ≤ |V - ∑ i, (p i : Real)|}).toReal ≤
      2 * Real.exp (- (β ^ 2 * ∑ i, (p i : Real)) / (2 + β)) := by
  exact bernoulliSum_twoSidedChernoff_proof hprior k p β hβ

end Esa22Copy

#modelClosureOfType Esa22Copy.esa22Copy
#print axioms Esa22Copy.esa22Copy
#modelClosure Esa22Copy.bernoulliPMF
#modelClosure Esa22Copy.bernoulliSumPMF
#modelClosureOfType Esa22Copy.bernoulliSum_twoSidedChernoff
#print axioms Esa22Copy.bernoulliSum_twoSidedChernoff
