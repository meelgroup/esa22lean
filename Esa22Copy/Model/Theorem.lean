import Esa22Copy.Model.Prior
import Esa22Copy.Model.Pseudocode
import Esa22Copy.Analysis.TheoremProof

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

end Esa22Copy

#modelClosureOfType Esa22Copy.esa22Copy
#print axioms Esa22Copy.esa22Copy
