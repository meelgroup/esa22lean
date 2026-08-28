import Esa22Copy.Model.Prelude
import Esa22Copy.Analysis.TheoremProof
import Esa22Copy.Analysis.TimeBound

/-!
# Accuracy, worst-case space and worst-case time of the ESA 2022 estimator

Every statement here is about `Esa22Copy.estimator`, the algorithm of
`Model/Program.lean`.  `#modelClosureOfType` below machine-checks that each
statement unfolds only to constants defined under `Model/`.
-/

namespace Esa22Copy

open Arlib.Computation

/--
PAPER: esa22-final.tex:500-508.

For every valid parameter block and stream, the estimator is accurate with
probability at least `1 - delta`, every reachable run holds at most `threshold P`
sample items at its highest point, and that bound has the paper's displayed big-O
form in its nondegenerate `n,m ≥ 2` regime.

The space clause is an operator applied to the program.
`Arlib.Computation.worstSpace` is the supremum, over the runs that can happen, of
what `Charged.space` says a run held, and that profile is computed by the
elaborator from the sequence of dictionary operations the program performs; there
is nowhere in `Model/Program.lean` to write what a line occupies.

The same `estimator` carries all three clauses: `estimatorOutput` is
`Charged.val` applied to it, and `esa22CopyTime` bounds `worstSteps` of it.

The bound is in **cells**, one per sample item.  The paper's bits are
`itemBits P = ⌈log₂ n⌉` per cell — assumption 3 in `Model/Prelude.lean` — and
`PaperItemSpaceBigO` is where that product meets the paper's displayed
asymptotic.
-/
theorem esa22Copy (hprior : Prior) (P : Params) (A : Stream P) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (estimatorOutput P A) (accurateEvent P A) ∧
    Arlib.Computation.worstSpace Cell.cell 0 (estimator P A)
      ≤ ((threshold P : Nat) : ℕ∞) ∧
    PaperItemSpaceBigO := by
  exact esa22Copy_proof hprior P A

/--
NOT IN THE PAPER.  The paper states a space bound and no running-time bound; the
word "time" does not occur in it.

`Arlib.Computation.worstSteps R mu` is the largest number of steps a run of the
randomised charged computation `mu` can perform, priced at the rate `R`; here `R`
charges one for each dictionary operation.

The quantity is `P.m * (2 * threshold P + 8) + 3`: five operations per arrival —
the test asking whether the run has already stopped, the erase, the insertion
coin, the reinsertion, and the comparison of `|X|` with the threshold — plus
`2 * threshold P + 3` for each thinning — one retain/discard coin and at most one
deletion per sampled element, the level halving, the second threshold test and
the write of bottom into the answer register — plus three for the paper's last
line, `return |X| / p`: the stop test, the size query, and the division.  It is
`Arlib.Computation.Charged.cost` applied to the program of `Model/Program.lean`,
so it counts the operations the algorithm performs.

`Analysis/TimeBoundRam.lean` carries the same bound into word operations, given a
rate for the sample-set implementation.
-/
theorem esa22CopyTime (P : Params) (A : Stream P) :
    worstSteps (Rate.unit StdOp) (estimator P A)
      ≤ ((P.m * (2 * threshold P + 8) + 3 : Nat) : ℕ∞) :=
  estimator_worstSteps_le P A

end Esa22Copy

#modelClosureOfType Esa22Copy.esa22Copy
#print axioms Esa22Copy.esa22Copy
#modelClosureOfType Esa22Copy.esa22CopyTime
#print axioms Esa22Copy.esa22CopyTime

/-! The other half of the closure audit: `#modelClosureOfType` above says no
statement reaches outside `Model/`; this says nothing inside `Model/` goes
unreached by a statement.

`Model/Program.lean` runs the same check against a tighter seed — the algorithm's
own entry points — which keeps a definition like `paperSpaceScale` out of the
program even though the headline statement reaches it. -/
#surplusIn Esa22Copy.Model from Esa22Copy.esa22Copy Esa22Copy.esa22CopyTime

/-! The driver seal, with the whole development in scope: `Interface/` and
`Analysis/` too, which is where the specification views of a run live. -/
#driverSeal Esa22Copy.Program
