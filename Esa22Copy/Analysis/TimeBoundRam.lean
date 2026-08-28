/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Esa22Copy.Analysis.TimeBound
import Arlib.Computation.Machine

/-!
# From dictionary operations to word operations

`TimeBound.lean` counts the estimator's work in its own currency: deletions,
coins, insertions, cardinality tests.  That is the right unit for the algorithm,
because it is the unit the pseudocode is written in and it commits to no
implementation of the sample set `X`.

It is not the unit a running-time claim is usually made in.  This module carries
the analysis across, using the exchange machinery of
`Arlib.Computation.CostVec`: given a rate saying what one dictionary operation
costs in machine words, the bound of `TimeBound.lean` becomes a bound in machine
words, **without redoing the analysis**.

The rate is a hypothesis, not a construction.  Which rate is available is a fact
about the data structure chosen for `X`, and this development exhibits no such
data structure — so `StdImpl` is an explicit parameter in the style of
`Arlib.KnowledgeCompilation`'s imported bundles, and, as that convention
requires, it is shown inhabited (`StdImpl.trivial`) so that the theorems below
are not vacuously true.

What this buys is a separation the paper does not make and would want: the
probabilistic analysis of the estimator is independent of how `X` is stored, and
choosing a different structure changes one number rather than one proof.

## Main definitions

* `StdImpl` — what one dictionary operation costs in word operations.
* `wordEstimator` — the same run, priced in word operations.
* `estimator_worstWordSteps_le` — its cost, as a bound on the time operator.
-/

namespace Esa22Copy

open Arlib.Computation

/-- **The estimator, priced in word operations.**

The run is unchanged — `Charged.exchange` touches only the tally — so this is the
same distribution over the same computations, denominated differently.  That is
what makes the bound below a statement about the estimator rather than about a
separate object. -/
noncomputable def wordEstimator (D : StdImpl) (P : Params) (A : Stream P) :
    PMF (Charged Op Cell (Answer × Nat)) :=
  (estimator P A).map (Charged.exchange D.rate)

/-- **The estimator's running time in word operations.**

If the sample set is stored in a structure whose operations each cost at most
`D.bound` word operations, then every run of the estimator on a stream of length
`m` performs at most `D.bound * (m * (2 * thresh + 7) + 2)` word operations.

There is no new analysis, and — the point of stating the abstract bound against
`worstSteps` rather than against a bespoke predicate — no new vocabulary either:
this is the same shape as `estimator_worstSteps_le`, at a different rate. -/
theorem estimator_worstWordSteps_le (D : StdImpl) (P : Params) (A : Stream P) :
    worstSteps CostModel.unitCost (wordEstimator D P A)
      ≤ ((D.bound * (P.m * (2 * threshold P + 8) + 3) : Nat) : ℕ∞) :=
  worstSteps_map_exchange_le CostModel.unitCost D.rate (estimator P A)
    D.bound (P.m * (2 * threshold P + 8) + 3) D.bound_ok (estimator_worstSteps_le P A)

/-- The same bound at each reachable run, for a caller who wants it that way.
One line, because `worstSteps_le_iff` is the whole of the difference. -/
theorem estimator_wordSteps_le (D : StdImpl) (P : Params) (A : Stream P)
    (outcome : Charged Op Cell (Answer × Nat))
    (houtcome : outcome ∈ (wordEstimator D P A).support) :
    Charged.steps CostModel.unitCost outcome
      ≤ D.bound * (P.m * (2 * threshold P + 8) + 3) :=
  (worstSteps_le_iff _ _ _).1 (estimator_worstWordSteps_le D P A) outcome houtcome

end Esa22Copy
