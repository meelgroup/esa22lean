import Esa22Copy.Analysis.ProbabilityModel

/-!
# The simulation relation for the original and relaxed estimators

The algorithms agree on their sample and level until the original algorithm
enters its absorbing failed state.  After failure the relation deliberately
places no restriction on the relaxed execution.
-/

namespace Esa22Copy

/--
INTERNAL: simulation invariant asserting agreement of the common state while the
original estimator has not failed.
-/
def NonfailRel {P : Params} (s : State P) (r : RelaxedState P) : Prop :=
  finish s ∉ failEvent P →
    s.samples = r.samples ∧ s.level = r.level ∧ s.answer = none

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · added · isolated the simulation invariant used by the nonfailure coupling
-/
