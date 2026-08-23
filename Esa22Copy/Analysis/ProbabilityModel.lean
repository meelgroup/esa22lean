import Esa22Copy.Model.Pseudocode

/-!
# Probability interfaces for the relaxed estimator

Arlib's output-event API expects a natural-number cost coordinate.  The relaxed
algorithm has no charged cost, so this file adds a zero-cost coordinate without
changing its state distribution.
-/

namespace Esa22Copy

/--
INTERNAL: equips the relaxed state distribution with a zero cost for Arlib event probabilities.
-/
noncomputable def relaxedRunCost (P : Params) (A : Stream P) :
    PMF (RelaxedState P × Nat) :=
  (relaxedRun P A).map fun s => (s, 0)

end Esa22Copy
