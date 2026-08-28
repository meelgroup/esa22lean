import Esa22Copy.Interface.Pseudocode

/-!
# The critical sampling level

The critical level is the dyadic scale at which the expected full-stream sample
size lies between one quarter and one half of the threshold.  Keeping the choice
as a named definition lets both tails in the relaxed-error proof use the same
cutoff.
-/

namespace Esa22Copy

/--
INTERNAL: the logarithmic cutoff shared by the two relaxed-estimator tail bounds.
-/
noncomputable def criticalLevel (P : Params) (A : Stream P) : Nat :=
  Nat.floor
    (Real.logb 2
      (4 * (F0 A : Real) / (threshold P : Real)))

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · introduced the shared logarithmic cutoff for the two relaxed-error tails
-/
