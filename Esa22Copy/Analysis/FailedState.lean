import Esa22Copy.Model.Pseudocode

/-!
# Explicit failure as a state predicate

This predicate connects the absorbing failure marker in the internal state to the
`none` answer exposed by `finish`.
-/

namespace Esa22Copy

/--
INTERNAL: names the internal-state event whose finished output is explicit failure.
-/
def FailedState {P : Params} (s : State P) : Prop :=
  (finish s).answer = none

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · added · named the internal state event corresponding to explicit output failure
-/
