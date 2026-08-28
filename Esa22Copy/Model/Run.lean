import Esa22Copy.Model.Program
import Arlib.Computation.ChargedPMF

/-!
# The run: where the randomness comes from

`Model/Program.lean` is the whole of Algorithm 1 and it computes; it does not
manufacture its own coins.  This file draws them.

It is `noncomputable` throughout because it mentions `PMF`.  That is why it is a
separate file: `noncomputable` is the one route past the compiler's half of the
cost seal, so the file that permits it cannot be the file that forbids it.
-/

set_option autoImplicit false

namespace Esa22Copy

open Arlib.Computation

/-- One tape cell, sealed.  `Block.ofFun` and `Coins.ofFinset` appear nowhere
else in the development. -/
noncomputable def freshCell (P : Params) : PMF (Program.Randomness P) :=
  (freshBlock P).bind fun bits =>
    (freshSubset P).map fun retained =>
      ⟨Block.ofFun bits, Coins.ofFinset retained⟩

/-- A tape of `n` independent cells.  Written by recursion so that the cons case
unfolds definitionally, which is what the fold proofs induct on. -/
noncomputable def freshTape (P : Params) : Nat → PMF (List (Program.Randomness P))
  | 0 => PMF.pure []
  | n + 1 => (freshCell P).bind fun r => (freshTape P n).map (r :: ·)

/-- The estimator: `Program.run` on a drawn tape, then `Program.report`.  The
report is bound in rather than computed here, so the last line of the algorithm
is charged like the rest.

The tape is drawn at length `P.m`, the length of `A`, and `Program.run` zips the
two: this is the line that decides no arrival goes uncoined.

The trailing `0` is not a cost.  `Arlib.Approximation.outProbR` takes a
`PMF (β × ℕ)` whose `ℕ` is a step count an author supplies, and which
`IsFPRAS.pinnedTime_of_cost_zero` shows is vacuous.  Both resource claims are
operators applied to this `estimator`. -/
noncomputable def estimator (P : Params) (A : Stream P) :
    PMF (Charged StdOp Cell (Answer × Nat)) :=
  ((freshTape P P.m).map (Program.run (threshold P) A)).map fun ce =>
    ce >>= fun e =>
      (fun answer => (answer, 0))
        <$> Program.report e.sampler e.result e.samples

/-- The estimator with its meters dropped: what the paper returns. -/
noncomputable def estimatorOutput (P : Params) (A : Stream P) : PMF (Answer × Nat) :=
  (estimator P A).map Charged.val

end Esa22Copy

/-! `#driverSeal` runs at the bottom of `Model/Theorem.lean`, where the whole
development is in scope; here there would be only `Model/` to check. -/

#modelClosure Esa22Copy.estimator
#modelClosure Esa22Copy.estimatorOutput
