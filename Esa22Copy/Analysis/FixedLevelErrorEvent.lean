import Esa22Copy.Analysis.LevelSampleIndependence

/-!
# Fixed-level error event

This is the unconditional Algorithm 3 deviation event used to dominate one
adaptive-level slice of the relaxed estimator.
-/

namespace Esa22Copy

/--
INTERNAL: the fixed-level sample estimate at the final stream prefix is outside
the required multiplicative-error interval.
-/
def fixedLevelErrorEvent (P : Params) (A : Stream P) (k : Nat) : Set (LevelCoins P) :=
  {coins |
    ((levelSample coins A k (Fin.last P.m)).card : Real) /
          ((2 : Real) ^ (-(k : Int))) ∉
      Arlib.relErr P.eps (F0 A : Real)}

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · added · normalized the unconditional final-prefix fixed-level error event
-/
