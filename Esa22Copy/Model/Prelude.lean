import Arlib.Prelude
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Image
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Esa22Copy.Meta.ModelClosure

/-!
# Static model for the distinct-elements estimator

The paper's finite universe is represented by `Fin n` (with zero-based labels), and a
length-`m` stream is a function `Fin m → Fin n`.  Prefixes use processed-position counts
`i : Fin (m + 1)`: position `j` belongs to the prefix exactly when `j.val < i.val`.
Base-two logarithms are Mathlib's `Real.logb 2`, so the threshold and item charge share
one ambient-library convention for logarithms and ceilings.
-/

namespace Esa22Copy

/-! ## Vocabulary -/

/-- The positive universe and stream sizes and the two probabilities appearing in the paper. -/
structure Params where
  n : Nat
  m : Nat
  hn : 0 < n
  hm : 0 < m
  eps : Real
  delta : Real
  heps : eps ∈ Set.Ioo 0 1
  hdelta : delta ∈ Set.Ioo 0 1

/-- The paper's finite universe `[n]`, harmlessly relabelled from one-based to zero-based. -/
abbrev Item (P : Params) := Fin P.n

/-- An ordered stream of exactly `m` universe elements. -/
abbrev Stream (P : Params) := Fin P.m → Item P

/-- The set of universe values that occur anywhere in the stream. -/
def distinctSet {P : Params} (A : Stream P) : Finset (Item P) :=
  Finset.univ.image A

/-- Values occurring in the first `i` processed positions, where `i` ranges from `0` to `m`. -/
def prefixDistinct {P : Params} (A : Stream P) (i : Fin (P.m + 1)) : Finset (Item P) :=
  (Finset.univ.filter fun j : Fin P.m => j.val < i.val).image A

/-- The natural threshold `ceil ((12 / eps^2) log_2 (8m/delta))`. -/
noncomputable def threshold (P : Params) : Nat :=
  Nat.ceil ((12 / P.eps ^ 2) * Real.logb 2 (8 * (P.m : Real) / P.delta))

/-- Bits charged per stored item under the paper's item-only accounting convention. -/
noncomputable def itemBits (P : Params) : Nat :=
  Nat.ceil (Real.logb 2 (P.n : Real))

/-! ## The quantity -/

/-- `F₀(A)`: the number of distinct universe values occurring in `A`. -/
def F0 {P : Params} (A : Stream P) : Nat :=
  (distinctSet A).card

/-! ## Finite Boolean families -/

/-- The real-valued sum of a finite family of Boolean random variables. -/
def bernoulliSum {Omega : Type*} {k : Nat} (v : Fin k → Omega → Bool) (omega : Omega) : Real :=
  ∑ i, if v i omega then 1 else 0

/-- The expectation of a finite Boolean sum under `P`. -/
noncomputable def bernoulliMean {Omega : Type*} [MeasurableSpace Omega] {k : Nat}
    (P : MeasureTheory.Measure Omega) (v : Fin k → Omega → Bool) : Real :=
  MeasureTheory.integral P (bernoulliSum v)

/-- The inclusive event that `V` deviates from `mu` by at least the relative factor `beta`. -/
def relativeDeviationEvent {Omega : Type*} (V : Omega → Real) (mu beta : Real) : Set Omega :=
  {omega | beta * mu ≤ |V omega - mu|}

end Esa22Copy
