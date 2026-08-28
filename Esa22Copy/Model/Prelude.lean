import Arlib.Prelude
import Arlib.Approximation.Counting
import Arlib.Computation.Std
import Esa22Copy.Meta.ModelClosure
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# What the theorem is stated in

The problem, the randomness that drives the estimator, the state it carries, and
what counts as a good answer.  `Model/Program.lean` and
`Interface/Pseudocode.lean` are both written in this vocabulary.

Every operation this algorithm performs is one of arlib's, so the currency is
`Arlib.Computation.StdOp`, the storage kind is
`Arlib.Computation.Cell`, and what an operation costs on the machine is an
`Arlib.Computation.StdImpl`.

`accurateEvent` and `PaperItemSpaceBigO` belong by subject in
`Model/Theorem.lean`; they are here because `Analysis/TheoremProof.lean` proves a
statement mentioning them and `Model/Theorem.lean` imports it.

## Assumptions

1. A Bernoulli(`2⁻ˡᵉᵛᵉˡ`) draw is one `RandOp.accept`, not `level` bit-reads.
   The block of `m + 1` fair bits is common randomness for Algorithm 3's
   fixed-level coupling; the price is declared at
   `Arlib.Computation.Sampler.accept`.  `Coins.flip` charges once per element of
   the sample set, not of the universe.
2. An arrival of a run that has already returned bottom costs its stop test and
   nothing more.
3. Storage is charged per sample item: one `Cell` per element.  The level counter
   and the stop flag — `O(log m)` and `O(1)` bits — are not charged, so the
   headline bounds the sample set rather than the machine.  Nor are the arrival's
   `m + 1` fresh bits or the universe-sized `retained` subset, which are the
   environment's randomness in the encoding the coupling needs; charging them
   would report `Θ(m)` per arrival and `Θ(2ⁿ)`.  No check can distinguish the
   environment's random bits from a bit array a program built for itself: the
   types are identical.
4. Loop control is free.  `Program.run` is a `Charged.foldl`, whose cost is the
   sum of its bodies' costs by definition, so the index increment, the bounds
   check and the branch are charged nothing.  `esa22CopyTime` states an exact
   number, not an asymptotic one, so it is claiming that constant is zero.
   Arlib's RAM-side `Loop.iterate` hides the same increment and compare.
5. `accurateEvent` and `PaperItemSpaceBigO` say what the paper means by a good
   answer and by its big-O sentence.  Nothing checks either against the paper.
-/

set_option autoImplicit false

namespace Esa22Copy

open Arlib.Computation

/-! ## The problem

The paper's finite universe is `Fin n`, zero-based; a length-`m` stream is
`Fin m → Fin n`.  Base-two logarithms are Mathlib's `Real.logb 2`, so the
threshold and the item charge share one convention. -/

/-- The positive universe and stream sizes and the two probabilities appearing in
the paper. -/
structure Params where
  n : Nat
  m : Nat
  hn : 0 < n
  hm : 0 < m
  eps : Real
  delta : Real
  heps : eps ∈ Set.Ioo 0 1
  hdelta : delta ∈ Set.Ioo 0 1

/-- The paper's universe `[n]`, relabelled zero-based. -/
abbrev Item (P : Params) := Fin P.n

/-- An ordered stream of exactly `m` universe elements. -/
abbrev Stream (P : Params) := Fin P.m → Item P

/-- The set of universe values occurring anywhere in the stream. -/
def distinctSet {P : Params} (A : Stream P) : Finset (Item P) :=
  Finset.univ.image A

/-- `F₀(A)`: the number of distinct universe values occurring in `A`. -/
def F0 {P : Params} (A : Stream P) : Nat :=
  (distinctSet A).card

/-- The paper's threshold `⌈(12 / eps²) log₂(8m/delta)⌉`. -/
noncomputable def threshold (P : Params) : Nat :=
  Nat.ceil ((12 / P.eps ^ 2) * Real.logb 2 (8 * (P.m : Real) / P.delta))

/-- Bits charged per stored item, under the paper's item-only accounting. -/
noncomputable def itemBits (P : Params) : Nat :=
  Nat.ceil (Real.logb 2 (P.n : Real))

/-- Every result this development takes from prior work rather than proving.

Empty: nothing has been surveyed, so the theorems assume nothing and `hprior` is
discharged by `⟨⟩`.  A borrowed result becomes a field here, so that what was
granted appears in the statement rather than in a `sorry` under it. -/
structure Prior : Prop where

/-! ## The randomness -/

/-- A block of fresh fair bits used by one arrival. -/
abbrev BitBlock (P : Params) := Fin (P.m + 1) → Bool

/-- A fresh uniform block of independent fair bits. -/
noncomputable def freshBlock (P : Params) : PMF (BitBlock P) :=
  PMF.uniformOfFintype (BitBlock P)

/-- A fresh uniform universe subset: one independent fair retain/discard choice
per element, avoiding an arbitrary enumeration of a mathematical `Finset`. -/
noncomputable def freshSubset (P : Params) : PMF (Finset (Item P)) :=
  PMF.uniformOfFintype (Finset (Item P))

/-! ## The answer and the state -/

/-- What a run returns: `none` is bottom, `some c` the estimate.

A natural number: the rate is `2⁻ˡᵉᵛᵉˡ`, so the paper's `|X| / p` is
`|X| * 2ˡᵉᵛᵉˡ`.  The comparison with `F₀` happens in the reals, in
`accurateEvent`. -/
abbrev Answer := Option Nat

/-- What the algorithm holds between arrivals, and what one arrival leaves.

The sample set is one `Roster` named once: a second field holding a sample set
would count as held twice in the space profile, and `Charged.ExactNet` would be
unprovable. -/
structure RunState (P : Params) where
  /-- The sample set. -/
  samples : Roster (Item P)
  /-- The sampler; the rate `2⁻ˡᵉᵛᵉˡ` is sealed inside it. -/
  sampler : Sampler
  /-- The answer register: nonempty once the run has returned bottom. -/
  result : Slot Answer

/-- The event that a run's answer is a successful relative approximation: a
numeric answer in Arlib's multiplicative relative-error interval around `F₀`, and
bottom is never accurate.

**Assumption 5.**  This is what the paper means by a good answer, asserted. -/
def accurateEvent (P : Params) (A : Stream P) : Set Answer :=
  {out | match out with
    | some c => (c : Real) ∈ Arlib.relErr P.eps (F0 A : Real)
    | none => False}

/-! ## The paper's displayed space bound -/

/-- The expression displayed in the paper's asymptotic item-only space claim. -/
noncomputable def paperSpaceScale (P : Params) : Real :=
  P.eps⁻¹ ^ 2 * Real.logb 2 (P.n : Real) *
    (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹)

/-- A uniform meaning for the paper's big-O sentence.  The explicit `n,m ≥ 2`
regime avoids the degenerate zero logarithms that make its displayed product
false as a pointwise bound, while retaining all `eps,delta ∈ (0,1)`. -/
def PaperItemSpaceBigO : Prop :=
  ∃ C : Real, 0 < C ∧ ∀ P : Params, 2 ≤ P.n → 2 ≤ P.m →
    ((threshold P * itemBits P : Nat) : Real) ≤ C * paperSpaceScale P

end Esa22Copy
