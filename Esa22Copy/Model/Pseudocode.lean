import Esa22Copy.Model.Prelude
import Arlib.Approximation.Counting
import Mathlib.Data.Finset.Insert
import Mathlib.Probability.Distributions.Uniform

/-!
# The paper's randomized algorithms

The sampling rate is encoded by a natural level `k`, with exact value `2⁻ᵏ`.  Each
arrival draws a fresh uniform block of `m + 1` fair bits; insertion at level `k` means
that its first `k` bits are all one.  This is the finite-bit encoding used by the
paper's Algorithm 3 and exposes the common randomness needed for its fixed-level
coupling.  Reachable levels are at most `m`; `acceptsAt` deliberately returns false if
asked for more bits than the block contains.

Thinning draws a fresh uniform finite subset of the universe and intersects it with
the current sample set.  Uniform subsets are exactly independent fair retain/discard
choices, while avoiding an arbitrary enumeration of a mathematical `Finset`.

The original and relaxed transitions are both literal PMF programs built from fresh
uniform samplers, `pure`, and `bind`.  The relaxed transition omits only the bottom
check, so its sample set is intentionally not capped after an all-survive thinning.
-/

namespace Esa22Copy

/-- The explicit bottom answer is `none`; `some c` is a numeric estimate. -/
abbrev Answer := Option Real

/-- A successful numeric answer lies in Arlib's multiplicative relative-error interval. -/
def Accurate (eps truth : Real) : Answer → Prop
  | some c => c ∈ Arlib.relErr eps truth
  | none => False

/-- A block of fresh fair bits used by one arrival. -/
abbrev BitBlock (P : Params) := Fin (P.m + 1) → Bool

/-- Whether the first `k` bits of a block are all one. -/
def acceptsAt {P : Params} (k : Nat) (bits : BitBlock P) : Bool :=
  if k ≤ P.m + 1 then (List.ofFn bits).take k |>.all id else false

/-- A fresh uniform block of independent fair bits. -/
noncomputable def freshBlock (P : Params) : PMF (BitBlock P) :=
  PMF.uniformOfFintype (BitBlock P)

/-- A fresh uniform universe subset, used as independent fair thinning bits. -/
noncomputable def freshSubset (P : Params) : PMF (Finset (Item P)) :=
  PMF.uniformOfFintype (Finset (Item P))

/-- Internal state of the original algorithm; `answer = none` means that it is still running. -/
structure State (P : Params) where
  samples : Finset (Item P)
  level : Nat
  peakSamples : Nat
  answer : Option Answer

/-- The exact dyadic sampling rate represented by a state. -/
noncomputable def rate {P : Params} (s : State P) : Real :=
  (2 : Real) ^ (-(s.level : Int))

/-- The initialized state `p = 1`, `X = ∅`. -/
def initialState (P : Params) : State P where
  samples := ∅
  level := 0
  peakSamples := 0
  answer := none

/-- Erase the arriving value and freshly reinsert it exactly when its level bits are all one. -/
def refresh {P : Params} (a : Item P) (level : Nat) (bits : BitBlock P)
    (X : Finset (Item P)) : Finset (Item P) :=
  let erased := X.erase a
  if acceptsAt level bits then insert a erased else erased

/-- One line-by-line transition of the original estimator. -/
noncomputable def step (P : Params) (a : Item P) (s : State P) : PMF (State P) :=
  match s.answer with
  | some _ => pure s
  | none =>
      (freshBlock P).bind fun bits =>
        let refreshed := refresh a s.level bits s.samples
        let peak := max s.peakSamples refreshed.card
        if refreshed.card = threshold P then
          (freshSubset P).bind fun retained =>
            let thinned := refreshed ∩ retained
            pure
              { samples := thinned
                level := s.level + 1
                peakSamples := peak
                answer := if thinned.card = threshold P then some none else none }
        else
          pure
            { samples := refreshed
              level := s.level
              peakSamples := peak
              answer := none }

/-- The result payload returned by a complete randomized run. -/
structure RunOutput (P : Params) where
  answer : Answer
  peakSamples : Nat

/-- Finish a nonfailed state with the exact estimate `|X| / p`; preserve bottom on failure. -/
noncomputable def finish {P : Params} (s : State P) : RunOutput P :=
  { answer := match s.answer with
      | some answer => answer
      | none => some ((s.samples.card : Real) / rate s)
    peakSamples := s.peakSamples }

/-- Fold the original transition over all `m` arrivals, stopping probabilistically after bottom. -/
noncomputable def runState (P : Params) (A : Stream P) : PMF (State P) :=
  (List.ofFn A).foldlM (fun s a => step P a s) (initialState P)

/--
The complete estimator distribution.  Its natural component is the paper's charged
item-only storage in bits; the payload also exposes the peak sample cardinality.
-/
noncomputable def run (P : Params) (A : Stream P) : PMF (RunOutput P × Nat) :=
  (runState P A).bind fun s =>
    let output := finish s
    pure (output, output.peakSamples * itemBits P)

/-- State of Algorithm 2, which has no bottom check. -/
structure RelaxedState (P : Params) where
  samples : Finset (Item P)
  level : Nat

/-- One transition of Algorithm 2: exactly `step` with the failure test removed. -/
noncomputable def relaxedStep (P : Params) (a : Item P)
    (s : RelaxedState P) : PMF (RelaxedState P) :=
  (freshBlock P).bind fun bits =>
    let refreshed := refresh a s.level bits s.samples
    if refreshed.card = threshold P then
      (freshSubset P).bind fun retained =>
        pure { samples := refreshed ∩ retained, level := s.level + 1 }
    else
      pure { samples := refreshed, level := s.level }

/-- Algorithm 2, the literal relaxed run over the whole stream. -/
noncomputable def relaxedRun (P : Params) (A : Stream P) : PMF (RelaxedState P) :=
  (List.ofFn A).foldlM (fun s a => relaxedStep P a s) { samples := ∅, level := 0 }

/-- One table of insertion bits for every stream occurrence, used by Algorithm 3. -/
abbrev LevelCoins (P : Params) := Fin P.m → BitBlock P

/--
The fixed-level set `Y_{k,i}` from Algorithm 3.  Folding erase-then-insert is essential:
for a repeated value, membership is determined by its latest occurrence in the prefix.
-/
def levelSample {P : Params} (coins : LevelCoins P) (A : Stream P)
    (k : Nat) (i : Fin (P.m + 1)) : Finset (Item P) :=
  ((List.ofFn fun j => (A j, coins j)).take i.val).foldl
    (fun X entry => refresh entry.1 k entry.2 X) ∅

/-- The event that a completed payload is a successful relative approximation. -/
def accurateEvent (P : Params) (A : Stream P) : Set (RunOutput P) :=
  {output | Accurate P.eps (F0 A : Real) output.answer}

/-- The explicit-bottom event. -/
def failEvent (P : Params) : Set (RunOutput P) :=
  {output | output.answer = none}

/-- Error is exactly the complement of successful multiplicative accuracy. -/
def errorEvent (P : Params) (A : Stream P) : Set (RunOutput P) :=
  (accurateEvent P A)ᶜ

/-- Numeric error for Algorithm 2's final estimate (the paper's `Error₂`). -/
def relaxedErrorEvent (P : Params) (A : Stream P) : Set (RelaxedState P) :=
  {s | (s.samples.card : Real) / ((2 : Real) ^ (-(s.level : Int))) ∉
    Arlib.relErr P.eps (F0 A : Real)}

/-- Both deterministic resource claims, stated support-wise for every reachable outcome. -/
def WorstCaseSpace {P : Params} (mu : PMF (RunOutput P × Nat)) (bitsBound : Nat) : Prop :=
  ∀ outcome ∈ mu.support,
    outcome.1.peakSamples ≤ threshold P ∧ outcome.2 ≤ bitsBound

/-- The exact expression displayed in the paper's asymptotic item-only space claim. -/
noncomputable def paperSpaceScale (P : Params) : Real :=
  P.eps⁻¹ ^ 2 * Real.logb 2 (P.n : Real) *
    (Real.logb 2 (P.m : Real) + Real.logb 2 P.delta⁻¹)

/--
A precise uniform meaning of the paper's big-O sentence.  The explicit `n,m ≥ 2`
regime avoids the degenerate zero logarithms that make its displayed product false as
a pointwise bound, while retaining all `eps,delta ∈ (0,1)`.
-/
def PaperItemSpaceBigO : Prop :=
  ∃ C : Real, 0 < C ∧ ∀ P : Params, 2 ≤ P.n → 2 ≤ P.m →
    ((threshold P * itemBits P : Nat) : Real) ≤ C * paperSpaceScale P

end Esa22Copy

#modelClosure Esa22Copy.run
