import Esa22Copy.Interface.Encoding

/-!
# The mathematical model of the estimator

`Model/Program.lean` is the algorithm: one arrival written as a program over a
sealed dictionary, with running time read off it.  This module is the *model* the
accuracy proof is carried out in — the same transition written directly on a
mathematical `Finset`, where `Finset.card`, `Finset.inter` and the whole Mathlib
API are available and nothing has to be paid for.

`Interface/ProgramModel.lean` proves the two agree, as an equality of
distributions.  That is what lets every result below transfer to the algorithm.

## Why there are two definitions and not one

Not computability.  Everything on both sides is already `noncomputable` — a `PMF`
is — so "the proof side may use noncomputable functions" is not what separates
them.  A theorem may mention `Roster.toFinset` freely; only a *program* may not.

The separation is about the sample set's type, and there are two reasons.

**A `Roster` is not extensional.**  It holds a duplicate-free list, because a
`Finset` cannot be iterated and thinning *is* an iteration over the sample — one
coin per element, one deletion per element discarded — which is the cost worth
getting right.  So a dictionary carries an order, and two dictionaries holding
the same set but reached by different histories are different terms.  The
accuracy proof is a chain of distributional arguments — couplings between
Algorithm 1, Algorithm 2 and Algorithm 3, each comparing the *law* of a sample
set.  Over `Roster` those would be laws over ordered lists, which differ even where
the set laws agree.  `Finset` is the quotient those arguments need.

**Most of the analysis is about processes that are not the algorithm.**
Algorithm 2 (`relaxedStep`, `relaxedRun`) and Algorithm 3 (`levelSample`,
`LevelCoins`) are proof devices with no counterpart in the estimator — they
appear in roughly thirty of the analysis modules.  They have no cost to state and
nothing to seal, so a sealed dictionary would buy them nothing and cost them the
whole `Finset` API.

What this does *not* rest on is `Roster`'s representation being forced.  A
`Finset`-backed sealed dictionary would be extensional and would still compile,
since `Finset.fold` does; it would, however, oblige every charged fold to prove
its step commutative, which rules out the order-dependent operations a real
dictionary performs.  The list is the more honest model of a data structure, and
the price is this module.

## What keeps the two in step

`Interface/ProgramModel.lean` proves them equal as distributions, per arrival
(`freshCell_toState`) and over the whole run (`estimatorOutput_eq`).  The whole
development crosses between them in exactly one place, a single rewrite in
`Analysis/TheoremProof.lean`; the running-time proof never crosses at all.

The equality is what makes the duplication safe rather than merely tidy.  A
program cannot understate its cost without doing less work, and doing less work
changes the state it produces, which breaks `freshCell_toState`.  The asymmetry is the
right way round: work whose result is discarded would be *over*-charged, and an
upper bound survives that.
-/

namespace Esa22Copy

/-- Internal state of the original algorithm; `answer = none` means that it is
still running.

The `peakSamples` field is gone.  It was the model's copy of the program's
hand-maintained space meter, and its only job was to be equal to it: the bridge
pinned the two together, so a wrong peak that was wrong in both places was
invisible.  Space is now read off the program's own profile. -/
structure State (P : Params) where
  samples : Finset (Item P)
  level : Nat
  answer : Option Answer

/-- The exact dyadic sampling rate represented by a state. -/
noncomputable def rate {P : Params} (s : State P) : Real :=
  (2 : Real) ^ (-(s.level : Int))

/-- The initialized state `p = 1`, `X = ∅`. -/
def initialState (P : Params) : State P where
  samples := ∅
  level := 0
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
        if refreshed.card = threshold P then
          (freshSubset P).bind fun retained =>
            let thinned := refreshed ∩ retained
            pure
              { samples := thinned
                level := s.level + 1
                answer := if thinned.card = threshold P then some none else none }
        else
          pure
            { samples := refreshed
              level := s.level
              answer := none }

/-- Finish a nonfailed state with the exact estimate `|X| / p`; preserve bottom on
failure.

The register is tested rather than read: the algorithm only ever records bottom,
so a full register *is* bottom, and `Program.report` decides the same way without
having to open it. -/
def finish {P : Params} (s : State P) : Answer :=
  if s.answer.isSome then none else some (s.samples.card * 2 ^ s.level)

/-- Fold the original transition over all `m` arrivals, stopping probabilistically after bottom. -/
noncomputable def runState (P : Params) (A : Stream P) : PMF (State P) :=
  (List.ofFn A).foldlM (fun s a => step P a s) (initialState P)

/--
The complete estimator distribution.

The trailing `0` is `Arlib.Approximation.outProbR`'s cost slot, and this
development deliberately puts nothing in it — see `Model/Program.lean`'s
`estimator`.  It used to hold the peak sample cardinality times `itemBits P`, a
number this model maintained by hand alongside the one the program maintained by
hand, with the bridge pinning the two to each other rather than to anything the
algorithm did.
-/
noncomputable def run (P : Params) (A : Stream P) : PMF (Answer × Nat) :=
  (runState P A).bind fun s => pure (finish s, 0)

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

/-- Numeric error for Algorithm 2's final estimate (the paper's `Error₂`). -/
def relaxedErrorEvent (P : Params) (A : Stream P) : Set (RelaxedState P) :=
  {s | (s.samples.card : Real) / ((2 : Real) ^ (-(s.level : Int))) ∉
    Arlib.relErr P.eps (F0 A : Real)}

/-! ## Specification vocabulary the analysis quantifies over

None of these is mentioned by a headline statement — `esa22Copy` names
`accurateEvent` and nothing else — so they are here rather than in `Model/`,
where their presence would widen the audited surface without widening the claim.
-/

/-- Values occurring in the first `i` processed positions, where `i` ranges from `0` to `m`. -/
def prefixDistinct {P : Params} (A : Stream P) (i : Fin (P.m + 1)) : Finset (Item P) :=
  (Finset.univ.filter fun j : Fin P.m => j.val < i.val).image A

/-- The explicit-bottom event. -/
def failEvent (P : Params) : Set Answer :=
  {out | out = none}

/-- Error is exactly the complement of successful multiplicative accuracy. -/
def errorEvent (P : Params) (A : Stream P) : Set Answer :=
  (accurateEvent P A)ᶜ

/-- **The integer estimate is the paper's real one.**  The sampling rate is
`2⁻ˡᵉᵛᵉˡ`, so dividing by it is multiplying by `2ˡᵉᵛᵉˡ`; the cast is the only
thing between what the algorithm computes and what accuracy compares against. -/
theorem cast_scaled (n level : Nat) :
    ((n * 2 ^ level : Nat) : Real) = (n : Real) / (2 : Real) ^ (-(level : Int)) := by
  rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
  push_cast
  ring

end Esa22Copy
