import Esa22Copy.Model.Prelude
import Esa22Copy.Meta.CostSeal

/-!
# The paper's estimator, as a program

Algorithm 1, written in `Arlib.Computation.Charged` over the sealed carriers
`Roster`, `Block`, `Coins`, `Sampler` and `Slot`.  Every operation's price is
fixed in arlib; the assumptions behind those prices are listed in
`Model/Prelude.lean`.  Time and space are `Arlib.Computation.worstSteps` and
`worstSpace` applied to the program below.

The randomised run over a stream is `Model/Run.lean`.

Three checks run at the bottom on every build: `#programSeal` (nothing here reads
a dictionary for free, calls `Charged.op`, or is `noncomputable`),
`#executableModule` (nothing here is `noncomputable` or a specification), and
`#surplusIn` (nothing here is unreachable from `run` or `report`).
-/

set_option autoImplicit false

namespace Esa22Copy.Program

open Arlib.Computation

variable {P : Params}

/-- One cell of the randomness tape: the entropy one arrival consumes.

It carries no stream item.  The stream is the algorithm's input and the tape is
a separate source it reads from, so nothing has to pair them before the algorithm
sees either; one block and one coin family per arrival is this algorithm's own
consumption rate. -/
structure Randomness (P : Params) where
  /-- The `m + 1` fair bits this arrival's insertion coin reads. -/
  bits : Block (P.m + 1)
  /-- One retain/discard coin per universe element, for this arrival's thinning. -/
  coins : Coins (Item P)

/-- The initial state: empty sample, rate one, empty register. -/
def initialState (P : Params) : RunState P where
  samples := Roster.empty
  sampler := Sampler.start
  result := Slot.empty

/-- Erase the arriving value, flip the insertion coin, reinsert when it accepts. -/
def arrival (s : Sampler) (b : Block (P.m + 1)) (a : Item P) (d : Roster (Item P)) :
    Charged StdOp Cell (Roster (Item P)) := do
  let erased ← Roster.erase a d
  let accept ← Sampler.accept b s
  if accept then Roster.insert a erased else pure erased

/-- One retain/discard coin per element of the sample set, and one deletion per
element the coin discards.

The count of deletions is not written here: `Roster.filterErase` folds over the
elements and `Roster.cost_filterErase_card` reads the count off the fold. -/
def thin (coins : Coins (Item P)) (d : Roster (Item P)) : Charged StdOp Cell (Roster (Item P)) :=
  Roster.filterErase (fun x => Coins.flip x coins) d

/-- One arrival, from a still-running state. -/
def step (thr : Nat) (a : Item P) (s : Sampler) (b : Block (P.m + 1))
    (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    Charged StdOp Cell (RunState P) := do
  let refreshed ← arrival s b a d
  let full ← Roster.cardEq thr refreshed
  if full then
    let thinned ← thin coins refreshed
    let halved ← Sampler.halve s
    let stillFull ← Roster.cardEq thr thinned
    let recorded ← if stillFull then Slot.fill none res else pure res
    pure ⟨thinned, halved, recorded⟩
  else
    pure ⟨refreshed, s, res⟩

/-- One arrival, complete: test whether the run is still going, then act.

The stop test is an operation and is charged; a run that has already returned
bottom performs exactly this one operation per remaining arrival.  It is here
rather than in the driver because `#driverSeal` forbids anything outside this
namespace from mentioning an operation that creates or destroys a charge. -/
def arrivalStep (thr : Nat) (a : Item P) (s : Sampler) (b : Block (P.m + 1))
    (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    Charged StdOp Cell (RunState P) := do
  let running ← Slot.isEmpty res
  if running then step thr a s b coins res d
  else pure ⟨d, s, res⟩

/-- **Algorithm 1**: process the stream in order, threading the state, reading
one cell of the tape per arrival.

Read `Charged.foldl` as `for (a, r) in stream.zip tape do st := arrivalStep … st a r`.
It has two equations, both `rfl`: the empty list is the starting state at no
cost, and a cons runs the body and then the rest, adding the tallies and
composing the profiles.  A run's cost is therefore the sum of its arrivals'
costs by definition.

The stream and the tape are separate parameters and the algorithm is what pairs
them.  A tape shorter than the stream stops the run early, since `List.zip`
truncates.

The loop charges nothing for its own control — assumption 4 in
`Model/Prelude.lean`. -/
def run (thr : Nat) (A : Stream P) (tape : List (Randomness P)) :
    Charged StdOp Cell (RunState P) :=
  Charged.foldl
    (fun st ar => arrivalStep thr ar.1 st.sampler ar.2.bits ar.2.coins st.result st.samples)
    ((List.ofFn A).zip tape) (initialState P)

/-- The paper's last line, `return |X| / p`.

Asking the sample set its size is a `sizeQuery`; the rate is `2⁻ˡᵉᵛᵉˡ`, so
`|X| / p` is `|X| * 2 ^ level`, a natural number.  A run that has already
returned bottom tests, pays for the test, and reports bottom.

The answer is produced here rather than by a caller, so the last line is charged
like the rest. -/
def report (s : Sampler) (res : Slot Answer) (d : Roster (Item P)) :
    Charged StdOp Cell Answer := do
  let running ← Slot.isEmpty res
  if running then
    let n ← Roster.size d
    let estimate ← Sampler.inflate n s
    pure (some estimate)
  else pure none

end Esa22Copy.Program

#programSeal Esa22Copy.Program
#executableModule Esa22Copy.Model.Program
#surplusIn Esa22Copy.Model.Program from Esa22Copy.Program.run Esa22Copy.Program.report
