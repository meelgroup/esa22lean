import Esa22Copy.Model.Run

/-!
# The encoding, reduced

The program is written against the classes of `Arlib.Computation` —
`RosterOps`, `RandOps`, `SlotOps`, `RosterCells` — rather than against the
operation names.  Every lemma here is that indirection collapsed, and every one
is `rfl`.

They are here rather than in `Model/` because none is part of what the headline
theorems *say*: a statement mentions `StdOp.roster .erase`, a proof about the
program meets `Roster.opcode StdOp .erase`, and the two are definitionally equal
without being syntactically equal, which is enough to stop `simp` and `omega`.
-/

namespace Esa22Copy

open Arlib.Computation

/-! ## The randomness, as the analysis names it -/

/-- Whether the first `k` bits of a block are all one.  This is the
Bernoulli(`2⁻ᵏ`) draw of the paper's line, in the finite-bit encoding Algorithm 3
needs; it deliberately returns false if asked for more bits than the block has. -/
def acceptsAt {P : Params} (k : Nat) (bits : BitBlock P) : Bool :=
  if k ≤ P.m + 1 then (List.ofFn bits).take k |>.all id else false

/-- INTERNAL: the instance's kind, reduced.  Without this the space theorems
state `Roster.cell (Item P)` while the bounds state `Cell.cell`; the two are
definitionally equal and syntactically are not, which is enough to stop `simp`
and `omega`. -/
theorem cell_item (P : Params) : Roster.cell (Item P) = Cell.cell := rfl
/-! INTERNAL: the opcode instances, reduced.  Same role as `cell_item`: the cost
theorems meet `Roster.opcode StdOp o` where the bounds state `StdOp.roster o`,
and definitional equality is not enough to move `simp`.

There were eleven of these, one per operation, because the currency was this
development's and the instances were translation tables.  The currency is now
`Arlib.Computation.StdOp` and the instances are injections, so one lemma per
class suffices. -/

@[simp] theorem opcode_roster (o : RosterOp) : Roster.opcode StdOp o = StdOp.roster o := rfl
@[simp] theorem randOpcode_rand (o : RandOp) : randOpcode StdOp o = StdOp.rand o := rfl
@[simp] theorem slotOpcode_slot (o : SlotOp) : slotOpcode StdOp o = StdOp.slot o := rfl

/-- **A sampler's draw against a sealed block is the paper's `acceptsAt`.** -/
@[simp] theorem val_accept_ofFun {P : Params} (bits : BitBlock P) (s : Sampler) :
    (Sampler.accept (κ := StdOp) (κₛ := Cell) (Block.ofFun bits) s).val
      = acceptsAt s.levelOf bits := rfl

/-- **A flip of a sealed coin family is membership of the retained set.** -/
@[simp] theorem val_flip_ofFinset {P : Params} (retained : Finset (Item P)) (x : Item P) :
    (Coins.flip (κ := StdOp) (κₛ := Cell) x (Coins.ofFinset retained)).val
      = decide (x ∈ retained) := rfl

/-! ## Reading an execution

`RunState` holds a `Sampler` and a `Slot`; the level is inside the sampler and
the answer is inside the register.  These are the accessors the analysis states
its invariants over, and neither is mentioned by any headline statement.

Both are **specification-only** — they read a sealed carrier for free, which is
right for an invariant and wrong for a line of the algorithm.
`Esa22Copy.Meta.driverByPermission` names each as the one declaration entitled to
its read, and `#driverSeal` at the bottom of `Model/Theorem.lean` is what checks
that nothing else makes one. -/

/-- The level a run is at.  Specification-only: it is a view of a sealed sampler,
which is what forces the two places that used to read a `level` field — the
Bernoulli draw and the final scaling — to be operations the program pays for. -/
noncomputable def RunState.level {P : Params} (e : RunState P) : Nat := e.sampler.levelOf

/-- The answer a run has recorded, if any.  Specification-only. -/
noncomputable def RunState.answer {P : Params} (e : RunState P) : Option Answer := e.result.get

@[simp] theorem RunState.level_initial (P : Params) : (Program.initialState P).level = 0 := rfl

@[simp] theorem RunState.answer_initial (P : Params) :
    (Program.initialState P).answer = none := rfl

/-! ## The run, before the report

`estimator` draws the tape, folds the arrivals and binds the report in one
expression.  Every proof about it splits at the same seam — after the last
arrival, before the answer is read — because that is where the pseudocode's
`runState` lives and where both resource bounds are about the fold rather than
the report.  `execRunState` names that seam.

It is here rather than in `Model/` because no headline statement mentions it:
`estimator` is the object the three operators are applied to, and this is a view
of it that only the proofs take. -/

/-- The estimator's state marginal: the program, run on a drawn tape. -/
noncomputable def execRunState (P : Params) (A : Stream P) :
    PMF (Charged StdOp Cell (RunState P)) :=
  (freshTape P P.m).map (Program.run (threshold P) A)

/-- INTERNAL: `estimator` is the report bound onto `execRunState`. -/
theorem estimator_eq (P : Params) (A : Stream P) :
    estimator P A = (execRunState P A).map fun ce =>
      ce >>= fun e =>
        (fun answer => (answer, 0))
          <$> Program.report e.sampler e.result e.samples := rfl

end Esa22Copy
