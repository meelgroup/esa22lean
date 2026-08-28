import Esa22Copy.Model.Run
import Esa22Copy.Interface.Encoding

/-!
# The seal, made to fail

`Model/Program.lean` runs `#programSeal` and `#driverSeal` on every build, and
they pass.  That is not evidence.  An audit that has never rejected anything is
not known to reject anything, and the two commands are exactly the kind of code
whose failure mode is silence — a filter that matches nothing reports a clean
build.

Each test below is a `#guard_msgs` block: it **passes when the checker produces
exactly the stated error**, so a future change that quietly opens one of these
routes turns this file red.  This is the same discipline as
`ArlibTest/Computation.lean` §3, applied to the checkers rather than to the
compiler.

Every cheat gets its **own namespace**.  The seal commands take the namespace to
scan as an argument, so a cheat planted in `Breach.Exchange.Program` is invisible
to the test that follows it — which keeps each expected message a single entry
and keeps the tests independent of the order they run in.  It also checks
something worth checking: that the commands are genuinely parameterized rather
than hardcoded to the development they were written for.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — `#programSeal`: the routes past the compiler, inside the algorithm —
  including the one that only a *transitive* scan catches, which is the property
  `reaches` exists for and the first test to run if it is ever touched.
* §3 — `#driverSeal`: inventing a charge, erasing a tally, and performing a line
  of the algorithm where nothing pays for it.

The positive direction is covered by the main build: `Model/Program.lean` runs
both commands over the real development and they report clean.
-/

namespace Esa22CopyTest

open Arlib.Computation Esa22Copy

/-! ## 1. What the compiler rejects on its own -/

/-! Copying a computation's result to drop its charges.  This is the cheat that
would make every bound in the development vacuous, and it does not compile,
because `Charged.val` is `noncomputable`. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.val', which is 'noncomputable'
-/
#guard_msgs in
def dropTally (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat := pure p.val

/-! Reading a dictionary's size without asking it.  `Roster.card` is the
specification's view and is `noncomputable`, so a program that wants the number
must call `Roster.size` and pay. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Roster.card', which is 'noncomputable'
-/
#guard_msgs in
def freeSize (d : Roster Nat) : Nat := d.card

/-! Forging a tally.  There is no syntax for asserting what something cost. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.Charged` is marked as private
-/
#guard_msgs in
example : Charged StdOp Cell Nat := ⟨0, 0, 1⟩

/-! ## 2. `#programSeal` — the routes past the compiler -/

/-! **Laundering a tally through a change of currency.**  `exchange` is
computable and takes a `Charged` to a `Charged`, so nothing the compiler checks
stands in the way; at a rate of zero it re-prices any computation at nothing. -/
namespace Breach.Exchange.Program
def cheat (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p
end Breach.Exchange.Program

/--
error: Seal breach in Esa22CopyTest.Breach.Exchange.Program: [(Esa22CopyTest.Breach.Exchange.Program.cheat, Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.Exchange.Program

/-! **Silencing the compiler.**  Writing `noncomputable def` turns off the half
of the seal §1 relies on.  Nothing else about this declaration is wrong, which is
the point: the marker alone is the breach. -/
namespace Breach.Noncomputable.Program
noncomputable def cheat : Real := 0
end Breach.Noncomputable.Program

/--
error: Seal breach in Esa22CopyTest.Breach.Noncomputable.Program: [(Esa22CopyTest.Breach.Noncomputable.Program.cheat, noncomputableProgram)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.Noncomputable.Program

/-! **Projecting a dictionary's contents through the eliminator.**  `casesOn` is
generated public even though the constructor is private, and it is compiled, so
this is the one route the compiler genuinely leaves open. -/
namespace Breach.CasesOn.Program
def cheat (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)
end Breach.CasesOn.Program

/--
error: Seal breach in Esa22CopyTest.Breach.CasesOn.Program: [(Esa22CopyTest.Breach.CasesOn.Program.cheat, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.CasesOn.Program

/-! **Pricing a line by hand.**  `Charged.op o a` is arlib's escape hatch — one
operation of the currency, returning a value the algorithm computed for itself —
and this development is on `forbiddenInProgram`'s side of it: every line of the
paper's pseudocode is a standard operation of the library, so no line needs it.

The cheat below is exactly what the algorithm used to do, and it is the shape to
watch for: the charge says "one coin" and the argument is an `O(level)` scan of a
bare bit block, read at a level nobody paid for.  The seal cannot see that the
argument is expensive — nothing can — so it forbids the escape hatch instead, and
the honest fix for a line that genuinely needs one is to seal what it touches and
add the operation to arlib. -/
namespace Breach.HandPriced.Program
def cheat (level : Nat) (bits : BitBlock P) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (acceptsAt level bits)
end Breach.HandPriced.Program

/--
error: Seal breach in Esa22CopyTest.Breach.HandPriced.Program: [(Esa22CopyTest.Breach.HandPriced.Program.cheat, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.HandPriced.Program

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
namespace Breach.PeekLevel.Program
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def cheat (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf
end Breach.PeekLevel.Program

/-! **Observing a computation's own tally.**  `Charged.cost` is computable and
"produces no value" — until `decide` is applied to it.  `Roster.cost_filterErase`
equates a thinning pass's tally to `d.card`, so a program that may read `cost`
has a free cardinality and therefore a free `cardEq`. -/
namespace Breach.Cost.Program
def cheat (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost
end Breach.Cost.Program

/--
error: Seal breach in Esa22CopyTest.Breach.Cost.Program: [(Esa22CopyTest.Breach.Cost.Program.cheat, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.Cost.Program

/-! **The same read, one hop away.**  `Charged.steps` is deliberately absent from
`forbiddenInProgram`: it is `CostVec.steps C p.cost`, so a blacklist of *direct*
mentions would miss it entirely.  This test is what makes the transitive walk a
checked fact rather than an intention, and it is the one to run first if
`reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change. -/
namespace Breach.Transitive.Program
def cheat (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p
end Breach.Transitive.Program

/--
error: Seal breach in Esa22CopyTest.Breach.Transitive.Program: [(Esa22CopyTest.Breach.Transitive.Program.cheat, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.Transitive.Program

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def readResidency (r : Residency Cell) : Nat := r.at' Cell.cell

/-! **Supplying your own measure.**  `opUpdate` is computable and takes the
measure as an argument, so nothing the compiler checks objects to a measure that
reports nothing — this is `Charged.exchange (fun _ => 0)` for space.  A program
calls `Roster.insert`, which passes a measure private to `Roster`. -/
namespace Breach.Measure.Program
def cheat (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d
end Breach.Measure.Program

/--
error: Seal breach in Esa22CopyTest.Breach.Measure.Program: [(Esa22CopyTest.Breach.Measure.Program.cheat, Arlib.Computation.Charged.opUpdate), (Esa22CopyTest.Breach.Measure.Program.cheat, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.Measure.Program

/-! **Reading the measured peak.**  `Charged.peakAt` is computable on purpose —
`#guard` has to read it for the protocol's execution tests — so the compiler does
not object, and the seal is what stops an algorithm from using it as a free size
query.  Same standing as `Charged.cost`. -/
namespace Breach.PeakAt.Program
def cheat (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.cell
end Breach.PeakAt.Program

/--
error: Seal breach in Esa22CopyTest.Breach.PeakAt.Program: [(Esa22CopyTest.Breach.PeakAt.Program.cheat, Arlib.Computation.Charged.peakAt)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Breach.PeakAt.Program

/-! ## 3. `#driverSeal` — creating and destroying charges outside the algorithm

The compiler has nothing to say about any of these.  A driver is noncomputable by
nature, so "not noncomputable" cannot be asked of it, and each cheat below
elaborates cleanly. -/

/-! **Inventing work the algorithm never did.**  An upper bound survives this,
but a lower bound does not, and neither does the claim that the tally counts what
the program performed. -/
namespace Breach.Invent
noncomputable def cheat (n : Nat) : Charged StdOp Cell Nat := Charged.op (StdOp.roster .erase) n
end Breach.Invent

/--
error: Seal breach in the driver: [(Esa22CopyTest.Breach.Invent.cheat, Arlib.Computation.Charged.op)].  A definition under Esa22CopyTest.Breach.Invent but outside Esa22CopyTest.Breach.Invent.Program may not create a charge or perform a dictionary operation, and may read a dictionary or a computation's value only if `Esa22Copy.Meta.driverByPermission` names it — otherwise a line of the algorithm can be performed where nothing pays for it.
-/
#guard_msgs (whitespace := lax) in
#driverSeal Esa22CopyTest.Breach.Invent.Program

/-! **Erasing a tally.**  `noncomputable` is legitimate in the driver, so the
compiler's objection from §1 does not arise here; this is the cheat the driver
seal exists for. -/
namespace Breach.Erase
noncomputable def cheat (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat := pure p.val
end Breach.Erase

/--
error: Seal breach in the driver: [(Esa22CopyTest.Breach.Erase.cheat, Arlib.Computation.Charged.val)].  A definition under Esa22CopyTest.Breach.Erase but outside Esa22CopyTest.Breach.Erase.Program may not create a charge or perform a dictionary operation, and may read a dictionary or a computation's value only if `Esa22Copy.Meta.driverByPermission` names it — otherwise a line of the algorithm can be performed where nothing pays for it.
-/
#guard_msgs (whitespace := lax) in
#driverSeal Esa22CopyTest.Breach.Erase.Program

/-! **Performing a line of the algorithm where nothing pays for it.**  This is
the shape of the defect this development shipped: a declaration that builds no
`Charged` value at all, and computes part of the answer from a free read.  It is
the reason `#driverSeal` scans by namespace rather than by type. -/
namespace Breach.FreeRead
noncomputable def cheat (d : Roster Nat) (level : Nat) : Nat := d.card * 2 ^ level
end Breach.FreeRead

/--
error: Seal breach in the driver: [(Esa22CopyTest.Breach.FreeRead.cheat, Arlib.Computation.Roster.card)].  A definition under Esa22CopyTest.Breach.FreeRead but outside Esa22CopyTest.Breach.FreeRead.Program may not create a charge or perform a dictionary operation, and may read a dictionary or a computation's value only if `Esa22Copy.Meta.driverByPermission` names it — otherwise a line of the algorithm can be performed where nothing pays for it.
-/
#guard_msgs (whitespace := lax) in
#driverSeal Esa22CopyTest.Breach.FreeRead.Program

end Esa22CopyTest
