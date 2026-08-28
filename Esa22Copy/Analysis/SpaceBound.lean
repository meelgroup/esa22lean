import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.RunPeak
import Arlib.Computation.ChargedPMF

/-!
# The space bound, read off the program

The paper's only complexity claim is worst-case space, and until now it was the
one claim in this development resting on a number its author supplied: `Exec`
carried a `peakSamples` field, `advance` updated it by hand, and the headline
bounded it.  The model carried a second copy and the bridge pinned the two to
each other, so a peak that was wrong in both places was invisible.

Both fields are gone.  What is bounded here is `Charged.space` — an operator
applied to the same `estimator` that `worstSteps` is applied to, computed by the
elaborator from the sequence of dictionary operations the program performs.
There is nowhere in `Model/Program.lean` to write what a line occupies.

## The shape of the argument

Space is not a sum, so this is not the time proof with different numerals.  A
tally adds along `bind`; a residency profile composes as
`(net₁, peak₁) ⋆ (net₂, peak₂) = (net₁ + net₂, max peak₁ (net₁ + peak₂))`, and a
bound on the whole is not a function of bounds on the parts.

What bounds CVM is an *invariant*: the arrival compares the sample against the
threshold and thins when it reaches it, so the residency after every arrival is
at most `threshold P`.  `Arlib.Computation.Profile.peak_foldProfiles_le` is the
combinator that turns that into a bound, and its hypothesis is the honest one —
**from a state below the ceiling, an arrival's excursion is at most the
headroom**.  The stream length does not appear in the conclusion, which is what a
streaming algorithm's space claim says and what no `+`-based accounting can
state.

Here the invariant is carried support-wise over the `PMF` fold, in the same
shape as `Analysis/TimeBound.lean`'s, because `execRunState` is a `foldlM` over a
distribution rather than a deterministic loop.

## What is asserted rather than proved

* One cell per sample item; `Arlib.Computation.Roster`'s `slots` is the assertion,
  and its `space_net_*` theorems tie each operation's residency change to the
  `Finset` view, so a measure reporting nothing falsifies them.
* The level counter and the stop flag are not counted, per the paper's item-only
  accounting; `Cell` has one constructor and its docstring records the
  omission.
* The arrival's fresh bits and the universe-sized `retained` subset are the
  environment's randomness in the encoding the coupling proof needs, not storage.

See `docs/dev/Space-Modelling-Design.md`.
-/

namespace Esa22Copy

open Arlib.Computation

variable {P : Params}

/-! ## What one line of the algorithm does to what is held -/

/-- **The arrival line's net is exactly the change in the sample set.**

Not a claim about the line: it erases and conditionally reinserts, both are
`opUpdate`s on the dictionary it was handed, and `Profile`'s composition adds
their nets.  `Roster`'s `space_net_erase` and `space_net_insert` state each one
against the `Finset` view, so what is being added up is visible without
mentioning a representation. -/
@[simp] theorem net_arrival (s : Sampler) (bits : BitBlock P) (a : Item P)
    (d : Roster (Item P)) :
    (Program.arrival s (Block.ofFun bits) a d).space.net Cell.cell
      = ((refresh a s.levelOf bits d.toFinset).card : ℤ) - (d.toFinset.card : ℤ) := by
  by_cases h : acceptsAt s.levelOf bits <;>
    simp [Program.arrival, h, refresh, Roster.toFinset_erase] <;> omega

/-- **The arrival line rises by at most one cell.**

The erase gives back a cell or none, the insert takes one or none, and
`Profile`'s composition takes the higher of the two excursions — so on a value
already present the erase pays for the insert and the peak is zero.  None of
those three numbers is written here. -/
theorem peak_arrival_le (s : Sampler) (bits : BitBlock P) (a : Item P)
    (d : Roster (Item P)) :
    (Program.arrival s (Block.ofFun bits) a d).space.peak Cell.cell ≤ 1 := by
  have herase : (Roster.erase (κ := StdOp) a d).space.net
      Cell.cell ≤ 0 := by
    have h := (Roster.erase (κ := StdOp) a d).space.net_le_peak
      Cell.cell
    rwa [Roster.space_peak_erase] at h
  by_cases h : acceptsAt s.levelOf bits
  · have hins := Roster.space_peak_insert_le (κ := StdOp) a
      ((Roster.erase (κ := StdOp) a d).val) Cell.cell
    simp only [Program.arrival, val_accept_ofFun, h, if_pos, Charged.space_bind,
      Sampler.space_accept, Profile.peak_mul, Profile.peak_one,
      Profile.net_one, one_mul, zero_add, Roster.space_peak_erase] at herase ⊢
    exact max_le (by omega) (by omega)
  · simp only [Program.arrival, val_accept_ofFun, h, Bool.false_eq_true, if_neg,
      not_false_eq_true, Charged.space_bind, Sampler.space_accept, Charged.space_pure,
      Profile.peak_mul, Profile.peak_one, Profile.net_one,
      one_mul, mul_one, add_zero, Roster.space_peak_erase]
    omega

/-- **The thinning line never rises.**

A pass that only deletes cannot raise a run's high-water mark, however many
elements it visits.  This is the fact a constant space bound over an unbounded
stream rests on, and it has no counterpart on the time side: a pass that visits
`n` elements costs `n` however little it keeps. -/
@[simp] theorem peak_thin (coins : Coins (Item P)) (d : Roster (Item P)) :
    (Program.thin coins d).space.peak Cell.cell = 0 := by
  rw [Program.thin]
  exact Roster.space_peak_filterErase _ (fun _ _ => by simp) d _

/-- **And it gives back a cell for each element it discards.** -/
theorem net_thin_nonpos (coins : Coins (Item P)) (d : Roster (Item P)) :
    (Program.thin coins d).space.net Cell.cell ≤ 0 := by
  have h := (Program.thin coins d).space.net_le_peak Cell.cell
  rwa [peak_thin] at h

end Esa22Copy

namespace Esa22Copy

open Arlib.Computation

variable {P : Params}

/-! ## One arrival -/

/-- INTERNAL: the threshold test, in the terms the model states it in. -/
private theorem card_arrival_eq_iff (thr : Nat) (a : Item P) (s : Sampler)
    (bits : BitBlock P) (d : Roster (Item P)) :
    (Program.arrival s (Block.ofFun bits) a d).val.card = thr
      ↔ (refresh a s.levelOf bits d.toFinset).card = thr := by
  rw [card_arrival]

/-- INTERNAL: the thinning line is exact — its net is what it gave back. -/
private theorem net_thin (coins : Coins (Item P)) (x : Roster (Item P)) :
    (Program.thin coins x).space.net Cell.cell
      = (((Program.thin coins x).val).card : ℤ) - (x.card : ℤ) :=
  Roster.space_net_filterErase _ (fun _ => by simp) x _

/-- **An arrival's net is the change in its sample set.**

The arrival line and the thinning line telescope: whatever the first added, the
second gives back part of, and the sum is what the arrival leaves minus what it
was handed.  Neither summand is a number written here — the first is
`Roster.space_net_erase` and `space_net_insert`, the second is read off the
`filterErase` fold. -/
theorem net_step (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    (Program.step thr a s (Block.ofFun bits) coins res d).space.net Cell.cell
      = (((Program.step thr a s (Block.ofFun bits) coins res d).val.samples).card : ℤ)
          - (d.card : ℤ) := by
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr
  · have h0 : (Program.arrival s (Block.ofFun bits) a d).val.card = thr :=
      (card_arrival_eq_iff thr a s bits d).2 h
    simp [Program.step, h, h0, net_arrival, net_thin, Roster.card_toFinset,
      apply_ite (Charged.space (κ := StdOp) (κₛ := Cell)),
      apply_ite (Charged.val (κ := StdOp) (κₛ := Cell)),
      apply_ite RunState.samples]
  · have h0 : ¬(Program.arrival s (Block.ofFun bits) a d).val.card = thr := fun hc =>
      h ((card_arrival_eq_iff thr a s bits d).1 hc)
    simp [Program.step, h, h0, net_arrival, net_thin, card_arrival, Roster.card_toFinset]

/-- **An arrival rises by at most one cell, or by what the arrival line added.**

Both halves matter.  The `1` is what a fresh insertion takes; the second is what
the sample grew to.  **The thinning line contributes nothing**, because
`peak_thin` is zero — so a run's high-water mark is set by the arrival line
alone, and the pass that visits every element is free of it.  That is the
asymmetry with time, where the same pass costs one operation per element. -/
theorem peak_step_le (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    (Program.step thr a s (Block.ofFun bits) coins res d).space.peak Cell.cell
      ≤ max 1 (((refresh a s.levelOf bits d.toFinset).card : ℤ) - (d.toFinset.card : ℤ)) := by
  have hpa := peak_arrival_le (P := P) s bits a d
  have hna := net_arrival (P := P) s bits a d
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr
  · have h0 : (Program.arrival s (Block.ofFun bits) a d).val.card = thr :=
      (card_arrival_eq_iff thr a s bits d).2 h
    simp [Program.step, h, h0, peak_thin, card_arrival,
      apply_ite (Charged.space (κ := StdOp) (κₛ := Cell))]
    omega
  · have h0 : ¬(Program.arrival s (Block.ofFun bits) a d).val.card = thr := fun hc =>
      h ((card_arrival_eq_iff thr a s bits d).1 hc)
    simp [Program.step, h, h0, card_arrival]
    omega

end Esa22Copy

namespace Esa22Copy

open Arlib.Computation

variable {P : Params}

/-! ## The whole arrival, and the run -/

/-- **A stopped run holds still.**  It performs its stop test, discovers it has
answered, and touches nothing — so it contributes nothing to the peak, however
long the stream continues after it. -/
theorem space_arrivalStep_stopped (P : Params) (a : Item P) (e : RunState P) (bits : BitBlock P)
    (retained : Finset (Item P)) (ans : Answer) (h : e.answer = some ans) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
      (Coins.ofFinset retained) e.result e.samples).space = 1 := by
  rw [Program.arrivalStep]
  simp [Slot.val_isEmpty, show e.result.get = some ans from h]

/-- **An arrival's net is the change in what it holds.**  This is
`Charged.ExactNet` for one step of the run, and it is what lets the accumulated
net of a fold be read as the residency of the state it has reached. -/
theorem net_arrivalStep (P : Params) (a : Item P) (e : RunState P) (bits : BitBlock P)
    (retained : Finset (Item P)) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).space.net Cell.cell
      = (((Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).val.samples).card : ℤ) - (e.samples.card : ℤ) := by
  cases h : e.answer with
  | some ans =>
      rw [space_arrivalStep_stopped P a e bits retained ans h]
      rw [Program.arrivalStep]
      simp [Slot.val_isEmpty, show e.result.get = some ans from h]
  | none =>
      rw [Program.arrivalStep]
      simp only [Slot.val_isEmpty, show e.result.get = none from h, Option.isNone_none,
        Charged.space_bind, Charged.val_bind, Slot.space_isEmpty, one_mul, if_pos]
      simpa using net_step (threshold P) a e.sampler bits (Coins.ofFinset retained)
        e.result e.samples

/-- **From a state below the ceiling, an arrival's excursion is at most the
headroom.**

This is the hypothesis `Arlib.Computation.Profile.peak_foldProfiles_le` asks for,
and it is where the algorithm's own threshold test does the work: a running state
holds strictly fewer than `threshold P` items, an arrival adds at most one, and
the thinning line contributes nothing to the peak. -/
theorem peak_arrivalStep_le (P : Params) (a : Item P) (e : RunState P) (bits : BitBlock P)
    (retained : Finset (Item P)) (hcard : e.samples.card ≤ threshold P)
    (hrun : e.answer = none → e.samples.card < threshold P) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).space.peak Cell.cell
      ≤ (threshold P : ℤ) - (e.samples.card : ℤ) := by
  cases h : e.answer with
  | some ans =>
      rw [space_arrivalStep_stopped P a e bits retained ans h]
      simp only [Profile.peak_one]
      omega
  | none =>
      have hlt := hrun h
      have hgrow := refresh_card_le_succ a e.level bits e.samples.toFinset
      have hcardF : e.samples.toFinset.card = e.samples.card := Roster.card_toFinset _
      rw [Program.arrivalStep]
      simp only [Slot.val_isEmpty, show e.result.get = none from h, Option.isNone_none,
        Charged.space_bind, Slot.space_isEmpty, if_pos, Profile.peak_mul, Profile.net_mul,
        Profile.peak_one, Profile.net_one, one_mul, zero_add, max_self, Charged.val_bind]
      have := peak_step_le (threshold P) a e.sampler bits (Coins.ofFinset retained)
        e.result e.samples
      have hmax : max (1 : ℤ)
          (((refresh a e.level bits e.samples.toFinset).card : ℤ)
            - (e.samples.toFinset.card : ℤ)) ≤ (threshold P : ℤ) - (e.samples.card : ℤ) := by
        refine max_le ?_ ?_ <;> omega
      simp only [RunState.level] at this hgrow ⊢
      omega

end Esa22Copy

namespace Esa22Copy

open Arlib.Computation

variable {P : Params}

/-! ## The run -/

/-- INTERNAL: a drawn tape cell is the sealed form of some bits and some retained
set.  This is what lets the lemmas above, stated over `Block.ofFun` and
`Coins.ofFinset`, apply to whatever the distributions produced. -/
theorem sealed_of_mem_freshCell (P : Params) (r : Program.Randomness P)
    (h : r ∈ (freshCell P).support) :
    ∃ (bits : BitBlock P) (retained : Finset (Item P)),
      r = ⟨Block.ofFun bits, Coins.ofFinset retained⟩ := by
  rw [freshCell, PMF.mem_support_bind_iff] at h
  obtain ⟨bits, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨retained, _, rfl⟩ := h
  exact ⟨bits, retained, rfl⟩

/-- INTERNAL: one arrival of the loop, from a state satisfying the model's
invariant: its net is the change in what is held, its peak is within the
headroom, and it leaves a state satisfying the invariant again. -/
theorem foldBody_space (P : Params) (a : Item P) (b : RunState P)
    (r : Program.Randomness P) (hr : r ∈ (freshCell P).support)
    (hb : StateSpaceInvariant P b.toState) :
    (Program.arrivalStep (threshold P) a b.sampler r.bits r.coins
        b.result b.samples).space.net Cell.cell
      = ((Program.arrivalStep (threshold P) a b.sampler r.bits r.coins
          b.result b.samples).val.samples.card : ℤ) - (b.samples.card : ℤ)
    ∧ (Program.arrivalStep (threshold P) a b.sampler r.bits r.coins
        b.result b.samples).space.peak Cell.cell
      ≤ (threshold P : ℤ) - (b.samples.card : ℤ)
    ∧ StateSpaceInvariant P (Program.arrivalStep (threshold P) a b.sampler r.bits
        r.coins b.result b.samples).val.toState := by
  obtain ⟨bits, retained, rfl⟩ := sealed_of_mem_freshCell P r hr
  have hcard : b.samples.card ≤ threshold P := by
    have h1 := hb.1
    rwa [RunState.toState_samples, Roster.card_toFinset] at h1
  have hrunning : b.answer = none → b.samples.card < threshold P := by
    intro hn
    have h2 := hb.2 (by rw [RunState.toState_answer]; exact hn)
    rwa [RunState.toState_samples, Roster.card_toFinset] at h2
  refine ⟨net_arrivalStep P a b bits retained,
    peak_arrivalStep_le P a b bits retained hcard hrunning, ?_⟩
  refine step_preserves_space P a hb ?_
  rw [← freshCell_toState P a b]
  exact (PMF.mem_support_map_iff _ _ _).2 ⟨_, hr, rfl⟩

/-- **Every reachable run holds at most `threshold P` items at its highest
point.**

The induction is over the stream and the tape together.  The peak clause is the
one that is not bookkeeping: `Profile`'s composition gives `max (peak of this
arrival) (its net + peak of the rest)`, the first is the headroom by
`peak_arrivalStep_le` and the second is `residency + headroom` from the state it
leaves.  Neither is a sum, and no arithmetic on totals would give it. -/
theorem foldl_space_le (P : Params) :
    ∀ (l : List (Item P)) (tape : List (Program.Randomness P)) (b : RunState P),
      tape ∈ (freshTape P l.length).support →
      StateSpaceInvariant P b.toState →
      (Charged.foldl (fun st ar => Program.arrivalStep (threshold P) ar.1 st.sampler
          ar.2.bits ar.2.coins st.result st.samples) (l.zip tape) b).space.peak Cell.cell
        ≤ (threshold P : ℤ) - (b.samples.card : ℤ)
      ∧ (Charged.foldl (fun st ar => Program.arrivalStep (threshold P) ar.1 st.sampler
          ar.2.bits ar.2.coins st.result st.samples) (l.zip tape) b).space.net Cell.cell
        = ((Charged.foldl (fun st ar => Program.arrivalStep (threshold P) ar.1 st.sampler
            ar.2.bits ar.2.coins st.result st.samples) (l.zip tape) b).val.samples.card : ℤ)
          - (b.samples.card : ℤ) := by
  intro l
  induction l with
  | nil =>
      intro tape b _ hb
      have hcard : b.samples.card ≤ threshold P := by
        have h1 := hb.1
        rwa [RunState.toState_samples, Roster.card_toFinset] at h1
      refine ⟨by simp; omega, by simp⟩
  | cons a l ih =>
      intro tape b htape hb
      rw [List.length_cons, freshTape, PMF.mem_support_bind_iff] at htape
      obtain ⟨r, hr, htape⟩ := htape
      rw [PMF.mem_support_map_iff] at htape
      obtain ⟨tape', htape', rfl⟩ := htape
      obtain ⟨hnet, hpeak, hinv⟩ := foldBody_space P a b r hr hb
      obtain ⟨hpeak', hnet'⟩ := ih tape' _ htape' hinv
      rw [List.zip_cons_cons]
      refine ⟨?_, ?_⟩
      · simp only [Charged.space_foldl_cons, Profile.peak_mul]
        exact max_le hpeak (by omega)
      · simp only [Charged.space_foldl_cons, Profile.net_mul, Charged.val_foldl_cons]
        omega

/-- The bound, as a statement about the estimator's own state distribution. -/
theorem execRunState_space_le (P : Params) (A : Stream P)
    (ce : Charged StdOp Cell (RunState P)) (hce : ce ∈ (execRunState P A).support) :
    ce.space.peak Cell.cell ≤ (threshold P : ℤ) := by
  rw [execRunState, PMF.mem_support_map_iff] at hce
  obtain ⟨tape, htape, rfl⟩ := hce
  have hinit : StateSpaceInvariant P (Program.initialState P).toState := by
    rw [toState_initialState]
    exact ⟨Nat.zero_le _, fun _ => threshold_pos P⟩
  have h := (foldl_space_le P (List.ofFn A) tape (Program.initialState P)
    (by rwa [List.length_ofFn]) hinit).1
  rw [Program.run]
  simpa [Program.initialState] using h

/-- INTERNAL: the final report holds nothing new.  It asks the sample set for its
size and scales the answer, and a query is work but not storage. -/
@[simp] theorem space_report (s : Sampler) (res : Slot Answer) (d : Roster (Item P)) :
    (Program.report (P := P) s res d).space = 1 := by
  rw [Program.report]
  cases hres : res.get <;> simp [Slot.val_isEmpty, hres]

/--
**PAPER: esa22-final.tex:507-508 — the estimator's worst-case space.**

Every reachable run of the estimator holds at most `threshold P` sample items at
its highest point, counted in cells of `Cell.cell`.

The quantity bounded is `Arlib.Computation.worstSpace` applied to `estimator` —
the supremum, over the runs that can happen, of what the run's own
`Charged.space` profile says it held.  That profile is computed by the elaborator
from the sequence of dictionary operations the program performs; there is
nowhere in `Model/Program.lean` to write what a line occupies, and the `Roster`
operations' `space_net_*` theorems tie each one to the `Finset` view.

It is the *same* `estimator` that `esa22CopyTime` bounds the running time of and
that the accuracy clause is about — three operators, one object.
-/
theorem estimator_worstSpace_le (P : Params) (A : Stream P) :
    worstSpace Cell.cell 0 (estimator P A) ≤ ((threshold P : ℕ) : ℕ∞) := by
  refine worstSpace_le _ _ _ _ ?_
  intro p hp
  rw [estimator_eq, PMF.mem_support_map_iff] at hp
  obtain ⟨ce, hce, rfl⟩ := hp
  have hinv := execRunState_space_le P A ce hce
  have hspace : (ce >>= fun e =>
      (fun answer => (answer, 0))
        <$> Program.report e.sampler e.result e.samples).space = ce.space := by
    simp
  rw [hspace]
  omega

end Esa22Copy
