import Esa22Copy.Interface.Pseudocode

/-!
# The program and the model are the same algorithm

`Model/Program.lean` defines the estimator as a program over a sealed dictionary.
`Interface/Pseudocode.lean` defines the same transition on a mathematical
`Finset`, where the accuracy proof can use the whole Mathlib API.  This module
proves they agree.

The main result, `estimatorOutput_eq`, is an equality **of distributions**, not a
correspondence of supports.  So every probabilistic statement proved about the
model — accuracy, failure probability, peak sample size — is literally a
statement about the algorithm, with no transfer argument at each use.

Two things are worth noting about the direction of the reduction.

* The program is the definition and the model is derived from it, not the other
  way round.  `RunState.toState` reads the new sample set, the new level and the
  bottom flag off the program's result rather than recomputing them, so a program
  that stopped doing the work would fail `freshCell_toState` — it could not merely
  under-report its cost.
* `freshCell` draws the thinning randomness on every arrival, while `step` draws it
  only when the threshold test fires.  These give the same distribution because
  drawing a value and ignoring it is the identity on distributions
  (`PMF.bind_const`), and taking both draws up front means the branch is decided
  in one place — inside the program — rather than written out twice.

## Main results

* `toFinset_step`, `level_step`, `answer_step` — what the program computes.
* `freshCell_toState` — one arrival of the program is one arrival of the model.
* `execRunState_map` — and so is the whole loop.
* `estimatorOutput_eq` — and so is the estimator, meters dropped.
-/

namespace Esa22Copy

open Arlib.Computation

variable {P : Params}

/-! ## What the program computes -/

/-! Every statement below is about the program applied to *sealed* randomness —
`Block.ofFun bits`, `Coins.ofFinset retained` — and reads its level off a
`Sampler`.  The right-hand sides are unchanged: `refresh`, `acceptsAt` and
`retained` are what the accuracy proof is written in, and sealing the program's
access to them changed none of that.  The two bridge lemmas that connect the two
sides are in `Model/Program.lean` and both hold by `rfl`. -/

/-- **The arrival line computes `refresh`.** -/
@[simp] theorem toFinset_arrival (s : Sampler) (bits : BitBlock P) (a : Item P)
    (d : Roster (Item P)) :
    ((Program.arrival s (Block.ofFun bits) a d).val).toFinset
      = refresh a s.levelOf bits d.toFinset := by
  by_cases h : acceptsAt s.levelOf bits <;> simp [Program.arrival, refresh, h]

/-- INTERNAL: the arrival line's sample size, in set terms. -/
@[simp] theorem card_arrival (s : Sampler) (bits : BitBlock P) (a : Item P)
    (d : Roster (Item P)) :
    ((Program.arrival s (Block.ofFun bits) a d).val).card
      = (refresh a s.levelOf bits d.toFinset).card := by
  rw [← Roster.card_toFinset, toFinset_arrival]

/-- **The thinning line computes the intersection.** -/
@[simp] theorem toFinset_thin (retained : Finset (Item P)) (d : Roster (Item P)) :
    ((Program.thin (Coins.ofFinset retained) d).val).toFinset = d.toFinset ∩ retained := by
  rw [Program.thin, Roster.toFinset_filterErase]
  ext y
  simp only [Finset.mem_filter, Finset.mem_inter, val_flip_ofFinset, decide_eq_true_eq]

/-- **The sample set the program leaves**, branch for branch: `refresh`, thinned
against `retained` exactly when the threshold test fires. -/
@[simp] theorem toFinset_step (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (retained : Finset (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    ((Program.step thr a s (Block.ofFun bits) (Coins.ofFinset retained) res d).val).samples.toFinset =
      (if (refresh a s.levelOf bits d.toFinset).card = thr then
        refresh a s.levelOf bits d.toFinset ∩ retained
      else refresh a s.levelOf bits d.toFinset) := by
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr <;>
    simp [Program.step, h, apply_ite (Charged.val (κ := StdOp) (κₛ := Cell)),
      apply_ite RunState.samples]

/-- **The level the program leaves**: incremented exactly on the thinning branch.

Read through `Sampler.levelOf`, because the level is no longer a field of the
result — it is inside a sealed sampler, and this is the specification's view of
it. -/
@[simp] theorem level_step (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (retained : Finset (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    ((Program.step thr a s (Block.ofFun bits) (Coins.ofFinset retained) res d).val).sampler.levelOf =
      (if (refresh a s.levelOf bits d.toFinset).card = thr then s.levelOf + 1 else s.levelOf) := by
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr <;>
    simp [Program.step, h, apply_ite (Charged.val (κ := StdOp) (κₛ := Cell)),
      apply_ite RunState.sampler]

/-- INTERNAL: the thinning line's sample size, in set terms. -/
@[simp] theorem card_thin (retained : Finset (Item P)) (d : Roster (Item P)) :
    ((Program.thin (Coins.ofFinset retained) d).val).card = (d.toFinset ∩ retained).card := by
  rw [← Roster.card_toFinset, toFinset_thin]

/-- **Whether the program reports bottom**: only after a thinning that left the
sample still at the threshold. -/
@[simp] theorem answer_step (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (retained : Finset (Item P)) (res : Slot Answer) (d : Roster (Item P))
    (hres : res.get = none) :
    ((Program.step thr a s (Block.ofFun bits) (Coins.ofFinset retained) res d).val).result.get =
      (if (refresh a s.levelOf bits d.toFinset).card = thr then
        (if (refresh a s.levelOf bits d.toFinset ∩ retained).card = thr then some none else none)
      else none) := by
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr <;>
    simp [Program.step, h, hres, apply_ite (Charged.val (κ := StdOp) (κₛ := Cell)),
      apply_ite RunState.result, apply_ite (Slot.get (α := Answer))]

/-! ### The complete arrival

`Program.arrivalStep` is `Program.step` behind the charged stop test.  Its value
is therefore the step's when the run is going and the state unchanged when it is
not — and the second of those is what lets `RunState.toState` be a read-off with
no branch of its own. -/

/-- INTERNAL: a running arrival computes what `step` computes. -/
@[simp] theorem val_arrivalStep_none (thr : Nat) (a : Item P) (s : Sampler)
    (b : Block (P.m + 1)) (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P))
    (hres : res.get = none) :
    (Program.arrivalStep thr a s b coins res d).val
      = (Program.step thr a s b coins res d).val := by
  simp [Program.arrivalStep, hres]

/-- INTERNAL: an arrival of a stopped run leaves everything alone. -/
@[simp] theorem val_arrivalStep_some (thr : Nat) (a : Item P) (s : Sampler)
    (b : Block (P.m + 1)) (coins : Coins (Item P)) (res : Slot Answer) (d : Roster (Item P))
    (ans : Answer) (hres : res.get = some ans) :
    (Program.arrivalStep thr a s b coins res d).val = ⟨d, s, res⟩ := by
  simp [Program.arrivalStep, hres]

/-! ## The model an execution denotes -/

/-- The mathematical state an execution holds: its dictionary, read as a set. -/
noncomputable def RunState.toState (e : RunState P) : State P where
  samples := e.samples.toFinset
  level := e.level
  answer := e.answer

@[simp] theorem RunState.toState_samples (e : RunState P) :
    e.toState.samples = e.samples.toFinset := rfl

@[simp] theorem RunState.toState_level (e : RunState P) : e.toState.level = e.level := rfl

@[simp] theorem RunState.toState_answer (e : RunState P) : e.toState.answer = e.answer := rfl

@[simp] theorem toState_initialState : (Program.initialState P).toState = initialState P := by
  simp [RunState.toState, Program.initialState, initialState, RunState.level, RunState.answer]

/-- **A stopped run stays put.**  The arrival performs its stop test, discovers
the run has answered, and leaves the state — the answer included — exactly as it
found it.  This is what lets `freshCell_toState` need no branch of its own. -/
theorem toState_arrivalStep_stopped (P : Params) (a : Item P) (e : RunState P)
    (bits : BitBlock P) (retained : Finset (Item P)) (ans : Answer)
    (h : e.answer = some ans) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).val.toState = e.toState := by
  simp only [RunState.toState,
    val_arrivalStep_some _ _ _ _ _ _ _ ans h, RunState.level, RunState.answer]

/-- **The thinning branch**: the state the program leaves when the test fires. -/
theorem toState_arrivalStep_thin (P : Params) (a : Item P) (e : RunState P) (bits : BitBlock P)
    (retained : Finset (Item P)) (hrun : e.answer = none)
    (h : (refresh a e.level bits e.samples.toFinset).card = threshold P) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).val.toState =
      { samples := refresh a e.level bits e.samples.toFinset ∩ retained
        level := e.level + 1
        answer := if (refresh a e.level bits e.samples.toFinset ∩ retained).card = threshold P then
          some none else none } := by
  simp only [RunState.level] at h
  simp only [RunState.toState, RunState.level, RunState.answer,
    val_arrivalStep_none _ _ _ _ _ _ _ hrun, toFinset_step, level_step,
    answer_step _ _ _ _ _ _ _ hrun, h, if_pos]
  rfl


/-- **The ordinary branch**: the state the program leaves when it does not. -/
theorem toState_arrivalStep_noThin (P : Params) (a : Item P) (e : RunState P) (bits : BitBlock P)
    (retained : Finset (Item P)) (hrun : e.answer = none)
    (h : ¬ (refresh a e.level bits e.samples.toFinset).card = threshold P) :
    (Program.arrivalStep (threshold P) a e.sampler (Block.ofFun bits)
        (Coins.ofFinset retained) e.result e.samples).val.toState =
      { samples := refresh a e.level bits e.samples.toFinset
        level := e.level
        answer := none } := by
  simp only [RunState.level] at h
  simp only [RunState.toState, RunState.level, RunState.answer,
    val_arrivalStep_none _ _ _ _ _ _ _ hrun, toFinset_step, level_step,
    answer_step _ _ _ _ _ _ _ hrun, h, if_neg, not_false_eq_true]

/-! ## The two runs agree -/

/-- **One arrival of the program is one arrival of the model.**

Note what is not here: a case split written on the driver's side.  The program
performs its own stop test, so both branches below are branches of
`Program.arrivalStep`, and this proof only says that the model agrees with each. -/
theorem freshCell_toState (P : Params) (a : Item P) (e : RunState P) :
    (freshCell P).map (fun r =>
        (Program.arrivalStep (threshold P) a e.sampler r.bits r.coins
          e.result e.samples).val.toState)
      = step P a e.toState := by
  rw [freshCell, step]
  simp only [RunState.toState_answer]
  cases hanswer : e.answer with
  | some ans =>
      rw [PMF.map_bind]
      refine Eq.trans (congrArg ((freshBlock P).bind) (funext fun bits => ?_))
        (PMF.bind_const (freshBlock P) _)
      rw [PMF.map_comp]
      refine Eq.trans (congrArg ((freshSubset P).map) (funext fun retained => ?_))
        (PMF.map_const (freshSubset P) _)
      exact toState_arrivalStep_stopped P a e bits retained ans hanswer
  | none =>
      rw [PMF.map_bind]
      refine congrArg _ (funext fun bits => ?_)
      rw [PMF.map_comp]
      by_cases hthreshold :
          (refresh a e.toState.level bits e.toState.samples).card = threshold P
      · rw [if_pos hthreshold]
        refine congrArg ((freshSubset P).map) (funext fun retained => ?_)
        exact toState_arrivalStep_thin P a e bits retained hanswer hthreshold
      · rw [if_neg hthreshold]
        refine Eq.trans (congrArg ((freshSubset P).map) (funext fun retained => ?_))
          (PMF.map_const (freshSubset P) _)
        exact toState_arrivalStep_noThin P a e bits retained hanswer hthreshold

/-- **The whole loop agrees**: the execution's state marginal is `runState`.

The induction is over the stream and the tape together, peeling one item off each
— which is exactly what `Program.run`'s `zip` does, so the two stay in step
without either being defined in terms of the other. -/
theorem execRunState_map (P : Params) (A : Stream P) :
    (execRunState P A).map (fun c => c.val.toState) = runState P A := by
  have fold : ∀ (l : List (Item P)) (b : RunState P),
      ((freshTape P l.length).map fun tape =>
          (Charged.foldl (fun st ar => Program.arrivalStep (threshold P) ar.1 st.sampler
            ar.2.bits ar.2.coins st.result st.samples) (l.zip tape) b).val.toState)
        = l.foldlM (fun s a => step P a s) b.toState := by
    intro l
    induction l with
    | nil => intro b; exact PMF.pure_map _ _
    | cons a l ih =>
        intro b
        show ((freshCell P).bind fun r =>
            (freshTape P l.length).map (r :: ·)).map _
          = (step P a b.toState).bind fun u => l.foldlM (fun s a => step P a s) u
        rw [← freshCell_toState P a b, PMF.bind_map, PMF.map_bind]
        refine congrArg _ (funext fun r => ?_)
        rw [PMF.map_comp]
        exact ih _
  have h := fold (List.ofFn A) (Program.initialState P)
  rw [toState_initialState, List.length_ofFn] at h
  rw [execRunState, PMF.map_comp, runState]
  exact h

/-! ## The final report -/

/-- INTERNAL: what the program's last line returns. -/
@[simp] theorem val_report (s : Sampler) (res : Slot Answer) (d : Roster (Item P)) :
    (Program.report (P := P) s res d).val =
      if res.get.isSome then none else some (d.card * 2 ^ s.levelOf) := by
  cases hres : res.get <;> simp [Program.report, hres]

/-- INTERNAL: **the program's last line is the model's.**  Both test the register
rather than reading it, and both scale `|X|` by `2ˡᵉᵛᵉˡ`, so there is nothing
between them to bridge. -/
@[simp] theorem report_eq (e : RunState P) :
    (Program.report e.sampler e.result e.samples).val = finish e.toState := by
  simp [val_report, finish, RunState.toState, RunState.answer, RunState.level]

/--
**The program's estimator is the paper's estimator.**

Forgetting the running-time tally — which is exactly `Charged.val` — turns the
algorithm of `Model/Program.lean` into the model of `Interface/Pseudocode.lean`,
exactly and as distributions.  So the accuracy theorem, the failure-probability
bound and the space bound proved for `run` are theorems about the program.
-/
theorem estimatorOutput_eq (P : Params) (A : Stream P) :
    estimatorOutput P A = run P A := by
  rw [estimatorOutput, estimator_eq, PMF.map_comp, run, ← execRunState_map, PMF.bind_map]
  refine congrArg _ (funext fun ce => ?_)
  refine congrArg PMF.pure ?_
  simp only [Function.comp_apply, Charged.val_bind, Charged.val_map, report_eq]

end Esa22Copy
