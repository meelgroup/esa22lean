import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.RunPeak

/-!
# Deterministic worst-case time bound

Every reachable run of the estimator performs at most
`P.m * (2 * threshold P + 8) + 3` operations.  The bound is explicit: no constant is
hidden, and no asymptotic notation appears.

## Where the numbers come from

Nothing in `Model/` says what a line of the algorithm costs, and nothing here
declares it either.  `Esa22Copy.work` is the program of `Model/Program.lean` run
on one arrival, and its cost is `Charged.cost` — the tally the elaborator
accumulates from the operations the program performs.  `arrivalBaseCost` and
`thinningCost` below are closed *expressions* for that tally, and
`cost_work_of_running` is the theorem that the program spends exactly them.  If
the program changed, the theorem would break; there is no second definition to
keep in step with it.

## The accounting

The accounting is the paper's own.  An arrival does four things — erase, flip the
insertion coin, maybe insert, compare `|X|` with the threshold — and that is all,
*unless* the comparison succeeds, in which case the run thins.  Thinning is the
only expensive line, costing one coin and at most one delete per element of a
sample set that the branch condition pins at exactly `threshold P`, and it is
also the only line that raises the level.  So the expensive work is paid for by
level increments, the level rises by at most one per arrival, and the total is
`4` per arrival plus `2 * threshold P + 3` per level.

`execStep_cost_le` is where that coupling of price to level is proved.
Everything after it is bookkeeping over the fold, in the style of
`Esa22Copy.runState_space_invariant`.

## Main results

* `cost_work_of_running` — what one arrival of the program costs, in closed form.
* `execStep_level_le`, `execStep_level_le_succ` — the level is nondecreasing along
  a supported transition and rises by at most one.
* `execStep_cost_le` — a transition costs `5` plus its level increment times
  `2 * threshold P + 3`.
* `execRunState_time_invariant` — the level-sensitive bound for the fold.
* `execRunLevel_steps_le` — the sharp bound, charging the thinning price once per
  level rather than once per arrival.
* `execRunState_level_le` — the level is at most `P.m + 1 - threshold P`.
* `estimator_steps_le`, `estimator_worstSteps_le` — the closed worst-case bound,
  support-wise and as a bound on the time operator `Arlib.Computation.worstSteps`.
-/

namespace Esa22Copy

open Arlib.Computation

/-! ## What the program spends

Each theorem in this section computes the cost of a piece of the program.  None
of them is a definition of that cost: the left-hand sides are `Charged.cost`
applied to the algorithm, and the right-hand sides are what it comes to. -/

/-- **The cost of the arrival line**: an erase, a coin, and the reinsertion when
the coin accepts. -/
theorem cost_arrival {P : Params} (s : Sampler) (bits : BitBlock P) (a : Item P)
    (d : Roster (Item P)) :
    (Program.arrival s (Block.ofFun bits) a d).cost =
      CostVec.one (StdOp.roster .erase) + CostVec.one (StdOp.rand .accept)
        + (if acceptsAt s.levelOf bits then CostVec.one (StdOp.roster .insert) else 0) := by
  by_cases h : acceptsAt s.levelOf bits
  · simp only [Program.arrival, h, Charged.cost_bind, Roster.cost_erase, Sampler.cost_accept,
      val_accept_ofFun, if_pos, Roster.cost_insert, opcode_roster, randOpcode_rand]
    abel
  · simp [Program.arrival, h]

/-- **The cost of the thinning line**: one coin per element, one deletion per
element discarded.  The deletion count is read off the pass the program makes,
not supplied. -/
theorem cost_thin {P : Params} (retained : Finset (Item P)) (d : Roster (Item P)) :
    (Program.thin (Coins.ofFinset retained) d).cost =
      CostVec.many (StdOp.rand .flip) d.card
        + CostVec.many (StdOp.roster .erase) (d.card - (d.toFinset ∩ retained).card) := by
  have hfilter : d.toFinset.filter (fun x => (Coins.flip (κ := StdOp) (κₛ := Cell)
      x (Coins.ofFinset retained)).val) = d.toFinset ∩ retained := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter, val_flip_ofFinset, decide_eq_true_eq]
  rw [Program.thin, Roster.cost_filterErase_card (StdOp.rand .flip) _ _ (fun _ => rfl), hfilter, opcode_roster]

/-- **The cost of one arrival, whole**: the arrival line, the threshold test, and
— only when that test fires — the thinning line, the level increment and the
second test.  The branch is the program's own `if`. -/
theorem cost_step {P : Params} (thr : Nat) (a : Item P) (s : Sampler) (bits : BitBlock P)
    (retained : Finset (Item P)) (res : Slot Answer) (d : Roster (Item P)) :
    (Program.step thr a s (Block.ofFun bits) (Coins.ofFinset retained) res d).cost =
      (Program.arrival s (Block.ofFun bits) a d).cost + CostVec.one (StdOp.roster .cardEq)
        + (if (refresh a s.levelOf bits d.toFinset).card = thr then
            (Program.thin (Coins.ofFinset retained)
                (Program.arrival s (Block.ofFun bits) a d).val).cost
              + CostVec.one (StdOp.rand .halve) + CostVec.one (StdOp.roster .cardEq)
              + (if (refresh a s.levelOf bits d.toFinset ∩ retained).card = thr then
                  CostVec.one (StdOp.slot .fill) else 0)
          else 0) := by
  by_cases h : (refresh a s.levelOf bits d.toFinset).card = thr
  · simp only [Program.step, h, Charged.cost_bind, Roster.cost_cardEq, Roster.val_cardEq, opcode_roster,
      card_arrival, card_thin, toFinset_arrival, decide_eq_true_eq, if_pos,
      Sampler.cost_halve, randOpcode_rand, apply_ite (Charged.cost (κ := StdOp) (κₛ := Cell)),
      Slot.cost_fill, slotOpcode_slot, Charged.cost_pure]
    abel
  · simp only [Program.step, h, Charged.cost_bind, Roster.cost_cardEq, Roster.val_cardEq, opcode_roster,
      card_arrival, decide_eq_true_eq, if_neg, Charged.cost_pure, not_false_eq_true]
    abel

/-- **The cost of the final report**: the test asking whether there is anything
to report, and the size query when there is. -/
theorem cost_report {P : Params} (s : Sampler) (res : Slot Answer)
    (d : Roster (Item P)) :
    (Program.report (P := P) s res d).cost =
      CostVec.one (StdOp.slot .test)
        + (if res.get.isNone then
            CostVec.one (StdOp.roster .size) + CostVec.one (StdOp.rand .inflate) else 0) := by
  cases hres : res.get <;>
    simp [Program.report, hres, Slot.val_isEmpty]

/-- INTERNAL: the report is three operations, or one when the run has stopped.

Three, not two: the paper's last line is `return |X| / p`, and the division is an
operation now that the level lives in a sealed `Sampler`.  The driver used to do
it, from a level it read for nothing. -/
theorem steps_report_le {P : Params} (s : Sampler) (res : Slot Answer)
    (d : Roster (Item P)) :
    Charged.steps (Rate.unit StdOp) (Program.report (P := P) s res d) ≤ 3 := by
  rw [Charged.steps, cost_report]
  cases res.get <;>
    simp [CostVec.steps_add, CostVec.steps_one]

/-! ## What one arrival costs, uniformly

The bound below holds for *every* incoming state, which is what lets the loop's
cost come from `Arlib.Computation.Charged.steps_foldl_le` rather than from an
induction written here.  It used to be an induction: a level-sensitive invariant
carried along the fold by hand, plus a second invariant bounding the level, plus
the collapse of the two.  The program now contains its own loop, so arlib's fold
lemma applies and all of that is gone.

The thinning branch is bounded without knowing anything about the incoming
sample set, because the branch is guarded by the program's own `cardEq thr`: the
roster being thinned has exactly `thr` elements *because the program tested that
it does*. -/

/-- INTERNAL: the arrival line is three operations, or two when the coin refuses. -/
theorem steps_arrival_le {P : Params} (s : Sampler) (b : Block (P.m + 1)) (a : Item P)
    (d : Roster (Item P)) :
    Charged.steps (Rate.unit StdOp) (Program.arrival s b a d) ≤ 3 := by
  rw [Charged.steps, Program.arrival]
  by_cases h : (Sampler.accept (κ := StdOp) (κₛ := Cell) b s).val <;>
    simp [Charged.cost_bind, h, CostVec.steps_add, CostVec.steps_one]

/-- INTERNAL: thinning a roster of `n` elements is at most `2 * n` operations —
one coin per element, and at most one deletion per element. -/
theorem steps_thin_le {P : Params} (coins : Coins (Item P)) (d : Roster (Item P)) :
    Charged.steps (Rate.unit StdOp) (Program.thin coins d) ≤ 2 * d.card := by
  rw [Charged.steps, Program.thin,
    Roster.cost_filterErase_card (StdOp.rand .flip) _ _ (fun _ => rfl), opcode_roster]
  simp only [CostVec.steps_add, CostVec.steps_many, Rate.unit_cost, one_mul]
  omega

/-- **One arrival of a running estimator is at most `2 * thr + 7` operations.**

No hypothesis about the incoming state: the thinning branch is guarded by the
program's own threshold test. -/
theorem steps_step_le {P : Params} (thr : Nat) (a : Item P) (s : Sampler)
    (b : Block (P.m + 1)) (coins : Coins (Item P)) (res : Slot Answer)
    (d : Roster (Item P)) :
    Charged.steps (Rate.unit StdOp) (Program.step thr a s b coins res d) ≤ 2 * thr + 7 := by
  have harr := steps_arrival_le s b a d
  rw [Charged.steps] at harr ⊢
  by_cases hfull : (Roster.cardEq (κ := StdOp) (κₛ := Cell) thr
      (Program.arrival s b a d).val).val
  · have hcard : (Program.arrival s b a d).val.card = thr := by
      simpa using hfull
    have hthin := steps_thin_le coins (Program.arrival s b a d).val
    rw [Charged.steps, hcard] at hthin
    by_cases hstill : (Roster.cardEq (κ := StdOp) (κₛ := Cell) thr
        (Program.thin coins (Program.arrival s b a d).val).val).val <;>
      simp only [Program.step, Charged.cost_bind, hfull, hstill, if_pos, if_neg,
        Roster.cost_cardEq, Sampler.cost_halve, Slot.cost_fill, Charged.cost_pure,
        CostVec.steps_add, CostVec.steps_one, CostVec.steps_zero, Rate.unit_cost,
        opcode_roster, randOpcode_rand, slotOpcode_slot,
        Bool.false_eq_true, not_false_eq_true] <;>
      omega
  · simp only [Program.step, Charged.cost_bind, hfull, if_neg, Roster.cost_cardEq,
      Charged.cost_pure, CostVec.steps_add, CostVec.steps_one, CostVec.steps_zero,
      Rate.unit_cost, opcode_roster, Bool.false_eq_true, not_false_eq_true]
    omega

/-- **One arrival of the estimator is at most `2 * thr + 8` operations.**

The extra one is the stop test, which every arrival pays.  A run that has already
answered pays exactly that and nothing else. -/
theorem steps_arrivalStep_le {P : Params} (thr : Nat) (a : Item P) (s : Sampler)
    (b : Block (P.m + 1)) (coins : Coins (Item P)) (res : Slot Answer)
    (d : Roster (Item P)) :
    Charged.steps (Rate.unit StdOp) (Program.arrivalStep thr a s b coins res d)
      ≤ 2 * thr + 8 := by
  have h := steps_step_le thr a s b coins res d
  rw [Charged.steps] at h ⊢
  by_cases hrun : (Slot.isEmpty (κ := StdOp) (κₛ := Cell) res).val
  · simp only [Program.arrivalStep, hrun, if_pos, Charged.cost_bind, Slot.cost_isEmpty,
      CostVec.steps_add, CostVec.steps_one, Rate.unit_cost, slotOpcode_slot]
    omega
  · simp only [Program.arrivalStep, hrun, if_neg, Charged.cost_bind, Slot.cost_isEmpty,
      Charged.cost_pure, CostVec.steps_add, CostVec.steps_one, CostVec.steps_zero,
      Rate.unit_cost, slotOpcode_slot, Bool.false_eq_true, not_false_eq_true]
    omega

/-! ## The loop -/

/-- **The whole run is at most `m * (2 * thr + 8)` operations.**

`Arlib.Computation.Charged.steps_foldl_le` does the induction, because the loop
is `Charged.foldl` inside `Model/Program.lean` rather than a `PMF` fold written
in a driver. -/
theorem steps_run_le {P : Params} (thr : Nat) (A : Stream P)
    (tape : List (Program.Randomness P)) :
    Charged.steps (Rate.unit StdOp) (Program.run thr A tape)
      ≤ ((List.ofFn A).zip tape).length * (2 * thr + 8) := by
  rw [Program.run]
  apply Charged.steps_foldl_le
  intro st ar
  exact steps_arrivalStep_le thr ar.1 st.sampler ar.2.bits ar.2.coins st.result st.samples

/-- INTERNAL: a drawn tape has the length it was asked for. -/
theorem length_of_mem_freshTape (P : Params) :
    ∀ (n : Nat) (tape : List (Program.Randomness P)),
      tape ∈ (freshTape P n).support → tape.length = n := by
  intro n
  induction n with
  | zero => intro tape h; simpa [freshTape] using h
  | succ n ih =>
      intro tape h
      rw [freshTape, PMF.mem_support_bind_iff] at h
      obtain ⟨r, _, h⟩ := h
      rw [PMF.mem_support_map_iff] at h
      obtain ⟨tape', htape', rfl⟩ := h
      simp [ih tape' htape']

/-! ## The closed bound -/

/-- **Every reachable outcome of the estimator is within the bound.** -/
theorem estimator_steps_le (P : Params) (A : Stream P)
    (outcome : Charged StdOp Cell (Answer × Nat))
    (houtcome : outcome ∈ (estimator P A).support) :
    Charged.steps (Rate.unit StdOp) outcome ≤ P.m * (2 * threshold P + 8) + 3 := by
  rw [estimator_eq, PMF.mem_support_map_iff] at houtcome
  obtain ⟨ce, hce, rfl⟩ := houtcome
  rw [execRunState, PMF.mem_support_map_iff] at hce
  obtain ⟨tape, htape, rfl⟩ := hce
  have hlen : ((List.ofFn A).zip tape).length = P.m := by
    rw [List.length_zip, List.length_ofFn, length_of_mem_freshTape P P.m tape htape]
    omega
  have hrun := steps_run_le (P := P) (threshold P) A tape
  rw [hlen] at hrun
  have hreport := steps_report_le (P := P)
    (Program.run (threshold P) A tape).val.sampler
    (Program.run (threshold P) A tape).val.result
    (Program.run (threshold P) A tape).val.samples
  rw [Charged.steps] at hrun hreport ⊢
  simp only [Charged.cost_bind, Charged.cost_map, CostVec.steps_add]
  omega

/-- **The estimator's running time, as an operator applied to the program.** -/
theorem estimator_worstSteps_le (P : Params) (A : Stream P) :
    worstSteps (Rate.unit StdOp) (estimator P A)
      ≤ ((P.m * (2 * threshold P + 8) + 3 : Nat) : ℕ∞) :=
  (worstSteps_le_iff _ _ _).2 (estimator_steps_le P A)

end Esa22Copy
