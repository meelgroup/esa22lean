import Esa22Copy.Analysis.ProbabilityModel
import Esa22Copy.Analysis.CriticalLevel
import Arlib.Approximation.UnionBound

/-!
# Counterexample to the unrestricted relaxed good-rate union bound

The proposed bookkeeping lemma permits a negative per-level budget.  For a
one-item stream the critical level is zero, so all of its positive-level slice
hypotheses are vacuous, while its conclusion bounds a nonnegative probability
by a negative number.

The declaration it refutes has since gained the binder `hb : 0 ≤ b`; this
theorem records the failure of the earlier version without that hypothesis.
-/

namespace Esa22Copy

/-- INTERNAL: concrete legal parameters used by the negative-budget counterexample. -/
private noncomputable def unionBoundCounterexampleParams : Params where
  n := 1
  m := 1
  hn := by omega
  hm := by omega
  eps := 1 / 2
  delta := 1 / 2
  heps := by norm_num
  hdelta := by norm_num

/-- INTERNAL: logarithmic arithmetic for the concrete threshold calculation. -/
private lemma logb_two_sixteen : Real.logb 2 16 = 4 := by
  rw [show (16 : Real) = 2 ^ 4 by norm_num, Real.logb, Real.log_pow]
  have hlog : Real.log (2 : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  norm_num

/-- INTERNAL: the counterexample's threshold evaluates exactly to `192`. -/
private lemma unionBoundCounterexample_threshold :
    threshold unionBoundCounterexampleParams = 192 := by
  norm_num [threshold, unionBoundCounterexampleParams, logb_two_sixteen]

/-- INTERNAL: every stream in the one-item instance has critical level zero. -/
private lemma unionBoundCounterexample_criticalLevel
    (A : Stream unionBoundCounterexampleParams) :
    criticalLevel unionBoundCounterexampleParams A = 0 := by
  let z : Item unionBoundCounterexampleParams :=
    ⟨0, by simp [unionBoundCounterexampleParams]⟩
  have hA : A = fun _ => z := by
    funext i
    apply Fin.eq_of_val_eq
    have hi : (A i).val < 1 := by
      simpa [unionBoundCounterexampleParams] using (A i).isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
  subst A
  have hdistinct :
      distinctSet (fun _ : Fin unionBoundCounterexampleParams.m => z) = {z} := by
    ext x
    simp only [distinctSet, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      rfl
    · intro hx
      subst x
      exact ⟨⟨0, by simp [unionBoundCounterexampleParams]⟩, rfl⟩
  have hf0 : F0 (fun _ : Fin unionBoundCounterexampleParams.m => z) = 1 := by
    rw [F0, hdistinct]
    simp
  unfold criticalLevel
  rw [Nat.floor_eq_zero, unionBoundCounterexample_threshold, hf0]
  norm_num [Real.logb]
  have hloglt : Real.log (1 / 48 : Real) < Real.log 2 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_lt_one hlogpos).2 hloglt

/--
INTERNAL: the unrestricted relaxed good-rate union-bound schema is false; the
one-item instance and budget `-1` make its hypotheses vacuous and its conclusion
negative.
-/
theorem relaxed_good_rate_union_bound_false :
    ¬ (∀ (P : Params) (A : Stream P) (b : Real),
      (∀ k : Nat, 0 < k → k ≤ P.m → k ≤ criticalLevel P A →
        Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤ b) →
      Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level ≤ criticalLevel P A} ∩ relaxedErrorEvent P A) ≤
        (P.m : Real) * b) := by
  intro hbound
  let A : Stream unionBoundCounterexampleParams := fun _ =>
    ⟨0, by simp [unionBoundCounterexampleParams]⟩
  have hcritical := unionBoundCounterexample_criticalLevel A
  have hslice : ∀ k : Nat, 0 < k → k ≤ unionBoundCounterexampleParams.m →
      k ≤ criticalLevel unionBoundCounterexampleParams A →
      Arlib.Approximation.outProbR
        (relaxedRunCost unionBoundCounterexampleParams A)
        ({s | s.level = k} ∩
          relaxedErrorEvent unionBoundCounterexampleParams A) ≤ (-1 : Real) := by
    intro k hkpos _ hkcritical
    omega
  have hle := hbound unionBoundCounterexampleParams A (-1) hslice
  have hnonneg := Arlib.Approximation.outProbR_nonneg
    (relaxedRunCost unionBoundCounterexampleParams A)
    ({s | s.level ≤ criticalLevel unionBoundCounterexampleParams A} ∩
      relaxedErrorEvent unionBoundCounterexampleParams A)
  norm_num [unionBoundCounterexampleParams] at hle
  linarith

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · disproved · concrete one-item instance refutes the unrestricted negative-budget schema
-/
