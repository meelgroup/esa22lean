import Esa22Copy.Analysis.FixedLevelErrorEvent
import Esa22Copy.Analysis.OutProbRLeOfSupportedCoupling
import Esa22Copy.Analysis.ProbabilityModel
import Esa22Copy.Analysis.RelaxedCoupling

/-!
# One adaptive level slice is dominated by a fixed-level sample

The coupling is used only for event containment.  The fresh fixed-level coins
remain unconditional; in particular, this statement does not condition them on
the adaptively selected final level.
-/

namespace Esa22Copy

/--
INTERNAL: the relaxed error probability on final level `k` is at most the
unconditional fixed-level sampling-error probability.
-/
theorem relaxed_level_slice_le_fixed_sample_error (P : Params) (A : Stream P)
    (k : Nat) (_hk : k ≤ P.m) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
        ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤
      ((freshLevelCoins P).toOuterMeasure (fixedLevelErrorEvent P A k)).toReal := by
  let iEnd : Fin (P.m + 1) := Fin.last P.m
  obtain ⟨κ, hfst, hsnd, hinvariant⟩ :=
    relaxedRun_levelSample_coupling P A iEnd
  let lift : RelaxedState P × LevelCoins P →
      (RelaxedState P × Nat) × (LevelCoins P × Nat) :=
    fun z => ((z.1, 0), (z.2, 0))
  let κ' := κ.map lift
  let ν := (freshLevelCoins P).map fun coins => (coins, 0)
  have hprefix : relaxedRunPrefix P A iEnd = relaxedRun P A := by
    unfold relaxedRunPrefix relaxedRun
    change ((List.ofFn A).take P.m).foldlM _ _ = (List.ofFn A).foldlM _ _
    rw [List.take_of_length_le (by simp)]
  have hdom :
      Arlib.Approximation.outProbR (relaxedRunCost P A)
          ({s | s.level = k} ∩ relaxedErrorEvent P A) ≤
        Arlib.Approximation.outProbR ν (fixedLevelErrorEvent P A k) := by
    apply outProbR_le_of_supported_coupling
      (relaxedRunCost P A) ν
      ({s | s.level = k} ∩ relaxedErrorEvent P A)
      (fixedLevelErrorEvent P A k) κ'
    · calc
        κ'.map Prod.fst = (κ.map Prod.fst).map (fun s => (s, 0)) := by
          simp only [κ', lift, PMF.map_comp, Function.comp_def]
        _ = (relaxedRunPrefix P A iEnd).map (fun s => (s, 0)) := by rw [hfst]
        _ = relaxedRunCost P A := by rw [hprefix]; rfl
    · calc
        κ'.map Prod.snd = (κ.map Prod.snd).map (fun coins => (coins, 0)) := by
          simp only [κ', lift, PMF.map_comp, Function.comp_def]
        _ = (freshLevelCoins P).map (fun coins => (coins, 0)) := by rw [hsnd]
        _ = ν := rfl
    · intro z hz hzerror
      obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      have hsamples := hinvariant q hq
      rcases hzerror with ⟨hlevel, herror⟩
      change q.1.level = k at hlevel
      change q.1 ∈ relaxedErrorEvent P A at herror
      change q.2 ∈ fixedLevelErrorEvent P A k
      unfold fixedLevelErrorEvent
      unfold relaxedErrorEvent at herror
      simp only [iEnd] at hsamples
      rw [← hlevel]
      change ((q.1.samples.card : Real) /
        ((2 : Real) ^ (-(q.1.level : Int))) ∉
          Arlib.relErr P.eps (F0 A : Real)) at herror
      change (((levelSample q.2 A q.1.level (Fin.last P.m)).card : Real) /
        ((2 : Real) ^ (-(q.1.level : Int))) ∉
          Arlib.relErr P.eps (F0 A : Real))
      rw [← hsamples]
      exact herror
  refine hdom.trans_eq ?_
  rw [Arlib.Approximation.outProbR_def]
  unfold Arlib.Approximation.outProb
  rw [PMF.toOuterMeasure_map_apply]
  rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · lifted the final-prefix coupling and transferred the error event support-wise
-/
