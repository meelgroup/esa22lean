import Esa22Copy.Analysis.FailedState
import Esa22Copy.Analysis.FreshSubsetSupersetProbability
import Esa22Copy.Analysis.RunPeak

/-!
# Conditional probability of failure in one transition

An already failed state stays failed. From a running invariant state, a new
failure requires all threshold-many provisional samples to survive thinning.
-/

namespace Esa22Copy

open scoped ENNReal

/--
INTERNAL: supplies classical decidability for the proposition-valued conditional bound.
-/
noncomputable local instance failedStateDecidable {P : Params} (s : State P) :
    Decidable (FailedState s) := Classical.propDecidable _

/--
INTERNAL: conditional one-step failure estimate used by the stream-fold union bound.
-/
theorem step_failure_probability_le (P : Params) (a : Item P) (s : State P)
    (hs : StateSpaceInvariant P s) :
    (step P a s).toOuterMeasure {t | FailedState t} ≤
      if FailedState s then 1 else ((2 : ℝ≥0∞)⁻¹) ^ threshold P := by
  classical
  have failed_iff (u : State P) : FailedState u ↔ u.answer = some none := by
    cases h : u.answer with
    | none => simp [FailedState, finish, h]
    | some answer =>
        cases answer <;> simp [FailedState, finish, h]
  by_cases hfail : FailedState s
  · rw [if_pos hfail]
    calc
      (step P a s).toOuterMeasure {t | FailedState t} ≤
          (step P a s).toOuterMeasure Set.univ :=
        (step P a s).toOuterMeasure.mono (fun _ _ => Set.mem_univ _)
      _ = 1 :=
        (PMF.toOuterMeasure_apply_eq_one_iff
          (p := step P a s) (s := Set.univ)).2 (fun _ _ => Set.mem_univ _)
  · rw [if_neg hfail]
    cases hanswer : s.answer with
    | some answer =>
        rw [step, hanswer]
        change (PMF.pure s).toOuterMeasure {t | FailedState t} ≤ _
        rw [PMF.toOuterMeasure_pure_apply]
        change (if FailedState s then 1 else 0) ≤ _
        rw [if_neg hfail]
        exact bot_le
    | none =>
        rw [step, hanswer, PMF.toOuterMeasure_bind_apply]
        let c : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ threshold P
        have hconditional (bits : BitBlock P) :
            (let refreshed := refresh a s.level bits s.samples
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
                   answer := none }).toOuterMeasure {t | FailedState t} ≤ c := by
          dsimp only
          let X := refresh a s.level bits s.samples
          let peak := max s.peakSamples X.card
          change
            (if X.card = threshold P then
               (freshSubset P).bind fun retained =>
                 pure
                   { samples := X ∩ retained
                     level := s.level + 1
                     peakSamples := peak
                     answer := if (X ∩ retained).card = threshold P then some none else none }
             else
               pure
                 { samples := X
                   level := s.level
                   peakSamples := peak
                   answer := none }).toOuterMeasure {t | FailedState t} ≤ c
          by_cases hX : X.card = threshold P
          · rw [if_pos hX]
            have thinning_failure (Y : Finset (Item P)) :
                (X ∩ Y).card = threshold P ↔ X ⊆ Y := by
              constructor
              · intro hcard
                apply Finset.inter_eq_left.mp
                apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
                simp [hcard, hX]
              · intro hsubset
                rw [Finset.inter_eq_left.mpr hsubset, hX]
            change
              ((freshSubset P).map fun retained =>
                { samples := X ∩ retained
                  level := s.level + 1
                  peakSamples := peak
                  answer := if (X ∩ retained).card = threshold P then some none else none }).toOuterMeasure
                  {t | FailedState t} ≤ c
            rw [PMF.toOuterMeasure_map_apply]
            have hevent :
                (fun retained : Finset (Item P) =>
                  { samples := X ∩ retained
                    level := s.level + 1
                    peakSamples := peak
                    answer := if (X ∩ retained).card = threshold P then some none else none }) ⁻¹'
                    {t | FailedState t} = {Y | X ⊆ Y} := by
              ext retained
              simp [failed_iff, thinning_failure]
            rw [hevent, freshSubset_superset_probability, hX]
          · rw [if_neg hX]
            change (PMF.pure
              { samples := X
                level := s.level
                peakSamples := peak
                answer := none }).toOuterMeasure {t | FailedState t} ≤ c
            rw [PMF.toOuterMeasure_pure_apply]
            simp [failed_iff]
        calc
          ∑' bits, (freshBlock P) bits *
                ((let refreshed := refresh a s.level bits s.samples
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
                        answer := none }).toOuterMeasure {t | FailedState t}) ≤
              ∑' bits, (freshBlock P) bits * c :=
            ENNReal.tsum_le_tsum fun bits =>
              mul_le_mul_right (hconditional bits) ((freshBlock P) bits)
          _ = c := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · reduced failure to the stored marker and thinning failure to set containment
* r1 · reduced · isolated the invariant conditional estimate; its bind/thinning proof remains open
-/
