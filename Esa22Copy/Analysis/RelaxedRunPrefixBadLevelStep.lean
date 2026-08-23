import Esa22Copy.Analysis.BadLevelCrossingCoupling

/-!
# One-step first-crossing bound for relaxed levels

At one stream update, a run that newly passes level `k` must have reached the
threshold in the corresponding fixed-level prefix sample.  This is the causal
step of the paper's first-crossing union bound.
-/

namespace Esa22Copy

/--
INTERNAL: one relaxed update increases the bad-level probability by at most the
fixed-level tail probability at the new prefix.
-/
theorem relaxedRunPrefix_bad_level_step (P : Params) (A : Stream P)
    (k r : Nat) (hk : k ≤ P.m) (hr : r < P.m) :
    ((relaxedRunPrefix P A ⟨r + 1, Nat.succ_lt_succ hr⟩).toOuterMeasure
        {s | k < s.level}).toReal ≤
      ((relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure
        {s | k < s.level}).toReal +
      ((freshLevelCoins P).toOuterMeasure
        {coins | threshold P ≤
          (levelSample coins A k ⟨r + 1, Nat.succ_lt_succ hr⟩).card}).toReal := by
  obtain ⟨γ, hold, hnew, hcoins, hcross⟩ :=
    bad_level_crossing_coupling P A k r hk hr
  let oldEvent : Set (RelaxedState P) := {s | k < s.level}
  let newEvent : Set (RelaxedState P) := {s | k < s.level}
  let tailEvent : Set (LevelCoins P) :=
    {coins | threshold P ≤
      (levelSample coins A k ⟨r + 1, Nat.succ_lt_succ hr⟩).card}
  have hmeasure :
      (relaxedRunPrefix P A
          ⟨r + 1, Nat.succ_lt_succ hr⟩).toOuterMeasure newEvent ≤
        (relaxedRunPrefix P A
            ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure oldEvent +
          (freshLevelCoins P).toOuterMeasure tailEvent := by
    calc
      (relaxedRunPrefix P A
          ⟨r + 1, Nat.succ_lt_succ hr⟩).toOuterMeasure newEvent =
          (γ.map (fun z => z.2.1)).toOuterMeasure newEvent := by rw [hnew]
      _ = γ.toOuterMeasure ((fun z => z.2.1) ⁻¹' newEvent) :=
        PMF.toOuterMeasure_map_apply (fun z => z.2.1) γ newEvent
      _ ≤ γ.toOuterMeasure
          (((fun z => z.1) ⁻¹' oldEvent) ∪
            ((fun z => z.2.2) ⁻¹' tailEvent)) := by
        apply γ.toOuterMeasure_mono
        intro z hz
        have hznew : k < z.2.1.level := hz.1
        rcases hcross z hz.2 hznew with hzold | hztail
        · exact Or.inl hzold
        · exact Or.inr hztail
      _ ≤ γ.toOuterMeasure ((fun z => z.1) ⁻¹' oldEvent) +
          γ.toOuterMeasure ((fun z => z.2.2) ⁻¹' tailEvent) :=
        MeasureTheory.measure_union_le _ _
      _ = (γ.map (fun z => z.1)).toOuterMeasure oldEvent +
          (γ.map (fun z => z.2.2)).toOuterMeasure tailEvent := by
        rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
      _ = (relaxedRunPrefix P A
            ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure oldEvent +
          (freshLevelCoins P).toOuterMeasure tailEvent := by rw [hold, hcoins]
  have hold_ne :
      (relaxedRunPrefix P A
          ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure oldEvent ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    refine le_trans
      ((relaxedRunPrefix P A
        ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure.mono
          (Set.subset_univ oldEvent)) ?_
    exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff
      (relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_lt hr⟩) Set.univ).2
        (Set.subset_univ _))
  have htail_ne :
      (freshLevelCoins P).toOuterMeasure tailEvent ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    refine le_trans
      ((freshLevelCoins P).toOuterMeasure.mono
        (Set.subset_univ tailEvent)) ?_
    exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff
      (freshLevelCoins P) Set.univ).2 (Set.subset_univ _))
  have hsum_ne :
      (relaxedRunPrefix P A
          ⟨r, Nat.lt_succ_of_lt hr⟩).toOuterMeasure oldEvent +
        (freshLevelCoins P).toOuterMeasure tailEvent ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hold_ne, htail_ne⟩
  have hreal := ENNReal.toReal_mono hsum_ne hmeasure
  rw [ENNReal.toReal_add hold_ne htail_ne] at hreal
  exact hreal

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · reduced · proved the marginal/union-bound calculation from
  `bad_level_crossing_coupling`; isolated that causal construction in its own module
* r3 · open · isolated the causal first-crossing step; the public prefix coupling
  records only the final adaptive sample and does not expose the predecessor state
-/
