import Arlib.Probability.Chernoff
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# A base-two moment bound from the complete Bernoulli pattern law

This file performs the finite fiber enumeration needed to turn probabilities of complete
Boolean patterns into an upper-tail estimate.
-/

namespace Esa22Copy

open scoped BigOperators

/--
INTERNAL: a complete independent Bernoulli pattern law bounds the threshold tail by its
base-two moment estimate.
-/
theorem bernoulli_pattern_upper_mgf_two
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (μ : PMF Ω) (success : Ω → I → Bool) (k T : Nat)
    (hlaw : ∀ wanted : I → Bool,
      μ.toOuterMeasure
          {ω | ∀ a : I, success ω a = true ↔ wanted a = true} =
        ∏ a : I,
          if wanted a = true then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹) :
    (μ.toOuterMeasure
      {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
        (2 : Real)⁻¹ ^ T *
          (1 + (2 : Real)⁻¹ ^ k) ^ Fintype.card I := by
  classical
  let p : Real := (2 : Real)⁻¹ ^ k
  let count (wanted : I → Bool) : Nat :=
    (Finset.univ.filter fun a : I => wanted a = true).card
  let fiber (wanted : I → Bool) : Set Ω :=
    {ω | ∀ a : I, success ω a = true ↔ wanted a = true}
  let high : Finset (I → Bool) := Finset.univ.filter fun wanted => T ≤ count wanted
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    exact pow_le_one₀ (by positivity) (by norm_num)
  have hone_sub_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have hq_le_one : ((2 : ENNReal) ^ k)⁻¹ ≤ 1 := by
    exact ENNReal.inv_le_one.2
      (one_le_pow_of_one_le' (M := ENNReal) (by norm_num) k)
  have hcover :
      {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card} ⊆
        ⋃ wanted ∈ high, fiber wanted := by
    intro ω hω
    have hwanted : success ω ∈ high := by
      simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [count] using hω
    refine Set.mem_iUnion_of_mem (success ω) ?_
    refine Set.mem_iUnion_of_mem hwanted ?_
    simp [fiber]
  have houter :
      μ.toOuterMeasure
          {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card} ≤
        ∑ wanted ∈ high, μ.toOuterMeasure (fiber wanted) := by
    exact (μ.toOuterMeasure.mono hcover).trans
      (MeasureTheory.measure_biUnion_finset_le high fiber)
  have hfiber_ne_top (wanted : I → Bool) :
      μ.toOuterMeasure (fiber wanted) ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top μ (fiber wanted)
  have hsum_ne_top :
      (∑ wanted ∈ high, μ.toOuterMeasure (fiber wanted)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 fun wanted hwanted => hfiber_ne_top wanted
  have hprob_le :
      (μ.toOuterMeasure
          {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
        ∑ wanted ∈ high, (μ.toOuterMeasure (fiber wanted)).toReal := by
    calc
      (μ.toOuterMeasure
          {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
          (∑ wanted ∈ high, μ.toOuterMeasure (fiber wanted)).toReal :=
        ENNReal.toReal_mono hsum_ne_top houter
      _ = ∑ wanted ∈ high, (μ.toOuterMeasure (fiber wanted)).toReal := by
        rw [ENNReal.toReal_sum]
        exact fun wanted _ => hfiber_ne_top wanted
  have hmass_real (wanted : I → Bool) :
      (μ.toOuterMeasure (fiber wanted)).toReal =
        ∏ a : I, if wanted a = true then p else 1 - p := by
    rw [show μ.toOuterMeasure (fiber wanted) =
        ∏ a : I,
          if wanted a = true then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹ by
      simpa [fiber] using hlaw wanted]
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro a ha
    split
    · simp [p]
    · rw [ENNReal.toReal_sub_of_le]
      · simp [p]
      · exact hq_le_one
      · norm_num
  have hmass_nonneg (wanted : I → Bool) :
      0 ≤ ∏ a : I, if wanted a = true then p else 1 - p := by
    apply Finset.prod_nonneg
    intro a ha
    split <;> assumption
  have hhigh_weight (wanted : I → Bool) (hwanted : wanted ∈ high) :
      (∏ a : I, if wanted a = true then p else 1 - p) ≤
        (2 : Real)⁻¹ ^ T *
          ((2 : Real) ^ count wanted *
            ∏ a : I, if wanted a = true then p else 1 - p) := by
    have hTc : T ≤ count wanted := by
      simpa [high] using hwanted
    have hpow2 : (2 : Real) ^ T ≤ (2 : Real) ^ count wanted :=
      pow_le_pow_right₀ (by norm_num) hTc
    have hfactor : 1 ≤ (2 : Real)⁻¹ ^ T * (2 : Real) ^ count wanted := by
      rw [inv_pow]
      exact (one_le_inv_mul₀ (by positivity)).2 hpow2
    calc
      (∏ a : I, if wanted a = true then p else 1 - p) =
          1 * (∏ a : I, if wanted a = true then p else 1 - p) := by ring
      _ ≤ ((2 : Real)⁻¹ ^ T * (2 : Real) ^ count wanted) *
          (∏ a : I, if wanted a = true then p else 1 - p) :=
        mul_le_mul_of_nonneg_right hfactor (hmass_nonneg wanted)
      _ = (2 : Real)⁻¹ ^ T *
          ((2 : Real) ^ count wanted *
            ∏ a : I, if wanted a = true then p else 1 - p) := by ring
  have hcomplete_sum :
      (∑ wanted : I → Bool,
          (2 : Real) ^ count wanted *
            ∏ a : I, if wanted a = true then p else 1 - p) =
        (1 + p) ^ Fintype.card I := by
    have hterm : ∀ wanted : I → Bool,
        (2 : Real) ^ count wanted *
            (∏ a : I, if wanted a = true then p else 1 - p) =
          ∏ a : I, if wanted a = true then 2 * p else 1 - p := by
      intro wanted
      rw [show (2 : Real) ^ count wanted =
          ∏ a : I, if wanted a = true then 2 else 1 by
        dsimp [count]
        rw [Finset.prod_ite]
        simp]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro a ha
      split <;> simp_all
    simp_rw [hterm]
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let E : (I → Bool) ≃ (Fin (Fintype.card I) → Bool) :=
      Equiv.arrowCongr e (Equiv.refl Bool)
    calc
      (∑ wanted : I → Bool,
          ∏ a : I, if wanted a = true then 2 * p else 1 - p) =
          ∑ wanted : Fin (Fintype.card I) → Bool,
            ∏ a : Fin (Fintype.card I),
              if wanted a = true then 2 * p else 1 - p := by
        apply Fintype.sum_equiv E
        intro wanted
        apply Fintype.prod_equiv e
        intro a
        simp [E, e]
      _ = ∏ a : Fin (Fintype.card I),
            ∑ b : Bool, if b = true then 2 * p else 1 - p := by
        exact (Fintype.prod_sum
          (fun (_ : Fin (Fintype.card I)) (b : Bool) =>
            if b = true then 2 * p else 1 - p)).symm
      _ = (1 + p) ^ Fintype.card I := by
        simp [Fintype.univ_bool]
        ring
  calc
    (μ.toOuterMeasure
        {ω | T ≤ (Finset.univ.filter fun a : I => success ω a = true).card}).toReal ≤
        ∑ wanted ∈ high, (μ.toOuterMeasure (fiber wanted)).toReal := hprob_le
    _ = ∑ wanted ∈ high,
          ∏ a : I, if wanted a = true then p else 1 - p := by
      apply Finset.sum_congr rfl
      intro wanted hwanted
      exact hmass_real wanted
    _ ≤ ∑ wanted ∈ high,
          (2 : Real)⁻¹ ^ T *
            ((2 : Real) ^ count wanted *
              ∏ a : I, if wanted a = true then p else 1 - p) := by
      exact Finset.sum_le_sum fun wanted hwanted => hhigh_weight wanted hwanted
    _ = (2 : Real)⁻¹ ^ T *
          ∑ wanted ∈ high,
            ((2 : Real) ^ count wanted *
              ∏ a : I, if wanted a = true then p else 1 - p) := by
      rw [Finset.mul_sum]
    _ ≤ (2 : Real)⁻¹ ^ T *
          ∑ wanted : I → Bool,
            ((2 : Real) ^ count wanted *
              ∏ a : I, if wanted a = true then p else 1 - p) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro wanted hwanted hnot
          positivity
      · positivity
    _ = (2 : Real)⁻¹ ^ T * (1 + p) ^ Fintype.card I := by
      rw [hcomplete_sum]
    _ = (2 : Real)⁻¹ ^ T *
          (1 + (2 : Real)⁻¹ ^ k) ^ Fintype.card I := by rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · finite pattern union and complete base-two moment sum
-/
