import Esa22Copy.Model.Pseudocode
import Mathlib.Data.Finset.Interval

/-!
# Probability that thinning retains a fixed set

Uniform thinning retains every member of a fixed finite set with probability
`2` to the negative cardinality of that set.
-/

namespace Esa22Copy

open scoped ENNReal

/--
INTERNAL: finite counting fact for the thinning operation used by `step`.
-/
theorem freshSubset_superset_probability (P : Params) (X : Finset (Item P)) :
    (freshSubset P).toOuterMeasure {Y | X ⊆ Y} =
      ((2 : ℝ≥0∞)⁻¹) ^ X.card := by
  classical
  rw [freshSubset, PMF.toOuterMeasure_uniformOfFintype_apply]
  let e : {Y : Finset (Item P) // X ⊆ Y} ≃
      {Z : Finset (Item P) // Z ⊆ Xᶜ} :=
  { toFun := fun Y => ⟨Y.1 \ X, by
      intro a ha
      simp only [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp ha).2⟩
    invFun := fun Z => ⟨X ∪ Z.1, Finset.subset_union_left⟩
    left_inv := fun Y => by
      apply Subtype.ext
      exact Finset.union_sdiff_of_subset Y.2
    right_inv := fun Z => by
      apply Subtype.ext
      apply Finset.union_sdiff_cancel_left
      exact Finset.disjoint_left.2 fun a haX haZ =>
        (Finset.mem_compl.mp (Z.2 haZ)) haX }
  have hsupersets : Fintype.card {Y : Finset (Item P) // X ⊆ Y} =
      2 ^ (P.n - X.card) := by
    rw [Fintype.card_congr e]
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun Z : Finset (Item P) => Z ⊆ Xᶜ) =
        (Xᶜ).powerset := by
      ext Z
      simp
    rw [heq, Finset.card_powerset, Finset.card_compl]
    simp only [Fintype.card_fin]
  change ((Fintype.card {Y : Finset (Item P) // X ⊆ Y} : Nat) : ℝ≥0∞) /
      (Fintype.card (Finset (Item P)) : ℝ≥0∞) =
    ((2 : ℝ≥0∞)⁻¹) ^ X.card
  rw [hsupersets, Fintype.card_finset]
  have hItem : Fintype.card (Item P) = P.n := by
    change Fintype.card (Fin P.n) = P.n
    exact Fintype.card_fin P.n
  rw [hItem]
  change (((2 ^ (P.n - X.card) : Nat) : ℝ≥0∞) /
      ((2 ^ P.n : Nat) : ℝ≥0∞)) = ((2 : ℝ≥0∞)⁻¹) ^ X.card
  have hcard : X.card ≤ P.n := by
    rw [← hItem]
    exact Finset.card_le_univ X
  have htr : ((((2 ^ (P.n - X.card) : Nat) : ℝ≥0∞) /
      ((2 ^ P.n : Nat) : ℝ≥0∞))).toReal =
      (((2 : ℝ≥0∞)⁻¹) ^ X.card).toReal := by
    simp only [ENNReal.toReal_div, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [pow_sub₀ (2 : Real) (by norm_num) hcard]
    field_simp
    rw [← mul_pow]
    norm_num
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp htr with hxy | hbad | hbad
  · exact hxy
  · exact False.elim (by simpa using hbad.2)
  · exact False.elim ((ENNReal.div_ne_top (by simp) (by positivity)) hbad.1)

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · counted supersets via the equivalence with subsets of the complement
-/
