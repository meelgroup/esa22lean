import Esa22Copy.Model.Pseudocode
import Mathlib.Data.Finset.Interval

/-!
# Exact restriction patterns for uniform thinning

A uniform subset realizes every prescribed membership pattern on a fixed finite set
with probability `2` to the negative cardinality of that set.
-/

namespace Esa22Copy

open scoped ENNReal

/--
INTERNAL: exact finite counting law for the restriction of `freshSubset` to a fixed
finite set.
-/
theorem freshSubset_restriction_pattern (P : Params) (X : Finset (Item P))
    (wanted : {a // a ∈ X} → Bool) :
    (freshSubset P).toOuterMeasure
        {Y | ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} =
      (((2 : ENNReal) ^ X.card)⁻¹) := by
  classical
  rw [freshSubset, PMF.toOuterMeasure_uniformOfFintype_apply]
  let W : Finset (Item P) :=
    (X.attach.filter fun a => wanted a = true).image Subtype.val
  have hW (a : Item P) :
      a ∈ W ↔ ∃ ha : a ∈ X, wanted ⟨a, ha⟩ = true := by
    simp only [W, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
      true_and, Subtype.exists, exists_and_right, exists_eq_right]
  let e :
      {Y : Finset (Item P) //
          ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} ≃
        {Z : Finset (Item P) // Z ⊆ Xᶜ} :=
    { toFun := fun Y => ⟨Y.1 \ X, by
        intro a ha
        exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp ha).2⟩
      invFun := fun Z => ⟨W ∪ Z.1, by
        intro a
        have hZnot : a.1 ∉ Z.1 := by
          intro ha
          exact (Finset.mem_compl.mp (Z.2 ha)) a.2
        simp only [Finset.mem_union, hZnot, or_false]
        rw [hW]
        simp⟩
      left_inv := fun Y => by
        apply Subtype.ext
        ext a
        by_cases ha : a ∈ X
        · have hsdiff : a ∉ Y.1 \ X := by simp [ha]
          simp only [Finset.mem_union, hsdiff, or_false]
          rw [hW]
          constructor
          · rintro ⟨ha', hwanted⟩
            apply (Y.2 ⟨a, ha⟩).2
            simpa only [Subsingleton.elim ha' ha] using hwanted
          · intro hY
            exact ⟨ha, (Y.2 ⟨a, ha⟩).1 hY⟩
        · simp [W, ha]
      right_inv := fun Z => by
        apply Subtype.ext
        ext a
        by_cases ha : a ∈ X
        · have hZnot : a ∉ Z.1 := by
            intro hza
            exact (Finset.mem_compl.mp (Z.2 hza)) ha
          simp [ha, hZnot]
        · simp [W, ha] }
  have hpatterns :
      Fintype.card {Y : Finset (Item P) //
          ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} =
        2 ^ (P.n - X.card) := by
    rw [Fintype.card_congr e]
    rw [Fintype.card_subtype]
    have heq :
        Finset.univ.filter (fun Z : Finset (Item P) => Z ⊆ Xᶜ) =
          Xᶜ.powerset := by
      ext Z
      simp
    rw [heq, Finset.card_powerset, Finset.card_compl]
    simp only [Fintype.card_fin]
  change
    ((Fintype.card {Y : Finset (Item P) //
        ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} : Nat) : ENNReal) /
        (Fintype.card (Finset (Item P)) : ENNReal) =
      (((2 : ENNReal) ^ X.card)⁻¹)
  rw [hpatterns, Fintype.card_finset]
  have hItem : Fintype.card (Item P) = P.n := by
    change Fintype.card (Fin P.n) = P.n
    exact Fintype.card_fin P.n
  rw [hItem]
  have hcard : X.card ≤ P.n := by
    rw [← hItem]
    exact Finset.card_le_univ X
  have htr : ((((2 ^ (P.n - X.card) : Nat) : ENNReal) /
      ((2 ^ P.n : Nat) : ENNReal))).toReal =
      (((2 : ENNReal) ^ X.card)⁻¹).toReal := by
    simp only [ENNReal.toReal_div, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [pow_sub₀ (2 : Real) (by norm_num) hcard]
    field_simp
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp htr with hxy | hbad | hbad
  · exact hxy
  · exact False.elim (by simpa using hbad.2)
  · exact False.elim ((ENNReal.div_ne_top (by simp) (by positivity)) hbad.1)

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r7 · proved · counted exact restriction patterns by an equivalence with subsets
  of the complement of the constrained set
-/
