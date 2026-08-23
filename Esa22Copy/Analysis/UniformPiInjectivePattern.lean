import Esa22Copy.Model.Pseudocode

/-!
# Uniform patterns at injective coordinates

Finite counting shows that constraints on pairwise distinct coordinates of a uniform
function have the product law, without invoking a separate independence API.
-/

open scoped BigOperators ENNReal

namespace Esa22Copy

/--
INTERNAL: generic finite-counting law used to isolate the independence bookkeeping.
-/
theorem uniform_pi_injective_pattern
    {I J β : Type*} [Fintype I] [Fintype J] [Fintype β] [Nonempty β]
    [DecidableEq J]
    (controller : I → J) (hcontroller : Function.Injective controller)
    (Q : I → β → Prop) [∀ a, DecidablePred (Q a)] :
    (PMF.uniformOfFintype (J → β)).toOuterMeasure
        {f | ∀ a : I, Q a (f (controller a))} =
      ∏ a : I, (Fintype.card {b : β // Q a b} : ENNReal) / Fintype.card β := by
  classical
  let R : J → β → Prop := fun j b ↦ ∀ a, controller a = j → Q a b
  let eventEquiv :
      {f : J → β // ∀ a : I, Q a (f (controller a))} ≃
        ∀ j : J, {b : β // R j b} :=
    { toFun := fun f j ↦ ⟨f.1 j, fun a ha ↦ ha ▸ f.2 a⟩
      invFun := fun g ↦ ⟨fun j ↦ (g j).1, fun a ↦ (g (controller a)).2 a rfl⟩
      left_inv := fun f ↦ by ext j; rfl
      right_inv := fun g ↦ by funext j; apply Subtype.ext; rfl }
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hcard :
      Fintype.card ↑({f : J → β | ∀ a : I, Q a (f (controller a))} : Set (J → β)) =
        Fintype.card (∀ j : J, {b : β // R j b}) :=
    Fintype.card_congr eventEquiv
  rw [hcard, Fintype.card_pi, Fintype.card_pi]
  simp only [Nat.cast_prod]
  rw [← ENNReal.prod_div_distrib_of_ne_top (s := Finset.univ)
    (f := fun j ↦ (Fintype.card {b : β // R j b} : ENNReal))
    (g := fun _ : J ↦ (Fintype.card β : ENNReal)) (by simp)]
  let image : Finset J := Finset.univ.image controller
  have hoff (j : J) (hj : j ∉ image) :
      (Fintype.card {b : β // R j b} : ENNReal) / Fintype.card β = 1 := by
    have hvac : ∀ b : β, R j b := by
      intro b a ha
      exfalso
      apply hj
      simp [image, ← ha]
    have heq : Fintype.card {b : β // R j b} = Fintype.card β := by
      exact Fintype.card_congr
        ((Equiv.subtypeEquivRight fun b ↦ by
            constructor
            · intro _
              trivial
            · intro _
              exact hvac b).trans (Equiv.Set.univ β))
    rw [heq]
    apply ENNReal.div_self
    · exact_mod_cast Fintype.card_ne_zero
    · exact ENNReal.natCast_ne_top _
  have hlocal (a : I) :
      Fintype.card {b : β // R (controller a) b} =
        Fintype.card {b : β // Q a b} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro b
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have : a' = a := hcontroller ha'
      simpa [this] using h
  calc
    ∏ j : J, (Fintype.card {b : β // R j b} : ENNReal) / Fintype.card β =
        ∏ j ∈ image, (Fintype.card {b : β // R j b} : ENNReal) / Fintype.card β := by
          symm
          apply Finset.prod_subset (by simp [image])
          intro j _ hj
          exact hoff j hj
    _ = ∏ a : I, (Fintype.card {b : β // R (controller a) b} : ENNReal) /
          Fintype.card β := by
          exact Finset.prod_image (fun _ _ _ _ h ↦ hcontroller h)
    _ = ∏ a : I, (Fintype.card {b : β // Q a b} : ENNReal) / Fintype.card β := by
          apply Finset.prod_congr rfl
          intro a _
          rw [hlocal a]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · counted constrained functions coordinatewise and removed vacuous factors
-/
