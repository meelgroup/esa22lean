import Esa22Copy.Interface.Pseudocode

/-!
# Deferred fair bits at an injective frontier

This is the finite deferred-decisions statement needed when the relaxed algorithm's
current level is adaptive.  An event insensitive to an injectively selected family of
table cells is independent of any prescribed Boolean pattern on those cells.
-/

namespace Esa22Copy

/--
INTERNAL: injectively selected frontier bits remain jointly fair outside an event that
does not inspect them.
-/
theorem uniform_table_fresh_frontier (P : Params) {I : Type*} [Fintype I]
    (controller : I → Fin P.m) (hcontroller : Function.Injective controller)
    (k : Nat) (hk : k ≤ P.m) (E : Set (LevelCoins P)) (wanted : I → Bool)
    (hE : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
        (∀ a : I, j ≠ controller a ∨ q ≠ ⟨k, Nat.lt_succ_of_le hk⟩) → x j q = y j q) →
      (x ∈ E ↔ y ∈ E)) :
    (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure
        {coins | coins ∈ E ∧
          ∀ a : I, coins (controller a) ⟨k, Nat.lt_succ_of_le hk⟩ = wanted a} =
      (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure E *
        (((2 : ENNReal) ^ Fintype.card I)⁻¹) := by
  classical
  let qk : Fin (P.m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  let put : (I → Bool) → LevelCoins P → LevelCoins P := fun w coins j q ↦
    if h : ∃ a : I, controller a = j ∧ q = qk then w (Classical.choose h)
    else coins j q
  have put_controlled (w : I → Bool) (coins : LevelCoins P) (a : I) :
      put w coins (controller a) qk = w a := by
    simp only [put]
    split
    next h =>
      congr 1
      apply hcontroller
      exact (Classical.choose_spec h).1
    next h =>
      exact False.elim (h ⟨a, rfl, trivial⟩)
  have put_uncontrolled (w : I → Bool) (coins : LevelCoins P)
      (j : Fin P.m) (q : Fin (P.m + 1))
      (haway : ∀ a : I, j ≠ controller a ∨ q ≠ qk) :
      put w coins j q = coins j q := by
    simp only [put]
    split
    next h =>
      obtain ⟨a, ha, hq⟩ := h
      exact False.elim ((haway a).elim (fun hn ↦ hn ha.symm) (fun hn ↦ hn hq))
    next _ => rfl
  have put_mem_iff (w : I → Bool) (coins : LevelCoins P) :
      coins ∈ E ↔ put w coins ∈ E := by
    apply hE
    intro j q haway
    symm
    apply put_uncontrolled
    simpa only [qk] using haway
  have put_put (u v : I → Bool) (coins : LevelCoins P) :
      put u (put v coins) = put u coins := by
    funext j q
    simp only [put]
    split <;> rfl
  have put_fixed (w : I → Bool) (coins : LevelCoins P)
      (hfrontier : ∀ a : I, coins (controller a) qk = w a) :
      put w coins = coins := by
    funext j q
    simp only [put]
    split
    next h =>
      have hs := Classical.choose_spec h
      calc
        w (Classical.choose h) = coins (controller (Classical.choose h)) qk :=
          (hfrontier (Classical.choose h)).symm
        _ = coins j q := by rw [hs.1, hs.2]
    next _ => rfl
  let Good : Set (LevelCoins P) :=
    {coins | coins ∈ E ∧ ∀ a : I, coins (controller a) qk = wanted a}
  let frontierEquiv : {coins : LevelCoins P // coins ∈ E} ≃
      (I → Bool) × {coins : LevelCoins P // coins ∈ Good} :=
    { toFun := fun coins ↦
        (fun a ↦ coins.1 (controller a) qk,
          ⟨put wanted coins.1,
            (put_mem_iff wanted coins.1).1 coins.2,
            fun a ↦ put_controlled wanted coins.1 a⟩)
      invFun := fun pair ↦
        ⟨put pair.1 pair.2.1, (put_mem_iff pair.1 pair.2.1).1 pair.2.2.1⟩
      left_inv := fun coins ↦ by
        apply Subtype.ext
        change put (fun a ↦ coins.1 (controller a) qk) (put wanted coins.1) = coins.1
        calc
          put (fun a ↦ coins.1 (controller a) qk) (put wanted coins.1) =
              put (fun a ↦ coins.1 (controller a) qk) coins.1 :=
            put_put (fun a : I ↦ coins.1 (controller a) qk) wanted coins.1
          _ = coins.1 :=
            put_fixed (fun a : I ↦ coins.1 (controller a) qk) coins.1 (fun _ ↦ rfl)
      right_inv := fun pair ↦ by
        apply Prod.ext
        · funext a
          exact put_controlled pair.1 pair.2.1 a
        · apply Subtype.ext
          change put wanted (put pair.1 pair.2.1) = pair.2.1
          exact (put_put wanted pair.1 pair.2.1).trans
            (put_fixed wanted pair.2.1 pair.2.2.2) }
  have hcard : Fintype.card {coins : LevelCoins P // coins ∈ E} =
      2 ^ Fintype.card I * Fintype.card {coins : LevelCoins P // coins ∈ Good} := by
    rw [Fintype.card_congr frontierEquiv, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_bool]
  change (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure Good =
    (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure E *
      (((2 : ENNReal) ^ Fintype.card I)⁻¹)
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [hcard]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_eq_inv_mul]
  have hcancel : (2 : ENNReal) ^ Fintype.card I *
      ((2 : ENNReal) ^ Fintype.card I)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp) (by simp)
  calc
    (Fintype.card (LevelCoins P) : ENNReal)⁻¹ *
          Fintype.card {coins : LevelCoins P // coins ∈ Good} =
        ((Fintype.card (LevelCoins P) : ENNReal)⁻¹ *
          Fintype.card {coins : LevelCoins P // coins ∈ Good}) * 1 := by rw [mul_one]
    _ = ((Fintype.card (LevelCoins P) : ENNReal)⁻¹ *
          Fintype.card {coins : LevelCoins P // coins ∈ Good}) *
          ((2 : ENNReal) ^ Fintype.card I *
            ((2 : ENNReal) ^ Fintype.card I)⁻¹) := by rw [hcancel]
    _ = ((Fintype.card (LevelCoins P) : ENNReal)⁻¹ *
          ((2 : ENNReal) ^ Fintype.card I *
            Fintype.card {coins : LevelCoins P // coins ∈ Good})) *
          ((2 : ENNReal) ^ Fintype.card I)⁻¹ := by ac_rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · normalized controlled cells and counted the resulting finite equivalence
* r1 · open · isolated finite deferred decisions from the adaptive coupling
-/
