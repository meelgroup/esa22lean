import Esa22Copy.Model.Pseudocode

/-!
# A fresh row after a causal represented state

This module isolates the first deferred-decisions calculation in a represented-state
successor: a state determined by earlier table rows is independent of the next row.
-/

namespace Esa22Copy

/--
INTERNAL: exposing an unused coin-table row after a causal represented state has the
same joint law as drawing a fresh block after drawing the state.
-/
theorem causalState_refresh_distribution (P : Params) (a : Item P)
    (r : Nat) (hr : r < P.m)
    (representedState : LevelCoins P → RelaxedState P)
    (hcausalRow : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
        j.val < r → x j q = y j q) →
      representedState x = representedState y) :
    (PMF.uniformOfFintype (LevelCoins P)).map
        (fun coins ↦
          let s := representedState coins
          (s, refresh a s.level (coins ⟨r, hr⟩) s.samples)) =
      ((PMF.uniformOfFintype (LevelCoins P)).map representedState).bind
        (fun s ↦ (freshBlock P).map
          (fun bits ↦ (s, refresh a s.level bits s.samples))) := by
  classical
  let row : Fin P.m := ⟨r, hr⟩
  have hstate_update : ∀ (coins : LevelCoins P) (bits : BitBlock P),
      representedState (Function.update coins row bits) = representedState coins := by
    intro coins bits
    apply hcausalRow
    intro j q hj
    rw [Function.update_of_ne]
    intro hEq
    subst j
    exact (Nat.lt_irrefl r hj).elim
  have uniform_product {A B : Type} [Fintype A] [Nonempty A]
      [Fintype B] [Nonempty B] :
      (PMF.uniformOfFintype A).bind
          (fun x ↦ (PMF.uniformOfFintype B).map (fun y ↦ (x, y))) =
        PMF.uniformOfFintype (A × B) := by
    apply PMF.ext
    intro z
    rw [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
    rw [Finset.sum_eq_single z.1]
    · rw [Finset.sum_eq_single z.2]
      · simp only [Prod.mk.eta, if_true, Fintype.card_prod]
        rw [Nat.cast_mul]
        exact (ENNReal.mul_inv
          (a := (Fintype.card A : ENNReal))
          (b := (Fintype.card B : ENNReal)) (by simp) (by simp)).symm
      · intro y _ hy
        simp only [ite_eq_right_iff]
        intro hz
        exact (hy (congrArg Prod.snd hz).symm).elim
      · simp
    · intro x _ hx
      have hz :
          (∑ y, if z = (x, y) then
            (↑(Fintype.card B) : ENNReal)⁻¹ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        simp only [ite_eq_right_iff]
        intro hxy
        exact (hx (congrArg Prod.fst hxy).symm).elim
      rw [hz, mul_zero]
    · simp
  have uniform_equiv {A : Type} [Fintype A] [Nonempty A] (e : A ≃ A) :
      (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype A := by
    apply PMF.ext
    intro y
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (e.symm y)]
    · simp [PMF.uniformOfFintype_apply]
    · intro x _ hx
      simp only [ite_eq_right_iff]
      intro hxy
      exact (hx (e.injective (by simpa using hxy.symm))).elim
    · simp
  let pairLaw : PMF (LevelCoins P × BitBlock P) :=
    (PMF.uniformOfFintype (LevelCoins P)).bind
      (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
        (fun bits ↦ (coins, bits)))
  let swapFun : LevelCoins P × BitBlock P → LevelCoins P × BitBlock P :=
    fun x ↦ (Function.update x.1 row x.2, x.1 row)
  have swap_involutive : Function.Involutive swapFun := by
    rintro ⟨coins, bits⟩
    apply Prod.ext
    · funext j
      by_cases h : j = row
      · subst j
        simp [swapFun]
      · simp [swapFun, Function.update_of_ne h]
    · simp [swapFun]
  let swapEquiv : (LevelCoins P × BitBlock P) ≃
      (LevelCoins P × BitBlock P) :=
    ⟨swapFun, swapFun, swap_involutive, swap_involutive⟩
  have pairLaw_uniform : pairLaw =
      PMF.uniformOfFintype (LevelCoins P × BitBlock P) := by
    exact uniform_product
  have pairLaw_swap : pairLaw.map swapEquiv = pairLaw := by
    rw [pairLaw_uniform, uniform_equiv]
  have hresample :
      (PMF.uniformOfFintype (LevelCoins P)).bind
          (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
            (fun bits ↦ Function.update coins row bits)) =
        PMF.uniformOfFintype (LevelCoins P) := by
    calc
      _ = pairLaw.map (fun x ↦ Function.update x.1 row x.2) := by
        rw [PMF.map_bind]
        congr 1
        funext coins
        rw [PMF.map_comp]
        rfl
      _ = (pairLaw.map swapEquiv).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
      _ = pairLaw.map Prod.fst := by rw [pairLaw_swap]
      _ = PMF.uniformOfFintype (LevelCoins P) := by
        dsimp only [pairLaw]
        rw [PMF.map_bind]
        simp_rw [PMF.map_comp]
        change (PMF.uniformOfFintype (LevelCoins P)).bind
          (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
            (Function.const (BitBlock P) coins)) = _
        simp_rw [PMF.map_const]
        exact PMF.bind_pure _
  let F : LevelCoins P → RelaxedState P × Finset (Item P) :=
    fun coins ↦
      let s := representedState coins
      (s, refresh a s.level (coins row) s.samples)
  change (PMF.uniformOfFintype (LevelCoins P)).map F = _
  calc
    _ = ((PMF.uniformOfFintype (LevelCoins P)).bind
          (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
            (fun bits ↦ Function.update coins row bits))).map F := by
      rw [hresample]
    _ = (PMF.uniformOfFintype (LevelCoins P)).bind
          (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
            (fun bits ↦ F (Function.update coins row bits))) := by
      rw [PMF.map_bind]
      congr 1
      funext coins
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (LevelCoins P)).bind
          (fun coins ↦ (PMF.uniformOfFintype (BitBlock P)).map
            (fun bits ↦
              let s := representedState coins
              (s, refresh a s.level bits s.samples))) := by
      congr 1
      funext coins
      congr 1
      funext bits
      dsimp only [F]
      rw [hstate_update]
      simp only [Function.update_self]
    _ = ((PMF.uniformOfFintype (LevelCoins P)).map representedState).bind
          (fun s ↦ (freshBlock P).map
            (fun bits ↦ (s, refresh a s.level bits s.samples))) := by
      rw [PMF.bind_map]
      rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · proved · resampled the unused row via a uniform-product involution
* r10 · reduced · isolated the unused-row half of the crossing-update law
-/
