import Esa22Copy.Model.Pseudocode
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cardinality of accepted bit blocks

An accepted block has a forced true prefix of length `k` and an arbitrary Boolean tail.
-/

namespace Esa22Copy

/--
INTERNAL: concrete accepted-block count behind the level-`k` sampling rate.
-/
theorem acceptsAt_true_card (P : Params) (k : Nat) (hk : k ≤ P.m) :
    Fintype.card {bits : BitBlock P // acceptsAt k bits = true} =
      2 ^ (P.m + 1 - k) := by
  classical
  have acceptsAt_true_iff (bits : BitBlock P) :
      acceptsAt k bits = true ↔
        ∀ i : Fin k, bits (Fin.castLE (hk.trans (Nat.le_succ P.m)) i) = true := by
    have hk' : k ≤ P.m + 1 := hk.trans (Nat.le_succ P.m)
    rw [acceptsAt, if_pos hk', ← Fin.ofFn_take_eq_take_ofFn hk' bits,
      List.all_eq_true, List.forall_mem_ofFn_iff]
    rfl
  let d := P.m + 1 - k
  have hk' : k ≤ P.m + 1 := hk.trans (Nat.le_succ P.m)
  have hd : k + d = P.m + 1 := Nat.add_sub_of_le hk'
  let castE : (Fin (k + d) → Bool) ≃ BitBlock P :=
    Equiv.piCongrLeft (fun _ : Fin (P.m + 1) ↦ Bool) (finCongr hd)
  let E : (Fin k → Bool) × (Fin d → Bool) ≃ BitBlock P :=
    (Fin.appendEquiv k d).trans castE
  have hE (bits : BitBlock P) :
      acceptsAt k bits = true ↔ ∀ i : Fin k, (E.symm bits).1 i = true := by
    rw [acceptsAt_true_iff bits]
    change (∀ i : Fin k, bits (Fin.castLE hk' i) = true) ↔
      ∀ i : Fin k, bits (Fin.cast hd (Fin.castAdd d i)) = true
    constructor
    · intro h i
      have hi : Fin.cast hd (Fin.castAdd d i) = Fin.castLE hk' i := by
        apply Fin.ext
        rfl
      rw [hi]
      exact h i
    · intro h i
      have hi : Fin.cast hd (Fin.castAdd d i) = Fin.castLE hk' i := by
        apply Fin.ext
        rfl
      rw [← hi]
      exact h i
  let acceptedEquiv :
      {bits : BitBlock P // acceptsAt k bits = true} ≃ (Fin d → Bool) :=
    { toFun := fun bits ↦ (E.symm bits.1).2
      invFun := fun tail ↦ ⟨E (fun _ ↦ true, tail), (hE _).2 (by simp [E])⟩
      left_inv := fun bits ↦ by
        apply Subtype.ext
        change E (fun _ ↦ true, (E.symm bits.1).2) = bits.1
        calc
          E (fun _ ↦ true, (E.symm bits.1).2) = E (E.symm bits.1) := by
            congr 1
            apply Prod.ext
            · funext i
              exact (hE bits.1).1 bits.2 i |>.symm
            · rfl
          _ = bits.1 := E.apply_symm_apply _
      right_inv := fun tail ↦ by simp }
  rw [Fintype.card_congr acceptedEquiv, Fintype.card_pi_const, Fintype.card_bool]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · split each block into its forced prefix and arbitrary Boolean tail
-/
