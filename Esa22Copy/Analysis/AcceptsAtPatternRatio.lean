import Esa22Copy.Analysis.AcceptsAtTrueCard

/-!
# Acceptance-pattern ratio

The accepted and rejected block counts normalize respectively to `2⁻ᵏ` and its complement.
-/

open scoped ENNReal

namespace Esa22Copy

/--
INTERNAL: packages accepted and rejected block counts in the exact factor used by the product law.
-/
theorem acceptsAt_pattern_ratio (P : Params) (k : Nat) (hk : k ≤ P.m)
    (wanted : Bool) :
    (Fintype.card {bits : BitBlock P //
        ((acceptsAt k bits = true) = (wanted = true))} : ENNReal) /
      Fintype.card (BitBlock P) =
      if wanted then ((2 : ENNReal) ^ k)⁻¹ else 1 - ((2 : ENNReal) ^ k)⁻¹ := by
  classical
  have ennreal_pow_ratio (k d : Nat) :
      (2 : ENNReal) ^ d / (2 : ENNReal) ^ (k + d) = ((2 : ENNReal) ^ k)⁻¹ := by
    rw [pow_add, ENNReal.div_eq_inv_mul]
    have hinv : ((2 : ENNReal) ^ k * (2 : ENNReal) ^ d)⁻¹ =
        ((2 : ENNReal) ^ k)⁻¹ * ((2 : ENNReal) ^ d)⁻¹ := by
      apply ENNReal.mul_inv
      · left
        norm_num
      · left
        simp
    rw [hinv]
    have hcancel : ((2 : ENNReal) ^ d)⁻¹ * (2 : ENNReal) ^ d = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by simp)
    calc
      ((2 : ENNReal) ^ k)⁻¹ * ((2 : ENNReal) ^ d)⁻¹ * (2 : ENNReal) ^ d =
          ((2 : ENNReal) ^ k)⁻¹ * (((2 : ENNReal) ^ d)⁻¹ * (2 : ENNReal) ^ d) := by
            rw [mul_assoc]
      _ = ((2 : ENNReal) ^ k)⁻¹ := by rw [hcancel, mul_one]
  let d := P.m + 1 - k
  have hk' : k ≤ P.m + 1 := hk.trans (Nat.le_succ P.m)
  have hd : k + d = P.m + 1 := Nat.add_sub_of_le hk'
  have htotal : Fintype.card (BitBlock P) = 2 ^ (P.m + 1) := by
    rw [Fintype.card_pi_const, Fintype.card_bool]
  have hacc := acceptsAt_true_card P k hk
  cases wanted with
  | true =>
      simp
      rw [hacc]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      change (2 : ENNReal) ^ d / (2 : ENNReal) ^ (P.m + 1) = _
      rw [← hd]
      exact ennreal_pow_ratio k d
  | false =>
      simp
      have hreject :
          Fintype.card {bits : BitBlock P // acceptsAt k bits = false} =
            Fintype.card {bits : BitBlock P // ¬ acceptsAt k bits = true} := by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro bits
        simp
      rw [hreject]
      rw [Fintype.card_subtype_compl (fun bits : BitBlock P ↦ acceptsAt k bits = true)]
      rw [htotal, hacc]
      rw [show P.m + 1 - k = d from rfl]
      rw [← hd]
      rw [ENNReal.natCast_sub]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [ENNReal.sub_div]
      · rw [ENNReal.div_self (by norm_num) (by simp)]
        rw [ennreal_pow_ratio]
      · intro _ _
        norm_num

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · normalized the accepted count and its finite complement in `ENNReal`
-/
