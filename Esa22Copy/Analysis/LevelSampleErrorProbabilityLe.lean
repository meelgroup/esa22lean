import Esa22Copy.Analysis.FixedLevelErrorEvent
import Esa22Copy.Analysis.BernoulliPatternChernoffRelErr
import Esa22Copy.Analysis.FixedLevelErrorEventMembership

/-!
# Multiplicative concentration for a fixed level sample

Independent membership of the distinct stream items gives a binomial sample of
mean `F0 · 2⁻ᵏ`.  This file packages the two-sided multiplicative tail needed by
the relaxed estimator.
-/

namespace Esa22Copy

/--
PAPER: esa22-final.tex:721-751, the fixed-level two-sided Chernoff estimate in
Claim `lm:error-fail`.
-/
theorem levelSample_error_probability_le (P : Params) (A : Stream P)
    (k : Nat) (hkpos : 0 < k) (hk : k ≤ P.m) :
    ((freshLevelCoins P).toOuterMeasure (fixedLevelErrorEvent P A k)).toReal ≤
      2 * Real.exp
        (-(P.eps ^ 2 *
          ((F0 A : Real) * (1 / 2 : Real) ^ k)) / 3) := by
  let I := {a // a ∈ prefixDistinct A (Fin.last P.m)}
  let X : LevelCoins P → I → Bool := fun coins a =>
    decide (a.1 ∈ levelSample coins A k (Fin.last P.m))
  have hpattern : ∀ wanted : I → Bool,
      (freshLevelCoins P).toOuterMeasure
          {coins | ∀ a : I, X coins a = wanted a} =
        ∏ a : I,
          if wanted a then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹ := by
    intro wanted
    rw [show {coins | ∀ a : I, X coins a = wanted a} =
        {coins | ∀ a : I,
          (a.1 ∈ levelSample coins A k (Fin.last P.m)) ↔ wanted a = true} by
      ext coins
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h a
        have ha := h a
        cases hw : wanted a <;> simp [X, hw] at ha ⊢ <;> exact ha
      · intro h a
        have ha := h a
        cases hw : wanted a <;> simp [X, hw] at ha ⊢ <;> exact ha]
    simpa [I] using
      levelSample_independent_membership P A (Fin.last P.m) k hk wanted
  have hprefix : prefixDistinct A (Fin.last P.m) = distinctSet A := by
    ext a
    simp [prefixDistinct, distinctSet]
  have hcard : Fintype.card I = F0 A := by
    rw [show Fintype.card I = (prefixDistinct A (Fin.last P.m)).card by
      simp [I], hprefix]
    rfl
  rw [fixedLevelErrorEvent_eq_membership_error]
  simpa [I, X, hcard] using
    bernoulli_pattern_chernoff_relErr
      (freshLevelCoins P) X k P.eps P.heps.1 P.heps.2.le hpattern

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · reduced · closed the algorithm adapter using complete-pattern concentration and
  deterministic final-prefix normalization
* r2 · open · isolated the missing multiplicative Bernoulli concentration argument
-/
