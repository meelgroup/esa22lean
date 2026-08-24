import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# From point masses to an event probability

This is the finite counting step which sums a product-form point-mass expansion over an
arbitrary event in the output space.
-/

namespace Esa22Copy

open scoped BigOperators ENNReal Classical

/--
INTERNAL (`bernoulliSum_twoSidedChernoff`): a pointwise finite-mixture formula for a PMF
induces the corresponding finite weighted sum for every outer-measure event.
-/
theorem bernoulliSum_twoSidedChernoff_outerMeasure_of_mass_expansion
    {k : Nat} (p : Fin k → Set.Icc (0 : Real) 1) (ν : PMF Real)
    (hmass : ∀ x : Real,
      ν x =
        ∑ wanted : Fin k → Bool,
          (∏ i : Fin k,
            if wanted i then ENNReal.ofReal (p i : Real)
            else ENNReal.ofReal (1 - (p i : Real))) *
          PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0) x)
    (S : Set Real) :
    ν.toOuterMeasure S =
      ∑ wanted : Fin k → Bool,
        (∏ i : Fin k,
          if wanted i then ENNReal.ofReal (p i : Real)
          else ENNReal.ofReal (1 - (p i : Real))) *
        if (∑ i : Fin k, if wanted i then (1 : Real) else 0) ∈ S then 1 else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply]
  calc
    (∑' x : Real, S.indicator ν x) =
        ∑' x : Real,
          ∑ wanted : Fin k → Bool,
            (∏ i : Fin k,
              if wanted i then ENNReal.ofReal (p i : Real)
              else ENNReal.ofReal (1 - (p i : Real))) *
            S.indicator
              (PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0)) x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
        exact hmass x
      · simp only [Set.indicator_of_notMem hx, mul_zero, Finset.sum_const_zero]
    _ = ∑' x : Real,
          ∑' wanted : Fin k → Bool,
            (∏ i : Fin k,
              if wanted i then ENNReal.ofReal (p i : Real)
              else ENNReal.ofReal (1 - (p i : Real))) *
            S.indicator
              (PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0)) x := by
      apply tsum_congr
      intro x
      rw [tsum_fintype]
    _ = ∑' wanted : Fin k → Bool,
          ∑' x : Real,
            (∏ i : Fin k,
              if wanted i then ENNReal.ofReal (p i : Real)
              else ENNReal.ofReal (1 - (p i : Real))) *
            S.indicator
              (PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0)) x :=
      ENNReal.tsum_comm
    _ = ∑' wanted : Fin k → Bool,
          (∏ i : Fin k,
            if wanted i then ENNReal.ofReal (p i : Real)
            else ENNReal.ofReal (1 - (p i : Real))) *
          ∑' x : Real,
            S.indicator
              (PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0)) x := by
      apply tsum_congr
      intro wanted
      exact ENNReal.tsum_mul_left
    _ = ∑ wanted : Fin k → Bool,
          (∏ i : Fin k,
            if wanted i then ENNReal.ofReal (p i : Real)
            else ENNReal.ofReal (1 - (p i : Real))) *
          if (∑ i : Fin k, if wanted i then (1 : Real) else 0) ∈ S then 1 else 0 := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro wanted _
      rw [← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_pure_apply]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · expanded the event indicator, commuted the two ENNReal sums, and
  evaluated each pure atom with `PMF.toOuterMeasure_pure_apply`
-/
