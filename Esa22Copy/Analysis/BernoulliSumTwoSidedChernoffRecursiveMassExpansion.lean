import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Algebra.BigOperators.Fin

/-!
# Point masses of a recursively sampled Bernoulli sum

This isolates the induction which identifies the recursive `PMF.bind` construction with
the finite enumeration of all Boolean outcome vectors.
-/

namespace Esa22Copy

open scoped BigOperators ENNReal

/--
INTERNAL: bookkeeping for `bernoulliSum_twoSidedChernoff`; a recursively bound family of
Bernoulli variables has the expected finite product expansion at every output point.
-/
theorem bernoulliSum_twoSidedChernoff_recursive_mass_expansion
    (coin : Set.Icc (0 : Real) 1 → PMF Bool)
    (sumPMF : (k : Nat) → (Fin k → Set.Icc (0 : Real) 1) → PMF Real)
    (hcoin : ∀ q b,
      coin q b = if b then ENNReal.ofReal (q : Real)
        else ENNReal.ofReal (1 - (q : Real)))
    (hzero : ∀ p : Fin 0 → Set.Icc (0 : Real) 1, sumPMF 0 p = PMF.pure 0)
    (hsucc : ∀ (k : Nat) (p : Fin (k + 1) → Set.Icc (0 : Real) 1),
      sumPMF (k + 1) p =
        (coin (p 0)).bind fun b =>
          (sumPMF k fun i => p i.succ).bind fun s =>
            PMF.pure ((if b then 1 else 0) + s))
    (k : Nat) (p : Fin k → Set.Icc (0 : Real) 1) (x : Real) :
    sumPMF k p x =
      ∑ wanted : Fin k → Bool,
        (∏ i : Fin k,
          if wanted i then ENNReal.ofReal (p i : Real)
          else ENNReal.ofReal (1 - (p i : Real))) *
        PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0) x := by
  classical
  induction k generalizing x with
  | zero =>
      rw [hzero]
      simp
  | succ k ih =>
      rw [hsucc, PMF.bind_apply]
      simp only [PMF.bind_apply]
      simp_rw [ih]
      have hpure (b : Bool) (wanted : Fin k → Bool) :
          ∑' s : Real,
              ((∏ i : Fin k,
                  if wanted i then ENNReal.ofReal (p i.succ : Real)
                  else ENNReal.ofReal (1 - (p i.succ : Real))) *
                PMF.pure (∑ i : Fin k, if wanted i then (1 : Real) else 0) s) *
                PMF.pure ((if b then (1 : Real) else 0) + s) x =
            (∏ i : Fin k,
                if wanted i then ENNReal.ofReal (p i.succ : Real)
                else ENNReal.ofReal (1 - (p i.succ : Real))) *
              PMF.pure
                ((if b then (1 : Real) else 0) +
                  ∑ i : Fin k, if wanted i then (1 : Real) else 0) x := by
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (∑ i : Fin k, if wanted i then (1 : Real) else 0)]
        · simp
        · intro s hs
          rw [PMF.pure_apply_of_ne _ _ hs]
          simp
      have hinner (b : Bool) :
          ∑' s : Real,
              (∑ wanted : Fin k → Bool,
                  (∏ i : Fin k,
                    if wanted i then ENNReal.ofReal (p i.succ : Real)
                    else ENNReal.ofReal (1 - (p i.succ : Real))) *
                  PMF.pure
                    (∑ i : Fin k, if wanted i then (1 : Real) else 0) s) *
                PMF.pure ((if b then (1 : Real) else 0) + s) x =
            ∑ wanted : Fin k → Bool,
              (∏ i : Fin k,
                if wanted i then ENNReal.ofReal (p i.succ : Real)
                else ENNReal.ofReal (1 - (p i.succ : Real))) *
              PMF.pure
                ((if b then (1 : Real) else 0) +
                  ∑ i : Fin k, if wanted i then (1 : Real) else 0) x := by
        calc
          _ = ∑' s : Real,
                (∑' wanted : Fin k → Bool,
                    (∏ i : Fin k,
                      if wanted i then ENNReal.ofReal (p i.succ : Real)
                      else ENNReal.ofReal (1 - (p i.succ : Real))) *
                    PMF.pure
                      (∑ i : Fin k, if wanted i then (1 : Real) else 0) s) *
                  PMF.pure ((if b then (1 : Real) else 0) + s) x := by
              congr 1
              funext s
              rw [tsum_fintype]
          _ = ∑' s : Real, ∑' wanted : Fin k → Bool,
                (((∏ i : Fin k,
                    if wanted i then ENNReal.ofReal (p i.succ : Real)
                    else ENNReal.ofReal (1 - (p i.succ : Real))) *
                  PMF.pure
                    (∑ i : Fin k, if wanted i then (1 : Real) else 0) s) *
                  PMF.pure ((if b then (1 : Real) else 0) + s) x) := by
              simp_rw [ENNReal.tsum_mul_right]
          _ = ∑' wanted : Fin k → Bool, ∑' s : Real,
                (((∏ i : Fin k,
                    if wanted i then ENNReal.ofReal (p i.succ : Real)
                    else ENNReal.ofReal (1 - (p i.succ : Real))) *
                  PMF.pure
                    (∑ i : Fin k, if wanted i then (1 : Real) else 0) s) *
                  PMF.pure ((if b then (1 : Real) else 0) + s) x) :=
              ENNReal.tsum_comm
          _ = ∑' wanted : Fin k → Bool,
                (∏ i : Fin k,
                  if wanted i then ENNReal.ofReal (p i.succ : Real)
                  else ENNReal.ofReal (1 - (p i.succ : Real))) *
                PMF.pure
                  ((if b then (1 : Real) else 0) +
                    ∑ i : Fin k, if wanted i then (1 : Real) else 0) x := by
              simp_rw [hpure]
          _ = ∑ wanted : Fin k → Bool,
                (∏ i : Fin k,
                  if wanted i then ENNReal.ofReal (p i.succ : Real)
                  else ENNReal.ofReal (1 - (p i.succ : Real))) *
                PMF.pure
                  ((if b then (1 : Real) else 0) +
                    ∑ i : Fin k, if wanted i then (1 : Real) else 0) x :=
              by rw [tsum_fintype]
      simp_rw [hinner]
      rw [tsum_fintype]
      rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ,
        Fin.sum_univ_succ, hcoin]
      simp_rw [Finset.mul_sum]
      simp only [mul_assoc]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · expanded recursive binds, collapsed each pure-mass convolution, and reindexed by `Fin.consEquiv`
-/
