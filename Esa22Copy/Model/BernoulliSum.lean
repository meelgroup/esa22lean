import Esa22Copy.Model.Pseudocode

/-!
# Concrete Bernoulli sum laws

These model-side implementations are shared by the public declarations in
`Model.Theorem` and their concentration proof in `Analysis.TheoremProof`.
-/

namespace Esa22Copy

/-- INTERNAL: a Bernoulli PMF at an arbitrary real rate in `[0, 1]`. -/
noncomputable def bernoulliPMFModel (p : Set.Icc (0 : Real) 1) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (p : Real) else ENNReal.ofReal (1 - (p : Real)))
    (by
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2)]
      norm_num)

/-- INTERNAL: the recursively bound sum of the supplied Bernoulli laws. -/
noncomputable def bernoulliSumPMFModel :
    (k : Nat) → (p : Fin k → Set.Icc (0 : Real) 1) → PMF Real
  | 0, _ => PMF.pure 0
  | k + 1, p =>
      (bernoulliPMFModel (p 0)).bind fun b =>
        (bernoulliSumPMFModel k fun i => p i.succ).bind fun s =>
          PMF.pure ((if b then 1 else 0) + s)

end Esa22Copy
