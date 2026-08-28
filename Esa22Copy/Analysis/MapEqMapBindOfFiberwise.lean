import Esa22Copy.Interface.Pseudocode

/-!
# Reassembling a distribution from fiberwise kernel laws

This module gives the discrete disintegration step used to turn an unnormalised law on
each fiber of a deterministic summary into a `map` followed by a `bind`.
-/

namespace Esa22Copy

/--
INTERNAL: exact joint masses on every fiber determine the corresponding `map`/`bind` law.
-/
theorem map_eq_map_bind_of_fiberwise {Ω B C : Type*} (μ : PMF Ω)
    (base : Ω → B) (output : Ω → C) (kernel : B → PMF C)
    (hfiber : ∀ b c,
      μ.toOuterMeasure {ω | base ω = b ∧ output ω = c} =
        (μ.map base) b * kernel b c) :
    μ.map output = (μ.map base).bind kernel := by
  apply PMF.ext
  intro c
  rw [PMF.bind_apply]
  simp_rw [← hfiber]
  rw [PMF.map_apply]
  simp only [PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro ω
  by_cases h : output ω = c
  · rw [tsum_eq_single (base ω)]
    · simp [Set.indicator, h]
    · intro b hb
      have hne : ¬base ω = b := fun heq => hb heq.symm
      simp [Set.indicator, h, hne]
  · have hc : ¬c = output ω := fun hc => h hc.symm
    simp [Set.indicator, h, hc]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · proved · summed exact joint masses over the fibers of the deterministic summary
-/
