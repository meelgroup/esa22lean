import Esa22Copy.Analysis.FreshSubsetRestrictionPattern
import Esa22Copy.Analysis.CausalStateRefreshDistribution
import Esa22Copy.Analysis.RepresentedStateFrontierThinningDistribution

/-!
# Distribution of the frontier-driven represented-state update

This module isolates the probabilistic calculation in the one-step represented-state
coupling.  The update uses the next row for refresh randomness and, exactly on a
threshold crossing, the next unused level frontier for thinning randomness.
-/

namespace Esa22Copy

/--
INTERNAL: the explicit deterministic update whose crossing branch is represented by
the next fixed-level sample.
-/
noncomputable def representedStateCrossingUpdate (P : Params) (A : Stream P)
    (r : Nat) (hr : r < P.m)
    (representedState : LevelCoins P → RelaxedState P) :
    LevelCoins P → RelaxedState P := fun coins =>
  let s := representedState coins
  let refreshed := refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples
  if refreshed.card = threshold P then
    { samples := levelSample coins A (s.level + 1)
        ⟨r + 1, Nat.succ_lt_succ hr⟩
      level := s.level + 1 }
  else
    { samples := refreshed, level := s.level }

/--
INTERNAL: under causal conditioning, the explicit frontier-driven update has exactly
the law of one relaxed transition.
-/
theorem representedState_crossing_update_distribution (P : Params) (A : Stream P)
    (r : Nat) (hr : r < P.m)
    (hprefix : ∀ (coins : LevelCoins P) (k r : Nat) (hr : r < P.m),
      levelSample coins A k ⟨r + 1, Nat.succ_lt_succ hr⟩ =
        refresh (A ⟨r, hr⟩) k (coins ⟨r, hr⟩)
          (levelSample coins A k ⟨r, Nat.lt_succ_of_lt hr⟩))
    (hsucc : ∀ (i : Fin (P.m + 1)) (k : Nat) (hk : k ≤ P.m),
      ∃ controller : {a // a ∈ prefixDistinct A i} → Fin P.m,
        Function.Injective controller ∧
          ∀ coins : LevelCoins P,
          levelSample coins A (k + 1) i =
            (levelSample coins A k i).filter fun a =>
              ∃ ha : a ∈ prefixDistinct A i,
                coins (controller ⟨a, ha⟩) ⟨k, Nat.lt_succ_of_le hk⟩ = true)
    (hfrontier : ∀ {I : Type} [Fintype I]
      (controller : I → Fin P.m) (hcontroller : Function.Injective controller)
      (k : Nat) (hk : k ≤ P.m) (E : Set (LevelCoins P)) (wanted : I → Bool),
      (∀ x y : LevelCoins P,
        (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
          (∀ a : I, j ≠ controller a ∨ q ≠ ⟨k, Nat.lt_succ_of_le hk⟩) → x j q = y j q) →
        (x ∈ E ↔ y ∈ E)) →
      (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure
          {coins | coins ∈ E ∧
            ∀ a : I, coins (controller a) ⟨k, Nat.lt_succ_of_le hk⟩ = wanted a} =
        (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure E *
          (((2 : ENNReal) ^ Fintype.card I)⁻¹))
    (representedState : LevelCoins P → RelaxedState P)
    (hsample : ∀ coins : LevelCoins P,
      (representedState coins).samples =
        levelSample coins A (representedState coins).level
          ⟨r, Nat.lt_succ_of_lt hr⟩)
    (hlevel : ∀ coins : LevelCoins P, (representedState coins).level ≤ r)
    (hcausal : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
        j.val < r → q.val < (representedState x).level → x j q = y j q) →
      representedState x = representedState y) :
    (PMF.uniformOfFintype (LevelCoins P)).map
        (representedStateCrossingUpdate P A r hr representedState) =
      ((PMF.uniformOfFintype (LevelCoins P)).map representedState).bind
        (relaxedStep P (A ⟨r, hr⟩)) := by
  have hcausalRow : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)), j.val < r → x j q = y j q) →
      representedState x = representedState y := by
    intro x y hxy
    apply hcausal
    intro j q hj _hq
    exact hxy j q hj
  change (PMF.uniformOfFintype (LevelCoins P)).map
      (fun coins ↦
        let s := representedState coins
        let refreshed := refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples
        if refreshed.card = threshold P then
          { samples := levelSample coins A (s.level + 1)
              ⟨r + 1, Nat.succ_lt_succ hr⟩
            level := s.level + 1 }
        else
          { samples := refreshed, level := s.level }) =
    ((PMF.uniformOfFintype (LevelCoins P)).map representedState).bind
      (relaxedStep P (A ⟨r, hr⟩))
  rw [representedState_frontier_thinning_distribution P A r hr hprefix hsucc
    hfrontier (freshSubset_restriction_pattern P) representedState hsample hlevel hcausal]
  rw [causalState_refresh_distribution P (A ⟨r, hr⟩) r hr representedState
    hcausalRow]
  rw [PMF.bind_bind]
  congr 1
  funext s
  rw [PMF.bind_map]
  rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · reduced · split the law into unused-row and adaptive-frontier calculations
* r9 · open · isolated the conditional frontier-pattern calculation for the explicit update
-/
