import Esa22Copy.Analysis.RepresentedStateOneStepCouplingCrossing

/-!
# One-step causal represented-state coupling

This module isolates the probabilistic heart of the deferred-decisions induction.  It
advances a causal fixed-level representation across one stream occurrence, coupling
the newly exposed row with `freshBlock` and the newly exposed level frontier with
`freshSubset`.
-/

namespace Esa22Copy

/--
INTERNAL: one relaxed transition can be realized from the next unused row and level
frontier of a uniform coin table while preserving the fixed-level and causal invariants.
-/
theorem representedState_one_step_coupling (P : Params) (A : Stream P)
    (i : Fin (P.m + 1))
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
    (hfresh : ∀ (X : Finset (Item P)) (wanted : {a // a ∈ X} → Bool),
      (freshSubset P).toOuterMeasure
          {Y | ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} =
        (((2 : ENNReal) ^ X.card)⁻¹))
    (r : Nat) (hr : r + 1 ≤ i.val)
    (representedState : LevelCoins P → RelaxedState P)
    (hsample : ∀ coins : LevelCoins P,
      (representedState coins).samples =
        levelSample coins A (representedState coins).level
          ⟨r, lt_of_le_of_lt (Nat.le_trans (Nat.le_succ r) hr) i.isLt⟩)
    (hlevel : ∀ coins : LevelCoins P, (representedState coins).level ≤ r)
    (hcausal : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
        j.val < r → q.val < (representedState x).level → x j q = y j q) →
      representedState x = representedState y) :
    ∃ representedState' : LevelCoins P → RelaxedState P,
      (PMF.uniformOfFintype (LevelCoins P)).map representedState' =
          ((PMF.uniformOfFintype (LevelCoins P)).map representedState).bind
            (relaxedStep P
              (A ⟨r, Nat.lt_of_succ_le
                (Nat.le_trans hr (Nat.le_of_lt_succ i.isLt))⟩)) ∧
      (∀ coins : LevelCoins P,
        (representedState' coins).samples =
          levelSample coins A (representedState' coins).level
            ⟨r + 1, lt_of_le_of_lt hr i.isLt⟩) ∧
      (∀ coins : LevelCoins P, (representedState' coins).level ≤ r + 1) ∧
      ∀ x y : LevelCoins P,
        (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
          j.val < r + 1 → q.val < (representedState' x).level → x j q = y j q) →
        representedState' x = representedState' y := by
  obtain ⟨representedState', hdistribution, hsample', hlevel', hcausal', _⟩ :=
    representedState_one_step_coupling_crossing P A i hprefix hsucc hfrontier
      r hr representedState hsample hlevel hcausal
  exact ⟨representedState', hdistribution, hsample', hlevel', hcausal'⟩

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · projected the coupling and invariant conclusions from the existing
  stronger one-step coupling theorem, which additionally supplies the crossing witness
* r7 · open · isolated the one-step PMF coupling and preservation of the causal
  fixed-level representation from the surrounding prefix-fold induction; its exact
  uniform-thinning pattern law is now an explicit premise
-/
