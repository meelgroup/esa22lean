import Esa22Copy.Analysis.LevelSampleEqOfEqBelow
import Esa22Copy.Analysis.RepresentedStateCrossingUpdateDistribution

/-!
# One-step represented-state coupling with a crossing witness

This module strengthens the causal one-step coupling with the pathwise fact needed by
the first-crossing argument.  If the new represented state rises above a fixed level
that the old represented state did not exceed, the fixed-level sample immediately
after the processed item has threshold cardinality.
-/

namespace Esa22Copy

/--
INTERNAL: the one-step causal represented-state coupling can be chosen so that every
newly crossed level is witnessed by a threshold-sized fixed-level sample.
-/
theorem representedState_one_step_coupling_crossing (P : Params) (A : Stream P)
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
      (∀ x y : LevelCoins P,
        (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
          j.val < r + 1 → q.val < (representedState' x).level → x j q = y j q) →
        representedState' x = representedState' y) ∧
      ∀ (k : Nat) (hk : k ≤ P.m) (coins : LevelCoins P),
        k < (representedState' coins).level →
          k < (representedState coins).level ∨
            threshold P ≤
              (levelSample coins A k ⟨r + 1, lt_of_le_of_lt hr i.isLt⟩).card := by
  have hrm : r < P.m := by
    omega
  let representedState' : LevelCoins P → RelaxedState P :=
    representedStateCrossingUpdate P A r hrm representedState
  refine ⟨representedState', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [representedState'] using
      representedState_crossing_update_distribution P A r hrm hprefix hsucc
        hfrontier representedState (fun coins => hsample coins) hlevel hcausal
  · intro coins
    have hs := hsample coins
    have hp := hprefix coins (representedState coins).level r hrm
    simp only [representedState', representedStateCrossingUpdate]
    split
    · rfl
    · rw [hs]
      exact hp.symm
  · intro coins
    simp only [representedState', representedStateCrossingUpdate]
    split
    · change (representedState coins).level + 1 ≤ r + 1
      exact Nat.add_le_add_right (hlevel coins) 1
    · change (representedState coins).level ≤ r + 1
      exact Nat.le_trans (hlevel coins) (Nat.le_succ r)
  · intro x y hxy
    have hold : representedState x = representedState y := by
      apply hcausal
      intro j q hj hq
      apply hxy j q
      · omega
      · simp only [representedState', representedStateCrossingUpdate]
        split
        · change q.val < (representedState x).level + 1
          omega
        · change q.val < (representedState x).level
          exact hq
    have hbase :
        levelSample x A (representedState x).level
            ⟨r + 1, Nat.succ_lt_succ hrm⟩ =
          levelSample y A (representedState x).level
            ⟨r + 1, Nat.succ_lt_succ hrm⟩ := by
      apply levelSample_eq_of_eq_below
      intro j q hj hq
      apply hxy j q hj
      simp only [representedState', representedStateCrossingUpdate]
      split
      · change q.val < (representedState x).level + 1
        omega
      · change q.val < (representedState x).level
        exact hq
    have hrefresh :
        refresh (A ⟨r, hrm⟩) (representedState x).level (x ⟨r, hrm⟩)
            (representedState x).samples =
          refresh (A ⟨r, hrm⟩) (representedState y).level (y ⟨r, hrm⟩)
            (representedState y).samples := by
      rw [hsample x, hsample y, ← hold]
      rw [← hprefix x (representedState x).level r hrm,
        ← hprefix y (representedState x).level r hrm]
      exact hbase
    have hrefresh' :
        refresh (A ⟨r, hrm⟩) (representedState y).level (x ⟨r, hrm⟩)
            (representedState y).samples =
          refresh (A ⟨r, hrm⟩) (representedState y).level (y ⟨r, hrm⟩)
            (representedState y).samples := by
      simpa only [hold] using hrefresh
    simp only [representedState', representedStateCrossingUpdate]
    rw [hold, hrefresh']
    split
    next hcross =>
      congr 1
      apply levelSample_eq_of_eq_below
      intro j q hj hq
      apply hxy j q hj
      simp only [representedState', representedStateCrossingUpdate]
      rw [hold, hrefresh']
      simp only [if_pos hcross]
      exact hq
    next _ => rfl
  · intro k hk coins hcross
    have hs := hsample coins
    have hp := hprefix coins (representedState coins).level r hrm
    simp only [representedState', representedStateCrossingUpdate] at hcross
    split at hcross
    next hthreshold =>
      by_cases holdCross : k < (representedState coins).level
      · exact Or.inl holdCross
      · right
        have hcross' : k < (representedState coins).level + 1 := by
          exact hcross
        have hkEq : k = (representedState coins).level := by omega
        rw [hkEq, hp, ← hs, hthreshold]
    next _ =>
      exact Or.inl hcross

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · reduced · defined the explicit update and proved its deterministic sample,
  level, causality, and crossing invariants; isolated only its conditional-law calculation
* r8 · open · isolated the construction-level strengthening needed because the
  distribution-only one-step coupling does not expose a pointwise old/new relation
-/
