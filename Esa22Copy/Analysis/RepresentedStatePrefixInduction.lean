import Esa22Copy.Analysis.RepresentedStatePrefixSuccessor

/-!
# Causal representation of relaxed prefix runs

This module states the strengthened deferred-decisions induction behind the adaptive
Algorithm 2/Algorithm 3 coupling.  In addition to the distributional and fixed-level
sample invariants, it records causality: after `r` arrivals, the represented state only
uses rows before `r` and bit coordinates below the level it attains.
-/

namespace Esa22Copy

/--
INTERNAL: strengthened prefix induction carrying the causal coin-dependence invariant
needed to expose the next row and the next level frontier as fresh randomness.
-/
theorem representedState_prefix_induction (P : Params) (A : Stream P)
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
    (r : Nat) (hr : r ≤ i.val) :
    ∃ representedState : LevelCoins P → RelaxedState P,
      (PMF.uniformOfFintype (LevelCoins P)).map representedState =
          ((List.ofFn A).take r).foldlM (fun s a => relaxedStep P a s)
            { samples := ∅, level := 0 } ∧
      (∀ coins : LevelCoins P,
        (representedState coins).samples =
          levelSample coins A (representedState coins).level
            ⟨r, lt_of_le_of_lt hr i.isLt⟩) ∧
      (∀ coins : LevelCoins P, (representedState coins).level ≤ r) ∧
      ∀ x y : LevelCoins P,
        (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
          j.val < r → q.val < (representedState x).level → x j q = y j q) →
        representedState x = representedState y := by
  induction r with
  | zero =>
      let initial : RelaxedState P := { samples := ∅, level := 0 }
      refine ⟨fun _ => initial, ?_, ?_, ?_, ?_⟩
      · change
          (PMF.uniformOfFintype (LevelCoins P)).map
              (Function.const (LevelCoins P) initial) = PMF.pure initial
        exact PMF.map_const (PMF.uniformOfFintype (LevelCoins P)) initial
      · intro coins
        change ∅ = levelSample coins A 0 ⟨0, lt_of_le_of_lt hr i.isLt⟩
        rfl
      · intro coins
        exact le_rfl
      · intro x y _
        rfl
  | succ r ih =>
      have hr' : r ≤ i.val := Nat.le_trans (Nat.le_succ r) hr
      obtain ⟨representedState, hdistribution, hsample, hlevel, hcausal⟩ := ih hr'
      exact representedState_prefix_successor P A i hprefix hsucc hfrontier r hr
        representedState hdistribution hsample hlevel hcausal

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · reduced · closed induction and base case; isolated the probabilistic successor
  as `representedState_prefix_successor`
* r3 · open · isolated the strengthened causal prefix induction needed by
  `representedState_distribution`
-/
