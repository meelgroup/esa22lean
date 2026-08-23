import Esa22Copy.Analysis.RepresentedStatePrefixInduction

/-!
# Coin-driven representation of a relaxed prefix run

This module isolates the deferred-decisions induction needed to represent a relaxed
prefix run as a deterministic function of the level-coin table.  Besides identifying
the distribution, the representation records the fixed-level sample invariant and the
elementary bound on the adaptive level.
-/

namespace Esa22Copy

/--
INTERNAL: the causal coin-table execution has the relaxed prefix-run distribution and
is represented by the corresponding fixed-level sample.
-/
theorem representedState_distribution (P : Params) (A : Stream P)
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
          (((2 : ENNReal) ^ Fintype.card I)⁻¹)) :
    ∃ representedState : LevelCoins P → RelaxedState P,
      (PMF.uniformOfFintype (LevelCoins P)).map representedState =
          ((List.ofFn A).take i.val).foldlM (fun s a => relaxedStep P a s)
            { samples := ∅, level := 0 } ∧
      (∀ coins : LevelCoins P,
        (representedState coins).samples =
          levelSample coins A (representedState coins).level i) ∧
      (∀ coins : LevelCoins P, (representedState coins).level ≤ i.val) := by
  obtain ⟨representedState, hdistribution, hsample, hlevel, _hcausal⟩ :=
    representedState_prefix_induction P A i hprefix hsucc hfrontier i.val le_rfl
  refine ⟨representedState, hdistribution, ?_, hlevel⟩
  intro coins
  simpa using hsample coins

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · reduced · closed the public representation theorem from the strengthened causal
  prefix induction
* r2 · reduced · isolated the causal deterministic representation and its distribution
-/
