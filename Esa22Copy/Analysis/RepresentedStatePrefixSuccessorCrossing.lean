import Esa22Copy.Analysis.RepresentedStateOneStepCouplingCrossing

/-!
# A crossing invariant for the represented-state successor

This module strengthens the causal represented-state successor by retaining the
pathwise relation between the supplied representation and the representation after
one more stream item.  That relation is the deterministic bookkeeping needed by the
paper's first-crossing argument.
-/

namespace Esa22Copy

/--
INTERNAL: the causal represented-state successor can be chosen so that crossing a
fixed level is witnessed either by the old state or by a threshold-sized fixed-level
sample at the new prefix.
-/
theorem representedState_prefix_successor_crossing (P : Params) (A : Stream P)
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
    (hdistribution :
      (PMF.uniformOfFintype (LevelCoins P)).map representedState =
        ((List.ofFn A).take r).foldlM (fun s a => relaxedStep P a s)
          { samples := ∅, level := 0 })
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
          ((List.ofFn A).take (r + 1)).foldlM (fun s a => relaxedStep P a s)
            { samples := ∅, level := 0 } ∧
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
              (levelSample coins A k
                ⟨r + 1, lt_of_le_of_lt hr i.isLt⟩).card := by
  have hrm : r < P.m := by
    omega
  obtain ⟨representedState', hstep, hsample', hlevel', hcausal', hcrossing⟩ :=
    representedState_one_step_coupling_crossing P A i hprefix hsucc hfrontier
      r hr representedState hsample hlevel hcausal
  refine ⟨representedState', ?_, hsample', hlevel', hcausal', hcrossing⟩
  rw [hstep, hdistribution]
  rw [List.take_succ, List.foldlM_append]
  have hget : (List.ofFn A)[r]? = some (A ⟨r, hrm⟩) := by
    rw [List.getElem?_eq_getElem (by simp [hrm])]
    simp
  rw [hget]
  simp
  rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · reduced · closed prefix-fold bookkeeping from the strengthened one-step
  coupling `representedState_one_step_coupling_crossing`
* r6 · open · isolated the crossing relation omitted by the existing represented-state
  successor theorem
-/
