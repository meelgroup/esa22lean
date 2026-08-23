import Esa22Copy.Analysis.RepresentedStateDistribution

/-!
# Strengthened prefix coupling

The adaptive coupling is strengthened with the bound that the current level cannot
exceed the number of processed stream positions.  The coin-driven/deferred-decisions
induction is isolated in `representedState_distribution`; this module turns that
representation into the required graph coupling.
-/

namespace Esa22Copy

/--
INTERNAL: prefix coupling with the level bound required to expose the next bit.
-/
theorem relaxedRun_levelSample_coupling_aux (P : Params) (A : Stream P)
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
    ∃ coupling : PMF (RelaxedState P × LevelCoins P),
      coupling.map Prod.fst =
        ((List.ofFn A).take i.val).foldlM (fun s a => relaxedStep P a s)
          { samples := ∅, level := 0 } ∧
      coupling.map Prod.snd = PMF.uniformOfFintype (LevelCoins P) ∧
      ∀ z ∈ coupling.support,
        z.1.samples = levelSample z.2 A z.1.level i ∧ z.1.level ≤ i.val := by
  obtain ⟨representedState, hdistribution, hsample, hlevel⟩ :=
    representedState_distribution P A i hprefix hsucc hfrontier
  let source := PMF.uniformOfFintype (LevelCoins P)
  refine ⟨source.map (fun coins => (representedState coins, coins)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    change source.map representedState = _
    simpa only [source] using hdistribution
  · rw [PMF.map_comp]
    change source.map id = _
    rw [PMF.map_id]
  · intro z hz
    obtain ⟨coins, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact ⟨hsample coins, hlevel coins⟩

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · reduced · closed the graph-coupling construction using `representedState_distribution`
* r1 · open · strengthened the coupling with `level ≤ prefix length`; the remaining proof
  needs a causal execution-fiber invariant to apply `uniform_table_fresh_frontier`
-/
