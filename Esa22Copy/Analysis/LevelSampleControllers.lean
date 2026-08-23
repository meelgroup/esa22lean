import Esa22Copy.Analysis.LevelSamplePrefixSucc

/-!
# Controllers for fixed-level sample membership

Every distinct item in a stream prefix has a latest occurrence in that prefix.  Those
latest occurrences are distinct and the bit block at that occurrence alone controls
the item's final membership in the erase-then-resample fold.
-/

namespace Esa22Copy

/--
INTERNAL: deterministic latest-occurrence form of the fixed-level sampling fold.
-/
theorem levelSample_has_injective_controllers (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) (k : Nat) :
    ∃ controller : {a // a ∈ prefixDistinct A i} → Fin P.m,
      Function.Injective controller ∧
        ∀ (coins : LevelCoins P) (a : {a // a ∈ prefixDistinct A i}),
          (a.1 ∈ levelSample coins A k i) = acceptsAt k (coins (controller a)) := by
  have aux : ∀ (r : Nat) (hr : r ≤ P.m),
      ∃ controller :
          {a // a ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_le hr⟩} → Fin P.m,
        Function.Injective controller ∧
          (∀ a, (controller a).val < r) ∧
          ∀ (coins : LevelCoins P)
              (a : {a // a ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_le hr⟩}),
            (a.1 ∈ levelSample coins A k ⟨r, Nat.lt_succ_of_le hr⟩) =
              acceptsAt k (coins (controller a)) := by
    intro r
    induction r with
    | zero =>
        intro hr
        let controller :
            {a // a ∈ prefixDistinct A ⟨0, Nat.lt_succ_of_le hr⟩} → Fin P.m :=
          fun a => False.elim (by simpa [prefixDistinct] using a.property)
        refine ⟨controller, ?_, ?_, ?_⟩
        · intro a
          exact False.elim (by simpa [prefixDistinct] using a.property)
        · intro a
          exact False.elim (by simpa [prefixDistinct] using a.property)
        · intro coins a
          exact False.elim (by simpa [prefixDistinct] using a.property)
    | succ r ih =>
        intro hsucc
        have hr : r < P.m := Nat.lt_of_succ_le hsucc
        obtain ⟨old, holdinj, holdrange, holdmem⟩ := ih (Nat.le_of_lt hr)
        let q : Fin P.m := ⟨r, hr⟩
        have hprefix (x : Item P) :
            x ∈ prefixDistinct A ⟨r + 1, Nat.lt_succ_of_le hsucc⟩ ↔
              x = A q ∨
                x ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ := by
          simp only [prefixDistinct, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩
            by_cases h : j.val = r
            · left
              congr
              exact Fin.ext h
            · right
              refine ⟨j, ?_, rfl⟩
              omega
          · rintro (rfl | ⟨j, hj, rfl⟩)
            · refine ⟨q, ?_, rfl⟩
              simp [q]
            · refine ⟨j, ?_, rfl⟩
              omega
        let controller :
            {a // a ∈ prefixDistinct A ⟨r + 1, Nat.lt_succ_of_le hsucc⟩} →
              Fin P.m := fun a =>
          if h : a.1 = A q then q
          else old ⟨a.1, (hprefix a.1).mp a.property |>.resolve_left h⟩
        refine ⟨controller, ?_, ?_, ?_⟩
        · intro a b hab
          by_cases ha : a.1 = A q
          · by_cases hb : b.1 = A q
            · apply Subtype.ext
              exact ha.trans hb.symm
            · have hbold :
                  b.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
                (hprefix b.1).mp b.property |>.resolve_left hb
              have hbval := holdrange ⟨b.1, hbold⟩
              have heq : q = old ⟨b.1, hbold⟩ := by
                simpa [controller, ha, hb] using hab
              have := congrArg Fin.val heq
              simp [q] at this
              omega
          · by_cases hb : b.1 = A q
            · have haold :
                  a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
                (hprefix a.1).mp a.property |>.resolve_left ha
              have haval := holdrange ⟨a.1, haold⟩
              have heq : old ⟨a.1, haold⟩ = q := by
                simpa [controller, ha, hb] using hab
              have := congrArg Fin.val heq
              simp [q] at this
              omega
            · have haold :
                  a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
                (hprefix a.1).mp a.property |>.resolve_left ha
              have hbold :
                  b.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
                (hprefix b.1).mp b.property |>.resolve_left hb
              have heq : old ⟨a.1, haold⟩ = old ⟨b.1, hbold⟩ := by
                simpa [controller, ha, hb] using hab
              have hold : (⟨a.1, haold⟩ :
                    {x // x ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩}) =
                  ⟨b.1, hbold⟩ := holdinj heq
              apply Subtype.ext
              exact congrArg (fun x :
                {x // x ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩} => x.1) hold
        · intro a
          by_cases ha : a.1 = A q
          · simp [controller, ha, q]
          · have haold :
                a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
              (hprefix a.1).mp a.property |>.resolve_left ha
            have haval := holdrange ⟨a.1, haold⟩
            simp only [controller, dif_neg ha]
            omega
        · intro coins a
          rw [levelSample_prefix_succ P A coins k r hr]
          by_cases ha : a.1 = A q
          · have hself :
                (A q ∈ refresh (A q) k (coins q)
                  (levelSample coins A k ⟨r, Nat.lt_succ_of_lt hr⟩)) =
                    acceptsAt k (coins q) := by
                unfold refresh
                by_cases hacc : acceptsAt k (coins q) = true <;> simp [hacc]
            simpa only [controller, dif_pos ha, q, ha] using hself
          · have haold :
                a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
              (hprefix a.1).mp a.property |>.resolve_left ha
            have hm := holdmem coins ⟨a.1, haold⟩
            have href :
                (a.1 ∈ refresh (A q) k (coins q)
                  (levelSample coins A k ⟨r, Nat.lt_succ_of_lt hr⟩)) =
                    (a.1 ∈ levelSample coins A k
                      ⟨r, Nat.lt_succ_of_lt hr⟩) := by
              unfold refresh
              by_cases hacc : acceptsAt k (coins q) = true <;> simp [hacc, ha]
            simpa only [controller, dif_neg ha, q] using href.trans hm
  have hiLe : i.val ≤ P.m := by omega
  obtain ⟨controller, hinj, _hrange, hmem⟩ := aux i.val hiLe
  refine ⟨controller, hinj, ?_⟩
  intro coins a
  exact hmem coins a

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · strengthened prefix induction tracks latest occurrences below the prefix bound
* r1 · open · isolated the deterministic latest-occurrence/controller argument
-/
