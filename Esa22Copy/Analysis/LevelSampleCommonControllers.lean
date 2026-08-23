import Esa22Copy.Analysis.LevelSamplePrefixSucc

/-!
# A level-independent controller for fixed-prefix samples

Every item in a stream prefix is controlled by its latest occurrence.  Since that
occurrence depends only on the prefix, the same injective controller characterizes
membership simultaneously at every sampling level.
-/

namespace Esa22Copy

/--
INTERNAL: the latest-occurrence controller for a prefix works uniformly at every level.
-/
theorem levelSample_has_common_injective_controller (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) :
    ∃ controller : {a // a ∈ prefixDistinct A i} → Fin P.m,
      Function.Injective controller ∧
        (∀ (coins : LevelCoins P) (level : Nat)
            (a : {a // a ∈ prefixDistinct A i}),
          (a.1 ∈ levelSample coins A level i) =
            acceptsAt level (coins (controller a))) ∧
        ∀ (coins : LevelCoins P) (level : Nat),
          levelSample coins A level i ⊆ prefixDistinct A i := by
  have aux : ∀ (r : Nat) (hr : r ≤ P.m),
      ∃ controller :
          {a // a ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_le hr⟩} → Fin P.m,
        Function.Injective controller ∧
          (∀ a, (controller a).val < r) ∧
          ∀ (coins : LevelCoins P) (level : Nat)
              (a : {a // a ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_le hr⟩}),
            (a.1 ∈ levelSample coins A level
                ⟨r, Nat.lt_succ_of_le hr⟩) =
              acceptsAt level (coins (controller a)) := by
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
        · intro coins level a
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
              have hval := congrArg Fin.val heq
              simp [q] at hval
              omega
          · by_cases hb : b.1 = A q
            · have haold :
                  a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
                (hprefix a.1).mp a.property |>.resolve_left ha
              have haval := holdrange ⟨a.1, haold⟩
              have heq : old ⟨a.1, haold⟩ = q := by
                simpa [controller, ha, hb] using hab
              have hval := congrArg Fin.val heq
              simp [q] at hval
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
                    {x // x ∈ prefixDistinct A
                      ⟨r, Nat.lt_succ_of_lt hr⟩}) =
                  ⟨b.1, hbold⟩ := holdinj heq
              apply Subtype.ext
              exact congrArg (fun x :
                {x // x ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩} =>
                  x.1) hold
        · intro a
          by_cases ha : a.1 = A q
          · simp [controller, ha, q]
          · have haold :
                a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
              (hprefix a.1).mp a.property |>.resolve_left ha
            have haval := holdrange ⟨a.1, haold⟩
            simp only [controller, dif_neg ha]
            omega
        · intro coins level a
          rw [levelSample_prefix_succ P A coins level r hr]
          by_cases ha : a.1 = A q
          · have hself :
                (A q ∈ refresh (A q) level (coins q)
                  (levelSample coins A level
                    ⟨r, Nat.lt_succ_of_lt hr⟩)) =
                    acceptsAt level (coins q) := by
                unfold refresh
                by_cases hacc : acceptsAt level (coins q) = true <;>
                  simp [hacc]
            simpa only [controller, dif_pos ha, q, ha] using hself
          · have haold :
                a.1 ∈ prefixDistinct A ⟨r, Nat.lt_succ_of_lt hr⟩ :=
              (hprefix a.1).mp a.property |>.resolve_left ha
            have hm := holdmem coins level ⟨a.1, haold⟩
            have href :
                (a.1 ∈ refresh (A q) level (coins q)
                  (levelSample coins A level
                    ⟨r, Nat.lt_succ_of_lt hr⟩)) =
                    (a.1 ∈ levelSample coins A level
                      ⟨r, Nat.lt_succ_of_lt hr⟩) := by
              unfold refresh
              by_cases hacc : acceptsAt level (coins q) = true <;>
                simp [hacc, ha]
            simpa only [controller, dif_neg ha, q] using href.trans hm
  have hiLe : i.val ≤ P.m := by omega
  obtain ⟨controller, hinj, _hrange, hmem⟩ := aux i.val hiLe
  refine ⟨controller, hinj, hmem, ?_⟩
  intro coins level
  have hentry : ∀ e ∈ (List.ofFn fun j => (A j, coins j)).take i.val,
      e.1 ∈ prefixDistinct A i := by
    intro e he
    obtain ⟨j, hj⟩ := List.get_of_mem he
    have hjltI : j.val < i.val :=
      lt_of_lt_of_le j.isLt (List.length_take_le _ _)
    have hjM : j.val < P.m := lt_of_lt_of_le hjltI hiLe
    let q : Fin P.m := ⟨j.val, hjM⟩
    have heq : e = (A q, coins q) := by
      rw [← hj, List.get_eq_getElem, List.getElem_take, List.getElem_ofFn]
    rw [prefixDistinct]
    refine Finset.mem_image.2 ⟨q, ?_, ?_⟩
    · simp [q, hjltI]
    · simp [heq]
  have hrefresh : ∀ (e : Item P × BitBlock P) (X : Finset (Item P)),
      X ⊆ prefixDistinct A i → e.1 ∈ prefixDistinct A i →
        refresh e.1 level e.2 X ⊆ prefixDistinct A i := by
    intro e X hX he a ha
    unfold refresh at ha
    split at ha
    · rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact he
      · exact hX (Finset.mem_of_mem_erase ha)
    · exact hX (Finset.mem_of_mem_erase ha)
  have hfold : ∀ (xs : List (Item P × BitBlock P)) (X : Finset (Item P)),
      X ⊆ prefixDistinct A i → (∀ e ∈ xs, e.1 ∈ prefixDistinct A i) →
        xs.foldl (fun X e => refresh e.1 level e.2 X) X ⊆
          prefixDistinct A i := by
    intro xs X hX hall
    induction xs generalizing X with
    | nil => simpa using hX
    | cons e es ih =>
        rw [List.foldl_cons]
        apply ih
        · exact hrefresh e X hX (hall e (by simp))
        · intro e2 he2
          exact hall e2 (by simp [he2])
  unfold levelSample
  exact hfold _ ∅ (by simp) hentry

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · made the latest-occurrence controller uniform over all sampling levels
-/
