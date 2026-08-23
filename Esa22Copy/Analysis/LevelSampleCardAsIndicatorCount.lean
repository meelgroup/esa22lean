import Esa22Copy.Model.Pseudocode

/-!
# Fixed-level sample cardinality as a prefix indicator count

The fixed-level fold never contains values outside the processed prefix. Consequently its
cardinality is exactly the number of prefix values whose membership indicator is true.
-/

namespace Esa22Copy

/--
INTERNAL: the cardinality of a fixed-level sample is the count of its membership
indicators indexed by the distinct items of the processed prefix.
-/
theorem levelSample_card_as_indicator_count (P : Params) (A : Stream P)
    (coins : LevelCoins P) (i : Fin (P.m + 1)) (k : Nat) :
    (levelSample coins A k i).card =
      (Finset.univ.filter fun a : {a // a ∈ prefixDistinct A i} =>
        a.1 ∈ levelSample coins A k i).card := by
  have hentry : ∀ e ∈ (List.ofFn fun j => (A j, coins j)).take i.val,
      e.1 ∈ prefixDistinct A i := by
    intro e he
    obtain ⟨j, hj⟩ := List.get_of_mem he
    have hjltI : j.val < i.val :=
      lt_of_lt_of_le j.isLt (List.length_take_le _ _)
    have hiM : i.val ≤ P.m := Nat.le_of_lt_succ i.isLt
    have hjM : j.val < P.m := lt_of_lt_of_le hjltI hiM
    let q : Fin P.m := ⟨j.val, hjM⟩
    have heq : e = (A q, coins q) := by
      rw [← hj, List.get_eq_getElem, List.getElem_take, List.getElem_ofFn]
    rw [prefixDistinct]
    refine Finset.mem_image.2 ⟨q, ?_, ?_⟩
    · simp [q, hjltI]
    · simp [heq]
  have hrefresh : ∀ (e : Item P × BitBlock P) (X : Finset (Item P)),
      X ⊆ prefixDistinct A i → e.1 ∈ prefixDistinct A i →
        refresh e.1 k e.2 X ⊆ prefixDistinct A i := by
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
        xs.foldl (fun X e => refresh e.1 k e.2 X) X ⊆ prefixDistinct A i := by
    intro xs X hX hall
    induction xs generalizing X with
    | nil => simpa using hX
    | cons e es ih =>
        rw [List.foldl_cons]
        apply ih
        · exact hrefresh e X hX (hall e (by simp))
        · intro e2 he2
          exact hall e2 (by simp [he2])
  have hsubset : levelSample coins A k i ⊆ prefixDistinct A i := by
    unfold levelSample
    exact hfold _ ∅ (by simp) hentry
  let X := levelSample coins A k i
  let S := prefixDistinct A i
  have hfilter : X.filter (fun a => a ∈ S) = X :=
    Finset.filter_eq_self.2 hsubset
  calc
    X.card = (X.filter fun a => a ∈ S).card := congrArg Finset.card hfilter.symm
    _ = (X.subtype fun a => a ∈ S).card := (Finset.card_subtype _ _).symm
    _ = (Finset.univ.filter fun a : {a // a ∈ S} => a.1 ∈ X).card := by
      congr 1
      ext a
      simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · established prefix containment through the fold and counted the resulting subtype indicators
-/
