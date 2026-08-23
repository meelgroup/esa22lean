import Esa22Copy.Analysis.LevelSampleCommonControllers

/-!
# Adjacent levels of a fixed-prefix sample

The latest occurrence controlling each prefix item also exposes the one additional
bit which distinguishes sampling at level `k + 1` from sampling at level `k`.
-/

namespace Esa22Copy

/--
INTERNAL: adjacent fixed levels differ by filtering on the controller's next bit.
-/
theorem levelSample_succ_level (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) (k : Nat) (hk : k ≤ P.m) :
    ∃ controller : {a // a ∈ prefixDistinct A i} → Fin P.m,
      Function.Injective controller ∧
        ∀ coins : LevelCoins P,
        levelSample coins A (k + 1) i =
          (levelSample coins A k i).filter fun a =>
            ∃ ha : a ∈ prefixDistinct A i,
              coins (controller ⟨a, ha⟩) ⟨k, Nat.lt_succ_of_le hk⟩ = true := by
  have haccepts (bits : BitBlock P) :
      acceptsAt (k + 1) bits = true ↔
        acceptsAt k bits = true ∧
          bits ⟨k, Nat.lt_succ_of_le hk⟩ = true := by
    unfold acceptsAt
    simp only [show k + 1 ≤ P.m + 1 by omega,
      show k ≤ P.m + 1 by omega, if_true]
    rw [List.take_succ, List.all_append, List.getElem?_ofFn]
    simp only [show k < P.m + 1 by omega, dif_pos, Option.toList_some,
      List.all_cons, id_eq, List.all_nil, Bool.and_true, Bool.and_eq_true]
  obtain ⟨controller, hinj, hmem, hsubset⟩ :=
    levelSample_has_common_injective_controller P A i
  refine ⟨controller, hinj, ?_⟩
  intro coins
  ext a
  simp only [Finset.mem_filter]
  by_cases ha : a ∈ prefixDistinct A i
  · let aa : {x // x ∈ prefixDistinct A i} := ⟨a, ha⟩
    rw [hmem coins (k + 1) aa, hmem coins k aa,
      haccepts (coins (controller aa))]
    constructor
    · rintro ⟨haccepted, hbit⟩
      exact ⟨haccepted, ha, hbit⟩
    · rintro ⟨haccepted, ha', hbit⟩
      refine ⟨haccepted, ?_⟩
      simpa [aa] using hbit
  · have hnotSucc : a ∉ levelSample coins A (k + 1) i :=
      fun h => ha (hsubset coins (k + 1) h)
    have hnotBase : a ∉ levelSample coins A k i :=
      fun h => ha (hsubset coins k h)
    simp [hnotSucc, hnotBase]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · used one latest-occurrence controller uniformly at levels `k` and `k + 1`
* r1 · open · isolated the common latest-occurrence controller needed across adjacent levels
-/
