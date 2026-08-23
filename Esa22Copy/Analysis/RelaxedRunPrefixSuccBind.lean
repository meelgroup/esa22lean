import Esa22Copy.Analysis.RelaxedCoupling

/-!
# Successor relaxed prefix as one bind

The relaxed execution through prefix `r + 1` is the execution through prefix `r`
followed by the single transition for occurrence `r`.
-/

namespace Esa22Copy

/--
INTERNAL: expose the last transition of a nonempty relaxed prefix execution.
-/
theorem relaxedRunPrefix_succ_bind (P : Params) (A : Stream P) (r : Nat)
    (hr : r < P.m) :
    relaxedRunPrefix P A ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (relaxedRunPrefix P A ⟨r, Nat.lt_succ_of_lt hr⟩).bind
        (relaxedStep P (A ⟨r, hr⟩)) := by
  unfold relaxedRunPrefix
  rw [List.take_succ, List.foldlM_append]
  have hget : (List.ofFn A)[r]? = some (A ⟨r, hr⟩) := by
    rw [List.getElem?_eq_getElem (by simp [hr])]
    simp
  rw [hget]
  simp
  change
    (List.foldlM (fun s a => relaxedStep P a s)
      { samples := ∅, level := 0 } ((List.ofFn A).take r)).bind
        (fun s => relaxedStep P (A ⟨r, hr⟩) s) = _
  rfl

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · added · exposed the final update of a successor prefix as a PMF bind
-/
