import Esa22Copy.Analysis.NonfailRel

/-!
# Terminal event agreement under the nonfailure simulation

Related terminal states compute the same numerical estimate whenever the
original state is nonfailed, so original error and relaxed error coincide.
-/

namespace Esa22Copy

/--
INTERNAL: converts agreement of terminal state data into agreement of the two
error predicates on a nonfailed original output.
-/
theorem finish_nonfail_error_iff_relaxed_error {P : Params} {A : Stream P}
    {s : State P} {r : RelaxedState P} (hrel : NonfailRel s r)
    (hnonfail : finish s ∉ failEvent P) :
    finish s ∈ errorEvent P A ↔ r ∈ relaxedErrorEvent P A := by
  obtain ⟨hsamples, hlevel, hanswer⟩ := hrel hnonfail
  simp only [errorEvent, accurateEvent, Set.mem_compl_iff, Set.mem_ofPred_eq,
    finish, hanswer, Option.isSome_none, Bool.false_eq_true, if_neg, not_false_eq_true,
    relaxedErrorEvent, accurateEvent]
  rw [← hsamples, ← hlevel, cast_scaled]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · added · proved terminal error agreement from the simulation invariant
-/
