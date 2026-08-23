import Esa22Copy.Analysis.RelaxedCoupling

/-!
# Reachable relaxed levels

After `i` stream updates, the relaxed algorithm has increased its level at most
`i` times.
-/

namespace Esa22Copy

/--
INTERNAL: every state reachable after a prefix of length `i` has level at most
that prefix length.
-/
theorem relaxedRunPrefix_level_le (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) (s : RelaxedState P)
    (hs : s ∈ (relaxedRunPrefix P A i).support) :
    s.level ≤ i.val := by
  have step_level_le : ∀ (a : Item P) (u v : RelaxedState P),
      v ∈ (relaxedStep P a u).support → v.level ≤ u.level + 1 := by
    intro a u v hv
    rw [relaxedStep, PMF.mem_support_bind_iff] at hv
    obtain ⟨bits, _, hv⟩ := hv
    let refreshed := refresh a u.level bits u.samples
    by_cases hthreshold : refreshed.card = threshold P
    · rw [if_pos hthreshold, PMF.mem_support_bind_iff] at hv
      obtain ⟨retained, _, hv⟩ := hv
      change v ∈ (PMF.pure
        { samples := refreshed ∩ retained, level := u.level + 1 }).support at hv
      rw [PMF.mem_support_pure_iff] at hv
      subst v
      exact Nat.le_refl _
    · rw [if_neg hthreshold] at hv
      change v ∈ (PMF.pure
        { samples := refreshed, level := u.level }).support at hv
      rw [PMF.mem_support_pure_iff] at hv
      subst v
      exact Nat.le_succ _
  have fold_level_le : ∀ (l : List (Item P)) (u v : RelaxedState P),
      v ∈ (l.foldlM (fun state a => relaxedStep P a state) u).support →
      v.level ≤ u.level + l.length := by
    intro l
    induction l with
    | nil =>
        intro u v hv
        change v ∈ (PMF.pure u).support at hv
        rw [PMF.mem_support_pure_iff] at hv
        subst v
        simp
    | cons a l ih =>
        intro u v hv
        rw [List.foldlM] at hv
        change v ∈ (PMF.bind (relaxedStep P a u)
          (fun w => l.foldlM (fun state a => relaxedStep P a state) w)).support at hv
        rw [PMF.mem_support_bind_iff] at hv
        obtain ⟨w, hw, hv⟩ := hv
        have hstep := step_level_le a u w hw
        have hfold := ih w v hv
        simp only [List.length_cons]
        omega
  unfold relaxedRunPrefix at hs
  have h := fold_level_le ((List.ofFn A).take i.val)
    { samples := ∅, level := 0 } s hs
  simp only [List.length_take, List.length_ofFn, zero_add] at h
  omega

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · induction over supported relaxed transitions bounds level by prefix length
-/
