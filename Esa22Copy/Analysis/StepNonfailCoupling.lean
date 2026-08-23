import Esa22Copy.Analysis.NonfailRel

/-!
# One-step original-to-relaxed coupling

The transition uses a shared insertion block and, in the threshold branch, a
shared thinning subset.  If thinning makes the original estimator fail, the
simulation relation becomes vacuous; otherwise both common state fields agree.
-/

namespace Esa22Copy

/--
INTERNAL: one original and relaxed transition have a coupling preserving the
nonfailure simulation invariant on every supported result.
-/
theorem step_nonfail_coupling {P : Params} (a : Item P) (s : State P)
    (r : RelaxedState P) (hrel : NonfailRel s r) :
    ∃ κ : PMF (State P × RelaxedState P),
      κ.map Prod.fst = step P a s ∧
      κ.map Prod.snd = relaxedStep P a r ∧
      ∀ z ∈ κ.support, NonfailRel z.1 z.2 := by
  by_cases hfail : finish s ∈ failEvent P
  · have hstep : step P a s = pure s := by
      unfold finish failEvent at hfail
      simp only [Set.mem_setOf_eq] at hfail
      cases h : s.answer with
      | none => simp [h] at hfail
      | some ans =>
        cases ans with
        | none => simp [step, h]
        | some x => simp [h] at hfail
    have hvacuous : ∀ r : RelaxedState P, NonfailRel s r := by
      intro r hnonfail
      exact (hnonfail hfail).elim
    refine ⟨(relaxedStep P a r).map (fun r' => (s, r')), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      change (relaxedStep P a r).map (Function.const (RelaxedState P) s) =
        step P a s
      rw [PMF.map_const, hstep]
      change PMF.pure s = PMF.pure s
      rfl
    · rw [PMF.map_comp]
      change (relaxedStep P a r).map id = relaxedStep P a r
      rw [PMF.map_id]
    · intro z hz
      rw [PMF.mem_support_map_iff] at hz
      obtain ⟨r', _, rfl⟩ := hz
      exact hvacuous r'
  · obtain ⟨hsamples, hlevel, hanswer⟩ := hrel hfail
    let erase : State P → RelaxedState P :=
      fun t => { samples := t.samples, level := t.level }
    have herase : (step P a s).map erase = relaxedStep P a r := by
      rw [step, hanswer, relaxedStep, PMF.map_bind]
      apply congrArg (freshBlock P).bind
      funext bits
      simp only [← hsamples, ← hlevel]
      split
      · rw [PMF.map_bind]
        apply congrArg (freshSubset P).bind
        funext retained
        change PMF.map erase (PMF.pure _) = PMF.pure _
        rw [PMF.pure_map]
      · change PMF.map erase (PMF.pure _) = PMF.pure _
        rw [PMF.pure_map]
    have hsupport : ∀ t ∈ (step P a s).support, NonfailRel t (erase t) := by
      intro t ht
      unfold NonfailRel
      intro hnonfail
      rw [step, hanswer, PMF.mem_support_bind_iff] at ht
      obtain ⟨bits, _, ht⟩ := ht
      let refreshed := refresh a s.level bits s.samples
      by_cases hthreshold : refreshed.card = threshold P
      · rw [if_pos hthreshold, PMF.mem_support_bind_iff] at ht
        obtain ⟨retained, _, ht⟩ := ht
        change t ∈ (PMF.pure
          { samples := refreshed ∩ retained
            level := s.level + 1
            peakSamples := max s.peakSamples refreshed.card
            answer := if (refreshed ∩ retained).card = threshold P
              then some none else none }).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        by_cases hthin : (refreshed ∩ retained).card = threshold P
        · simp [finish, failEvent, hthin] at hnonfail
        · exact ⟨rfl, rfl, by simp [hthin]⟩
      · rw [if_neg hthreshold] at ht
        change t ∈ (PMF.pure
          { samples := refreshed
            level := s.level
            peakSamples := max s.peakSamples refreshed.card
            answer := none }).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        exact ⟨rfl, rfl, rfl⟩
    refine ⟨(step P a s).map (fun t => (t, erase t)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      change (step P a s).map id = step P a s
      rw [PMF.map_id]
    · rw [PMF.map_comp]
      change (step P a s).map erase = relaxedStep P a r
      exact herase
    · intro z hz
      rw [PMF.mem_support_map_iff] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact hsupport t ht

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · constructed the absorbing and graph couplings directly
* r1 · reduced · isolated the shared-randomness transition coupling
-/
