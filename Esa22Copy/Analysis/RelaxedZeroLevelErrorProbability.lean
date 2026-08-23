import Esa22Copy.Analysis.ProbabilityModel

/-!
# Exactness of the relaxed estimator at level zero

A reachable final state that never thinned has retained exactly the distinct
stream values.  Its rate is one, so its estimate is exactly `F0` and cannot be
in the relaxed error event.
-/

namespace Esa22Copy

/--
INTERNAL: the relaxed estimator's level-zero error slice has probability zero.
-/
theorem relaxed_zero_level_error_probability (P : Params) (A : Stream P) :
    Arlib.Approximation.outProbR (relaxedRunCost P A)
      ({s | s.level = 0} ∩ relaxedErrorEvent P A) = 0 := by
  have hstep : ∀ (s t : RelaxedState P) (a : Item P),
      t ∈ (relaxedStep P a s).support → t.level = 0 →
        s.level = 0 ∧ t.samples = insert a s.samples := by
    intro s t a ht htlevel
    rw [relaxedStep, PMF.mem_support_bind_iff] at ht
    obtain ⟨bits, _hbits, ht⟩ := ht
    by_cases hcard : (refresh a s.level bits s.samples).card = threshold P
    · rw [if_pos hcard, PMF.mem_support_bind_iff] at ht
      obtain ⟨retained, _hretained, ht⟩ := ht
      change t ∈ (PMF.pure _).support at ht
      rw [PMF.mem_support_pure_iff] at ht
      subst t
      simp at htlevel
    · rw [if_neg hcard] at ht
      change t ∈ (PMF.pure _).support at ht
      rw [PMF.mem_support_pure_iff] at ht
      subst t
      simp only at htlevel
      have hslevel : s.level = 0 := htlevel
      constructor
      · exact hslevel
      · simp only [refresh, acceptsAt, hslevel, Nat.zero_le, ↓reduceIte,
          List.take_zero, List.all_nil]
        ext x
        by_cases hx : x = a <;> simp [hx]
  have hfold : ∀ (xs : List (Item P)) (s t : RelaxedState P),
      t ∈ (xs.foldlM (fun s a => relaxedStep P a s) s).support →
        t.level = 0 →
          s.level = 0 ∧ t.samples = s.samples ∪ xs.toFinset := by
    intro xs
    induction xs with
    | nil =>
        intro s t ht htlevel
        rw [List.foldlM_nil] at ht
        change t ∈ (PMF.pure s).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        exact ⟨htlevel, by simp⟩
    | cons a xs ih =>
        intro s t ht htlevel
        rw [List.foldlM_cons] at ht
        change t ∈ (PMF.bind (relaxedStep P a s)
          (fun u => xs.foldlM (fun s a => relaxedStep P a s) u)).support at ht
        rw [PMF.mem_support_bind_iff] at ht
        obtain ⟨u, hu, ht⟩ := ht
        obtain ⟨hulevel, htsamples⟩ := ih u t ht htlevel
        obtain ⟨hslevel, husamples⟩ := hstep s u a hu hulevel
        refine ⟨hslevel, ?_⟩
        rw [htsamples, husamples, List.toFinset_cons, Finset.insert_union,
          Finset.union_insert]
  have hrun : ∀ (s : RelaxedState P),
      s ∈ (relaxedRun P A).support → s.level = 0 →
        s.samples = distinctSet A := by
    intro s hs hslevel
    unfold relaxedRun at hs
    obtain ⟨_hinitialLevel, hsamples⟩ := hfold (List.ofFn A)
      { samples := ∅, level := 0 } s hs hslevel
    simpa [distinctSet, Fin.univ_image_def] using hsamples
  have hzero : Arlib.Approximation.outProb (relaxedRunCost P A)
      ({s | s.level = 0} ∩ relaxedErrorEvent P A) = 0 := by
    rw [Arlib.Approximation.outProb, PMF.toOuterMeasure_apply_eq_zero_iff,
      Set.disjoint_left]
    intro p hp hpevent
    unfold relaxedRunCost at hp
    obtain ⟨s, hs, hsp⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    subst p
    rcases hpevent with ⟨hslevel, hserror⟩
    apply hserror
    change (s.samples.card : Real) / ((2 : Real) ^ (-(s.level : Int))) ∈
      Arlib.relErr P.eps (F0 A : Real)
    rw [hslevel, hrun s hs hslevel]
    simp only [Int.ofNat_zero, neg_zero, zpow_zero, div_one]
    change (F0 A : Real) ∈ Arlib.relErr P.eps (F0 A : Real)
    rw [Arlib.relErr]
    have hF0 : (0 : Real) ≤ (F0 A : Real) := by positivity
    constructor <;> nlinarith [P.heps.1, hF0]
  rw [Arlib.Approximation.outProbR, hzero]
  simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · established level-zero exactness support-wise through `relaxedStep` and `foldlM`
* r3 · open · isolated the missing level-zero exactness invariant
-/
