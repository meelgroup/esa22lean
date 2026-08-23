import Esa22Copy.Model.Pseudocode

/-!
# Exactness below the sampling threshold

If the stream has fewer distinct values than the threshold, level zero never
triggers thinning and the estimator returns the exact distinct count.
-/

namespace Esa22Copy

/--
INTERNAL: discharges the exact, no-thinning branch of the accuracy proof.
-/
theorem small_stream_accuracy (P : Params) (A : Stream P)
    (hsmall : F0 A < threshold P) :
    1 - P.delta ≤ Arlib.Approximation.outProbR (run P A) (accurateEvent P A) := by
  have hstep : ∀ (a : Item P) (s : State P),
      s.level = 0 → s.answer = none → (insert a s.samples).card < threshold P →
      step P a s = pure (State.mk (insert a s.samples) 0
        (max s.peakSamples (insert a s.samples).card) none) := by
    intro a s hlevel hanswer hcard
    rw [step, hanswer]
    simp only [hlevel]
    simp_rw [show ∀ bits : BitBlock P,
        refresh a 0 bits s.samples = insert a s.samples by
      intro bits
      ext x
      by_cases h : x = a <;> simp [h, refresh, acceptsAt]]
    rw [if_neg (Nat.ne_of_lt hcard)]
    simp
  have hfold : ∀ (l : List (Item P)) (s : State P),
      s.level = 0 → s.answer = none → s.samples ⊆ distinctSet A →
      (∀ a ∈ l, a ∈ distinctSet A) →
      ∃ t : State P, l.foldlM (fun state a => step P a state) s = pure t ∧
        t.level = 0 ∧ t.answer = none ∧ t.samples = s.samples ∪ l.toFinset := by
    intro l
    induction l with
    | nil =>
        intro s hlevel hanswer _ _
        refine ⟨s, by simp, hlevel, hanswer, ?_⟩
        simp
    | cons a l ih =>
        intro s hlevel hanswer hsub hall
        have ha : a ∈ distinctSet A := hall a (by simp)
        have hsubinsert : insert a s.samples ⊆ distinctSet A := by
          intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact ha
          · exact hsub hx
        have hcard : (insert a s.samples).card < threshold P :=
          (Finset.card_le_card hsubinsert).trans_lt hsmall
        let s₁ : State P := State.mk (insert a s.samples) 0
          (max s.peakSamples (insert a s.samples).card) none
        have hs₁ : step P a s = pure s₁ := hstep a s hlevel hanswer hcard
        have htail : ∀ x ∈ l, x ∈ distinctSet A := by
          intro x hx
          exact hall x (by simp [hx])
        obtain ⟨t, ht, htlevel, htanswer, htsamples⟩ :=
          ih s₁ (by rfl) (by rfl) hsubinsert htail
        refine ⟨t, ?_, htlevel, htanswer, ?_⟩
        · rw [List.foldlM, hs₁]
          simpa using ht
        · rw [htsamples]
          ext x
          simp [s₁]
  have hall : ∀ a ∈ List.ofFn A, a ∈ distinctSet A := by
    intro a ha
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    simp [distinctSet]
  obtain ⟨t, ht, htlevel, htanswer, htsamples⟩ :=
    hfold (List.ofFn A) (initialState P) (by rfl) (by rfl)
      (by simp [initialState]) hall
  have hrunState : runState P A = pure t := ht
  have hsampleFinal : t.samples = distinctSet A := by
    change t.samples = Finset.univ.image A
    rw [Fin.univ_image_def]
    simpa [initialState] using htsamples
  have hfinish : (finish t).answer = some (F0 A : Real) := by
    simp [finish, htanswer, rate, htlevel, hsampleFinal, F0]
  have hrun : run P A =
      pure (finish t, (finish t).peakSamples * itemBits P) := by
    rw [run, hrunState]
    change PMF.bind (PMF.pure t) (fun s =>
      PMF.pure (finish s, (finish s).peakSamples * itemBits P)) = _
    rw [PMF.pure_bind]
    rfl
  have hexact : Accurate P.eps (F0 A : Real) (some (F0 A : Real)) := by
    simp only [Accurate, Arlib.relErr, Set.mem_Icc]
    have hF : 0 ≤ (F0 A : Real) := Nat.cast_nonneg _
    constructor <;> nlinarith [P.heps.1]
  have hout : finish t ∈ accurateEvent P A := by
    change Accurate P.eps (F0 A : Real) (finish t).answer
    rw [hfinish]
    exact hexact
  rw [hrun]
  have hprob : Arlib.Approximation.outProbR
      (pure (finish t, (finish t).peakSamples * itemBits P))
        (accurateEvent P A) = 1 := by
    rw [Arlib.Approximation.outProbR, Arlib.Approximation.outProb]
    change ((PMF.pure (finish t,
      (finish t).peakSamples * itemBits P)).toOuterMeasure
        {p | p.1 ∈ accurateEvent P A}).toReal = 1
    have hmeasure :
        (PMF.pure (finish t, (finish t).peakSamples * itemBits P)).toOuterMeasure
            {p | p.1 ∈ accurateEvent P A} = 1 := by
      rw [PMF.toOuterMeasure_pure_apply]
      have hp : (finish t, (finish t).peakSamples * itemBits P) ∈
          {p | p.1 ∈ accurateEvent P A} := hout
      rw [if_pos hp]
    rw [hmeasure]
    norm_num
  rw [hprob]
  linarith [P.hdelta.1]

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · deterministic level-zero fold returns the exact distinct count below threshold
-/
