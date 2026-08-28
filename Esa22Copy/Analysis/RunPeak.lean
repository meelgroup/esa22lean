import Esa22Copy.Interface.Pseudocode

/-!
# The sample set stays below the threshold

Reachable states of the original algorithm never hold more than `threshold P`
items, and while a run is still going they hold strictly fewer.  A step can
provisionally reach the threshold, and then either thins below it or records
bottom and becomes stationary.

This used to be a bound on a `peakSamples` *field* — a high-water mark the model
and the program each maintained by hand, with the bridge pinning the two to each
other.  The field is gone.  What is left is the invariant, which is the honest
part and is what `Analysis/SpaceBound.lean` feeds to
`Arlib.Computation.Profile.peak_foldProfiles_le` to bound the program's own
profile: *from a state below the ceiling, an arrival's excursion is at most the
headroom.*
-/

namespace Esa22Copy

/--
INTERNAL: packages the three facts about a reachable state needed by the step induction.
-/
def StateSpaceInvariant (P : Params) (s : State P) : Prop :=
  s.samples.card ≤ threshold P ∧ (s.answer = none → s.samples.card < threshold P)

/--
INTERNAL: positivity of the paper's threshold under the positivity fields of `Params`.
-/
theorem threshold_pos (P : Params) : 0 < threshold P := by
  unfold threshold
  rw [Nat.ceil_pos]
  apply mul_pos
  · have heps : 0 < P.eps := P.heps.1
    positivity
  · apply Real.logb_pos (by norm_num : (1 : Real) < 2)
    have hm : (1 : Real) ≤ P.m := by exact_mod_cast P.hm
    have hdelta : 0 < P.delta := P.hdelta.1
    apply (lt_div_iff₀ hdelta).2
    nlinarith [P.hdelta.2]

/--
INTERNAL: erase-then-optional-insert grows a finite sample by at most one element.
-/
theorem refresh_card_le_succ {P : Params} (a : Item P) (level : Nat)
    (bits : BitBlock P) (X : Finset (Item P)) :
    (refresh a level bits X).card ≤ X.card + 1 := by
  unfold refresh
  split
  · exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (Finset.card_erase_le) 1)
  · exact Finset.card_erase_le.trans (Nat.le_add_right X.card 1)

/--
INTERNAL: one supported transition preserves the deterministic state-space invariant.
-/
theorem step_preserves_space (P : Params) (a : Item P) {s t : State P}
    (hs : StateSpaceInvariant P s) (ht : t ∈ (step P a s).support) :
    StateSpaceInvariant P t := by
  rcases hs with ⟨hsamples, hrunning⟩
  cases hanswer : s.answer with
  | some answer =>
      rw [step, hanswer] at ht
      change t ∈ (PMF.pure s).support at ht
      rw [PMF.mem_support_pure_iff] at ht
      subst t
      exact ⟨hsamples, hrunning⟩
  | none =>
      rw [step, hanswer, PMF.mem_support_bind_iff] at ht
      obtain ⟨bits, _, ht⟩ := ht
      let refreshed := refresh a s.level bits s.samples
      have hrefreshed : refreshed.card ≤ threshold P := by
        have hgrow := refresh_card_le_succ a s.level bits s.samples
        change refreshed.card ≤ s.samples.card + 1 at hgrow
        have hbelow := hrunning hanswer
        omega
      by_cases hthreshold : refreshed.card = threshold P
      · rw [if_pos hthreshold, PMF.mem_support_bind_iff] at ht
        obtain ⟨retained, _, ht⟩ := ht
        change t ∈ (PMF.pure
          { samples := refreshed ∩ retained
            level := s.level + 1
            answer := if (refreshed ∩ retained).card = threshold P
              then some none else none }).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        have hinter : (refreshed ∩ retained).card ≤ threshold P :=
          (Finset.card_le_card Finset.inter_subset_left).trans hrefreshed
        refine ⟨hinter, ?_⟩
        intro hnone
        change (refreshed ∩ retained).card < threshold P
        by_cases heq : (refreshed ∩ retained).card = threshold P
        · simp [heq] at hnone
        · omega
      · rw [if_neg hthreshold] at ht
        change t ∈ (PMF.pure
          { samples := refreshed
            level := s.level
            answer := none }).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        subst t
        refine ⟨hrefreshed, ?_⟩
        intro
        change refreshed.card < threshold P
        omega

/--
INTERNAL: every state in the support of the original fold satisfies the space invariant.
-/
theorem runState_space_invariant (P : Params) (A : Stream P) (s : State P)
    (hs : s ∈ (runState P A).support) : StateSpaceInvariant P s := by
  have fold_preserves : ∀ (l : List (Item P)) (s₀ t : State P),
      StateSpaceInvariant P s₀ →
      t ∈ (l.foldlM (fun state a => step P a state) s₀).support →
      StateSpaceInvariant P t := by
    intro l
    induction l with
    | nil =>
        intro s₀ t hs₀ ht
        change t ∈ (PMF.pure s₀).support at ht
        rw [PMF.mem_support_pure_iff] at ht
        simpa [ht] using hs₀
    | cons a l ih =>
        intro s₀ t hs₀ ht
        rw [List.foldlM] at ht
        change t ∈ (PMF.bind (step P a s₀)
          (fun u => l.foldlM (fun state a => step P a state) u)).support at ht
        rw [PMF.mem_support_bind_iff] at ht
        obtain ⟨u, hu, ht⟩ := ht
        exact ih u t (step_preserves_space P a hs₀ hu) ht
  apply fold_preserves (List.ofFn A) (initialState P) s
  · exact ⟨Nat.zero_le _, fun _ => threshold_pos P⟩
  · exact hs

/--
PAPER: main.tex:1189-1191, the maintained sample set never exceeds the threshold.

Stated about the *state*, which is what the paper's sentence is about.  It used
to be stated about `outcome.1.peakSamples`, a field of the returned payload; that
field recorded a number the model computed for itself, so the theorem bounded the
model's bookkeeping rather than the algorithm's storage.  The bound on what the
program holds is `Analysis/SpaceBound.lean`'s, and it is an operator applied to
the program's profile.
-/
theorem runState_card_le_threshold (P : Params) (A : Stream P) (s : State P)
    (hs : s ∈ (runState P A).support) : s.samples.card ≤ threshold P :=
  (runState_space_invariant P A s hs).1

end Esa22Copy
