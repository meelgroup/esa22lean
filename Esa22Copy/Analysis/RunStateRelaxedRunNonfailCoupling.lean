import Esa22Copy.Analysis.StepNonfailCoupling

/-!
# Whole-run original-to-relaxed coupling

Sequentially composing the one-step couplings gives a joint law for the two
state machines whose supported outcomes retain the nonfailure simulation.
-/

namespace Esa22Copy

/--
INTERNAL: the complete original and relaxed state distributions admit a coupling
that preserves their common fields whenever the original execution is nonfailed.
-/
theorem runState_relaxedRun_nonfail_coupling (P : Params) (A : Stream P) :
    ∃ κ : PMF (State P × RelaxedState P),
      κ.map Prod.fst = runState P A ∧
      κ.map Prod.snd = relaxedRun P A ∧
      ∀ z ∈ κ.support, NonfailRel z.1 z.2 := by
  classical
  have map_bindOnSupport {γ : Type} (p : PMF (State P × RelaxedState P))
      (K : (x : State P × RelaxedState P) → x ∈ p.support →
        PMF (State P × RelaxedState P))
      (f : State P × RelaxedState P → γ) :
      PMF.map f (p.bindOnSupport K) =
        p.bindOnSupport (fun x hx => PMF.map f (K x hx)) := by
    rw [← PMF.bind_pure_comp f (p.bindOnSupport K)]
    rw [← PMF.bindOnSupport_eq_bind (p.bindOnSupport K) (PMF.pure ∘ f)]
    rw [PMF.bindOnSupport_bindOnSupport]
    simp only [PMF.bindOnSupport_eq_bind, PMF.bind_pure_comp]
  have foldlM_nonfail_coupling_from_related (xs : List (Item P))
      (s : State P) (r : RelaxedState P) (hrel : NonfailRel s r) :
      ∃ κ : PMF (State P × RelaxedState P),
        κ.map Prod.fst = xs.foldlM (fun s a => step P a s) s ∧
        κ.map Prod.snd = xs.foldlM (fun r a => relaxedStep P a r) r ∧
        ∀ z ∈ κ.support, NonfailRel z.1 z.2 := by
    induction xs generalizing s r with
    | nil =>
        refine ⟨PMF.pure (s, r), ?_, ?_, ?_⟩
        · simp only [PMF.pure_map, List.foldlM_nil]
          rfl
        · simp only [PMF.pure_map, List.foldlM_nil]
          rfl
        · intro z hz
          have hz' : z = (s, r) := by
            simpa only [PMF.mem_support_pure_iff] using hz
          subst z
          exact hrel
    | cons a tail ih =>
        obtain ⟨κ₁, h₁fst, h₁snd, h₁rel⟩ := step_nonfail_coupling a s r hrel
        have hcont : ∀ (z : State P × RelaxedState P) (hz : z ∈ κ₁.support),
            ∃ κ : PMF (State P × RelaxedState P),
              κ.map Prod.fst = tail.foldlM (fun s a => step P a s) z.1 ∧
              κ.map Prod.snd = tail.foldlM (fun r a => relaxedStep P a r) z.2 ∧
              ∀ y ∈ κ.support, NonfailRel y.1 y.2 := by
          intro z hz
          exact ih z.1 z.2 (h₁rel z hz)
        choose K hKfst hKsnd hKrel using hcont
        refine ⟨κ₁.bindOnSupport K, ?_, ?_, ?_⟩
        · calc
            PMF.map Prod.fst (κ₁.bindOnSupport K) =
                κ₁.bindOnSupport (fun z hz => PMF.map Prod.fst (K z hz)) :=
              map_bindOnSupport κ₁ K Prod.fst
            _ = κ₁.bindOnSupport
                  (fun z _ => tail.foldlM (fun s a => step P a s) z.1) := by
              congr 1
              funext z hz
              exact hKfst z hz
            _ = κ₁.bind (fun z => tail.foldlM (fun s a => step P a s) z.1) :=
              PMF.bindOnSupport_eq_bind _ _
            _ = (κ₁.map Prod.fst).bind
                  (fun s => tail.foldlM (fun s a => step P a s) s) := by
              rw [PMF.bind_map]
              rfl
            _ = (step P a s).bind
                  (fun s => tail.foldlM (fun s a => step P a s) s) := by
              rw [h₁fst]
            _ = (a :: tail).foldlM (fun s a => step P a s) s := by
              rw [List.foldlM_cons]
              rfl
        · calc
            PMF.map Prod.snd (κ₁.bindOnSupport K) =
                κ₁.bindOnSupport (fun z hz => PMF.map Prod.snd (K z hz)) :=
              map_bindOnSupport κ₁ K Prod.snd
            _ = κ₁.bindOnSupport
                  (fun z _ => tail.foldlM (fun r a => relaxedStep P a r) z.2) := by
              congr 1
              funext z hz
              exact hKsnd z hz
            _ = κ₁.bind (fun z => tail.foldlM (fun r a => relaxedStep P a r) z.2) :=
              PMF.bindOnSupport_eq_bind _ _
            _ = (κ₁.map Prod.snd).bind
                  (fun r => tail.foldlM (fun r a => relaxedStep P a r) r) := by
              rw [PMF.bind_map]
              rfl
            _ = (relaxedStep P a r).bind
                  (fun r => tail.foldlM (fun r a => relaxedStep P a r) r) := by
              rw [h₁snd]
            _ = (a :: tail).foldlM (fun r a => relaxedStep P a r) r := by
              rw [List.foldlM_cons]
              rfl
        · intro y hy
          obtain ⟨z, hz, hyK⟩ := (PMF.mem_support_bindOnSupport_iff K y).mp hy
          exact hKrel z hz y hyK
  let r₀ : RelaxedState P := { samples := ∅, level := 0 }
  have hinitial : NonfailRel (initialState P) r₀ := by
    simp [NonfailRel, initialState, finish, failEvent, r₀]
  obtain ⟨κ, hfst, hsnd, hrel⟩ :=
    foldlM_nonfail_coupling_from_related (List.ofFn A)
      (initialState P) r₀ hinitial
  refine ⟨κ, ?_, ?_, hrel⟩
  · simpa only [runState] using hfst
  · simpa only [relaxedRun, r₀] using hsnd

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · composed dependent one-step couplings over the stream fold
* r1 · reduced · isolated fold-level composition of the one-step simulation
-/
