import Arlib.Probability.Chernoff
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Chernoff concentration from a complete Bernoulli pattern law

This module states the bridge from a distribution described by the probability of every
complete Boolean membership pattern to Arlib's product-space multiplicative Chernoff bound.
-/

namespace Esa22Copy

/--
INTERNAL: transport the sharp two-sided multiplicative Chernoff bound from an explicit
Bernoulli product space to any finite sample having the same complete-pattern law.
-/
theorem bernoulli_pattern_chernoff_relErr
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : PMF Ω) (X : Ω → I → Bool) (k : Nat) (ε : Real)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hpattern : ∀ wanted : I → Bool,
      ν.toOuterMeasure
          {ω | ∀ a : I, X ω a = wanted a} =
        ∏ a : I,
          if wanted a then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹) :
    (ν.toOuterMeasure
        {ω | ((Finset.univ.filter fun a => X ω a).card : Real) /
              ((1 / 2 : Real) ^ k) ∉
          Arlib.relErr ε (Fintype.card I : Real)}).toReal ≤
      2 * Real.exp
        (-(ε ^ 2 * ((Fintype.card I : Real) * (1 / 2 : Real) ^ k)) / 3) := by
  classical
  let J := Fin (Fintype.card I)
  let e : I ≃ J := Fintype.equivFin I
  let Y : Ω → J → Bool := fun ω j => X ω (e.symm j)
  let p : Real := (1 / 2 : Real) ^ k
  let coinMass : J → Bool → Real := fun _ b => if b then p else 1 - p
  have hp0 : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hmass0 : ∀ a b, 0 ≤ coinMass a b := by
    intro a b
    cases b <;> simp [coinMass, hp0.le, hp1]
  have hmass1 : ∀ a, ∑ b, coinMass a b = 1 := by
    intro a
    simp [coinMass]
  let bad : (J → Bool) → Prop := fun wanted =>
    ((Finset.univ.filter fun a => wanted a).card : Real) / p ∉
      Arlib.relErr ε (Fintype.card J : Real)
  have hq : (((2 : ENNReal) ^ k)⁻¹).toReal = p := by
    simp [p, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hqle : ((2 : ENNReal) ^ k)⁻¹ ≤ 1 := by
    exact ENNReal.inv_le_one.2 (one_le_pow₀ (by norm_num))
  have hpatternReal : ∀ wanted : J → Bool,
      ((ν.map Y) wanted).toReal = ∏ j : J, coinMass j (wanted j) := by
    intro wanted
    rw [← PMF.toOuterMeasure_apply_singleton,
      PMF.toOuterMeasure_map_apply]
    rw [show Y ⁻¹' {wanted} = {ω | ∀ a : I, X ω a = wanted (e a)} by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · intro h a
        have := congrFun h (e a)
        simpa [Y] using this
      · intro h
        funext j
        simpa [Y] using h (e.symm j)]
    rw [hpattern (fun a => wanted (e a))]
    rw [ENNReal.toReal_prod]
    calc
      (∏ a : I, (if wanted (e a) then ((2 : ENNReal) ^ k)⁻¹
          else 1 - ((2 : ENNReal) ^ k)⁻¹).toReal) =
          ∏ a : I, coinMass (e a) (wanted (e a)) := by
            apply Finset.prod_congr rfl
            intro a _
            cases hw : wanted (e a)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rw [ENNReal.toReal_sub_of_le hqle (by simp), ENNReal.toReal_one, hq]
              rfl
            · change (((2 : ENNReal) ^ k)⁻¹).toReal = p
              exact hq
      _ = ∏ j : J, coinMass j (wanted j) :=
        Equiv.prod_comp e (fun j => coinMass j (wanted j))
  have hprob :
      (ν.toOuterMeasure {ω | bad (Y ω)}).toReal =
        (Arlib.Probability.prodSpace coinMass hmass0 hmass1).toFinProb.Pr
          (Finset.univ.filter bad : Finset (J → Bool)) := by
    rw [show {ω | bad (Y ω)} = Y ⁻¹' {wanted | bad wanted} by rfl]
    rw [← PMF.toOuterMeasure_map_apply Y ν {wanted | bad wanted}]
    rw [show {wanted | bad wanted} =
        (↑(Finset.univ.filter bad) : Set (J → Bool)) by ext wanted; simp]
    rw [PMF.toOuterMeasure_apply_finset]
    rw [ENNReal.toReal_sum (fun a _ => (ν.map Y).apply_ne_top a)]
    unfold Arlib.Probability.FinProb.Pr
    apply Finset.sum_congr rfl
    intro wanted _
    rw [hpatternReal wanted, Arlib.Probability.prodSpace_mass]
  have hchernoff := Arlib.Probability.chernoff_two_sided
    coinMass hmass0 hmass1 (Finset.univ : Finset J)
    (fun _ => {true}) hε0 hε1
  have hcardJ : Fintype.card J = Fintype.card I := by
    simp [J]
  have hmean : Arlib.Probability.indicMean coinMass
      (Finset.univ : Finset J) (fun _ => {true}) =
        (Fintype.card J : Real) * p := by
    simp [Arlib.Probability.indicMean, coinMass]
  have bad_iff_abs (c N : Real) :
      c / p ∉ Arlib.relErr ε N ↔ ε * (N * p) < |c - N * p| := by
    simp only [Arlib.relErr, Set.mem_Icc, not_and_or]
    push Not
    rw [lt_abs]
    constructor
    · intro h
      rcases h with h | h
      · right
        have hc := (div_lt_iff₀ hp0).1 h
        calc
          ε * (N * p) = N * p - (1 - ε) * N * p := by ring
          _ < N * p - c := sub_lt_sub_left hc _
          _ = -(c - N * p) := by ring
      · left
        have hc := (lt_div_iff₀ hp0).1 h
        calc
          ε * (N * p) = (1 + ε) * N * p - N * p := by ring
          _ < c - N * p := sub_lt_sub_right hc _
    · intro h
      rcases h with h | h
      · right
        apply (lt_div_iff₀ hp0).2
        calc
          (1 + ε) * N * p = ε * (N * p) + N * p := by ring
          _ < (c - N * p) + N * p := by
            simpa [add_comm] using add_lt_add_right h (N * p)
          _ = c := by ring
      · left
        apply (div_lt_iff₀ hp0).2
        have hh : ε * (N * p) < N * p - c := by
          simpa only [neg_sub] using h
        calc
          c = N * p - (N * p - c) := by ring
          _ < N * p - ε * (N * p) := sub_lt_sub_left hh _
          _ = (1 - ε) * N * p := by ring
  have hbadEvent :
      (Finset.univ.filter bad : Finset (J → Bool)) =
        Finset.univ.filter (fun wanted : J → Bool =>
          ε * Arlib.Probability.indicMean coinMass
              (Finset.univ : Finset J) (fun _ => {true}) <
            |(Arlib.Probability.indicCount (Finset.univ : Finset J)
                (fun _ => {true}) wanted : Real) -
              Arlib.Probability.indicMean coinMass
                (Finset.univ : Finset J) (fun _ => {true})|) := by
    ext wanted
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hmean]
    simp only [Arlib.Probability.indicCount, Finset.mem_singleton]
    change bad wanted ↔ ε * ((Fintype.card J : Real) * p) <
      |((Finset.univ.filter fun j => wanted j).card : Real) -
        (Fintype.card J : Real) * p|
    exact bad_iff_abs _ _
  have hcount : ∀ ω : Ω,
      (Finset.univ.filter fun a : I => X ω a).card =
        (Finset.univ.filter fun j : J => Y ω j).card := by
    intro ω
    apply Finset.card_bij (fun a _ => e a)
    · intro a ha
      simpa [Y] using ha
    · intro a₁ _ a₂ _ h
      exact e.injective h
    · intro j hj
      refine ⟨e.symm j, ?_, ?_⟩
      · simpa [Y] using hj
      · exact e.apply_symm_apply j
  rw [show {ω | ((Finset.univ.filter fun a => X ω a).card : Real) /
          ((1 / 2 : Real) ^ k) ∉ Arlib.relErr ε (Fintype.card I : Real)} =
      {ω | bad (Y ω)} by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [hcount]
        simp [bad, p, J], hprob, hbadEvent]
  simpa [hmean, p, hcardJ] using hchernoff

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · transported the pushed-forward complete-pattern law pointwise to
  Arlib's Boolean `prodSpace` and applied `chernoff_two_sided`
* r3 · open · isolated transport from a complete Boolean pattern law to Arlib's
  explicit-product `chernoff_two_sided`
-/
