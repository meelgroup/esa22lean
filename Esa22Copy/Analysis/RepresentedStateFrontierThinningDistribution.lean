import Esa22Copy.Analysis.LevelSampleCommonControllers
import Esa22Copy.Analysis.LevelSampleEqOfEqBelow
import Esa22Copy.Analysis.MapEqMapBindOfFiberwise

/-!
# Adaptive frontier thinning after a represented-state refresh

This module isolates the second deferred-decisions calculation in a represented-state
successor.  Conditional on the old state and its refreshed fixed-level sample, the
next unused level frontier realizes exactly a fresh uniform thinning subset.
-/

namespace Esa22Copy

/--
INTERNAL: the next fixed-level sample on a threshold crossing has the same conditional
law as intersecting the refreshed sample with `freshSubset`.
-/
theorem representedState_frontier_thinning_distribution (P : Params) (A : Stream P)
    (r : Nat) (hr : r < P.m)
    (hprefix : ∀ (coins : LevelCoins P) (k r : Nat) (hr : r < P.m),
      levelSample coins A k ⟨r + 1, Nat.succ_lt_succ hr⟩ =
        refresh (A ⟨r, hr⟩) k (coins ⟨r, hr⟩)
          (levelSample coins A k ⟨r, Nat.lt_succ_of_lt hr⟩))
    (hsucc : ∀ (i : Fin (P.m + 1)) (k : Nat) (hk : k ≤ P.m),
      ∃ controller : {a // a ∈ prefixDistinct A i} → Fin P.m,
        Function.Injective controller ∧
          ∀ coins : LevelCoins P,
          levelSample coins A (k + 1) i =
            (levelSample coins A k i).filter fun a =>
              ∃ ha : a ∈ prefixDistinct A i,
                coins (controller ⟨a, ha⟩) ⟨k, Nat.lt_succ_of_le hk⟩ = true)
    (hfrontier : ∀ {I : Type} [Fintype I]
      (controller : I → Fin P.m) (hcontroller : Function.Injective controller)
      (k : Nat) (hk : k ≤ P.m) (E : Set (LevelCoins P)) (wanted : I → Bool),
      (∀ x y : LevelCoins P,
        (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
          (∀ a : I, j ≠ controller a ∨ q ≠ ⟨k, Nat.lt_succ_of_le hk⟩) → x j q = y j q) →
        (x ∈ E ↔ y ∈ E)) →
      (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure
          {coins | coins ∈ E ∧
            ∀ a : I, coins (controller a) ⟨k, Nat.lt_succ_of_le hk⟩ = wanted a} =
        (PMF.uniformOfFintype (LevelCoins P)).toOuterMeasure E *
          (((2 : ENNReal) ^ Fintype.card I)⁻¹))
    (hfresh : ∀ (X : Finset (Item P)) (wanted : {a // a ∈ X} → Bool),
      (freshSubset P).toOuterMeasure
          {Y | ∀ a : {a // a ∈ X}, (a.1 ∈ Y ↔ wanted a = true)} =
        (((2 : ENNReal) ^ X.card)⁻¹))
    (representedState : LevelCoins P → RelaxedState P)
    (hsample : ∀ coins : LevelCoins P,
      (representedState coins).samples =
        levelSample coins A (representedState coins).level
          ⟨r, Nat.lt_succ_of_lt hr⟩)
    (hlevel : ∀ coins : LevelCoins P, (representedState coins).level ≤ r)
    (hcausal : ∀ x y : LevelCoins P,
      (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
        j.val < r → q.val < (representedState x).level → x j q = y j q) →
      representedState x = representedState y) :
    (PMF.uniformOfFintype (LevelCoins P)).map
        (fun coins ↦
          let s := representedState coins
          let refreshed := refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples
          if refreshed.card = threshold P then
            ({ samples :=
                levelSample coins A (s.level + 1) ⟨r + 1, Nat.succ_lt_succ hr⟩
               level := s.level + 1 } : RelaxedState P)
          else
            ({ samples := refreshed, level := s.level } : RelaxedState P)) =
      ((PMF.uniformOfFintype (LevelCoins P)).map
        (fun coins ↦
          let s := representedState coins
          (s, refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples))).bind
        (fun pair ↦
          if pair.2.card = threshold P then
            (freshSubset P).map fun retained ↦
              ({ samples := pair.2 ∩ retained, level := pair.1.level + 1 } :
                RelaxedState P)
          else
            pure ({ samples := pair.2, level := pair.1.level } : RelaxedState P)) := by
  let μ := PMF.uniformOfFintype (LevelCoins P)
  let base : LevelCoins P → RelaxedState P × Finset (Item P) := fun coins =>
    let s := representedState coins
    (s, refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples)
  let output : LevelCoins P → RelaxedState P := fun coins =>
    let s := representedState coins
    let refreshed := refresh (A ⟨r, hr⟩) s.level (coins ⟨r, hr⟩) s.samples
    if refreshed.card = threshold P then
      { samples := levelSample coins A (s.level + 1)
          ⟨r + 1, Nat.succ_lt_succ hr⟩
        level := s.level + 1 }
    else
      { samples := refreshed, level := s.level }
  let kernel : RelaxedState P × Finset (Item P) → PMF (RelaxedState P) := fun pair =>
    if pair.2.card = threshold P then
      (freshSubset P).map fun retained =>
        ({ samples := pair.2 ∩ retained, level := pair.1.level + 1 } : RelaxedState P)
    else
      pure ({ samples := pair.2, level := pair.1.level } : RelaxedState P)
  change μ.map output = (μ.map base).bind kernel
  apply map_eq_map_bind_of_fiberwise
  intro pair target
  have hbaseprob :
      (μ.map base) pair = μ.toOuterMeasure {coins | base coins = pair} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
  by_cases hcross : pair.2.card = threshold P
  · let E : Set (LevelCoins P) := {coins | base coins = pair}
    by_cases hE : E.Nonempty
    · obtain ⟨coins₀, hcoins₀⟩ := hE
      have hbase₀ : base coins₀ = pair := hcoins₀
      have hstate₀ : representedState coins₀ = pair.1 :=
        congrArg Prod.fst hbase₀
      have hrefreshed₀ :
          refresh (A ⟨r, hr⟩) (representedState coins₀).level
              (coins₀ ⟨r, hr⟩) (representedState coins₀).samples = pair.2 :=
        congrArg Prod.snd hbase₀
      rw [hstate₀] at hrefreshed₀
      let k := pair.1.level
      let i : Fin (P.m + 1) := ⟨r + 1, Nat.succ_lt_succ hr⟩
      have hk : k ≤ P.m := by
        change pair.1.level ≤ P.m
        rw [← hstate₀]
        exact (hlevel coins₀).trans (Nat.le_of_lt hr)
      have hsample₀ := hsample coins₀
      rw [hstate₀] at hsample₀
      have hprefix₀ := hprefix coins₀ k r hr
      change levelSample coins₀ A k i = _ at hprefix₀
      rw [← hsample₀, hrefreshed₀] at hprefix₀
      obtain ⟨_commonController, _hcommonInj, _hcommonMem, hcommonSubset⟩ :=
        levelSample_has_common_injective_controller P A i
      have hsubset : pair.2 ⊆ prefixDistinct A i := by
        rw [← hprefix₀]
        exact hcommonSubset coins₀ k
      obtain ⟨controller, hcontroller, hsuccessor⟩ := hsucc i k hk
      let restricted : {a // a ∈ pair.2} → Fin P.m := fun a =>
        controller ⟨a.1, hsubset a.2⟩
      have hrestricted : Function.Injective restricted := by
        intro a b hab
        have hfull :
            (⟨a.1, hsubset a.2⟩ : {x // x ∈ prefixDistinct A i}) =
              ⟨b.1, hsubset b.2⟩ := hcontroller hab
        apply Subtype.ext
        exact congrArg (fun z : {x // x ∈ prefixDistinct A i} => z.1) hfull
      have hforward : ∀ x y : LevelCoins P,
          (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
            (∀ a : {a // a ∈ pair.2},
              j ≠ restricted a ∨ q ≠ ⟨k, Nat.lt_succ_of_le hk⟩) →
              x j q = y j q) →
          x ∈ E → y ∈ E := by
        intro x y hxy hx
        have hbasex : base x = pair := hx
        have hstatex : representedState x = pair.1 :=
          congrArg Prod.fst hbasex
        have hrefreshedx :
            refresh (A ⟨r, hr⟩) (representedState x).level
                (x ⟨r, hr⟩) (representedState x).samples = pair.2 :=
          congrArg Prod.snd hbasex
        rw [hstatex] at hrefreshedx
        have hsamplex := hsample x
        rw [hstatex] at hsamplex
        have hprefixx := hprefix x k r hr
        change levelSample x A k i = _ at hprefixx
        rw [← hsamplex, hrefreshedx] at hprefixx
        have hstatexy : representedState x = representedState y := by
          apply hcausal
          intro j q hj hq
          apply hxy j q
          intro a
          right
          apply Fin.ne_of_val_ne
          have hqk : q.val < k := by
            simpa [k, hstatex] using hq
          simp only [Fin.val_mk]
          omega
        have hstatey : representedState y = pair.1 := hstatexy.symm.trans hstatex
        have hsamplesxy : levelSample x A k i = levelSample y A k i := by
          apply levelSample_eq_of_eq_below P A
          intro j q _hj hq
          apply hxy j q
          intro a
          right
          apply Fin.ne_of_val_ne
          simp only [Fin.val_mk]
          omega
        have hsampley := hsample y
        rw [hstatey] at hsampley
        have hprefixy := hprefix y k r hr
        change levelSample y A k i = _ at hprefixy
        rw [← hsampley] at hprefixy
        have hrefreshedy :
            refresh (A ⟨r, hr⟩) (representedState y).level
                (y ⟨r, hr⟩) (representedState y).samples = pair.2 := by
          rw [hstatey]
          exact hprefixy.symm.trans (hsamplesxy.symm.trans hprefixx)
        change base y = pair
        apply Prod.ext
        · exact hstatey
        · exact hrefreshedy
      have hEinvariant : ∀ x y : LevelCoins P,
          (∀ (j : Fin P.m) (q : Fin (P.m + 1)),
            (∀ a : {a // a ∈ pair.2},
              j ≠ restricted a ∨ q ≠ ⟨k, Nat.lt_succ_of_le hk⟩) →
              x j q = y j q) →
          (x ∈ E ↔ y ∈ E) := by
        intro x y hxy
        constructor
        · exact hforward x y hxy
        · apply hforward y x
          intro j q haway
          exact (hxy j q haway).symm
      have hprefixOfBase : ∀ coins : LevelCoins P, base coins = pair →
          levelSample coins A k i = pair.2 := by
        intro coins hbaseCoins
        have hstateCoins : representedState coins = pair.1 :=
          congrArg Prod.fst hbaseCoins
        have hrefreshedCoins :
            refresh (A ⟨r, hr⟩) (representedState coins).level
                (coins ⟨r, hr⟩) (representedState coins).samples = pair.2 :=
          congrArg Prod.snd hbaseCoins
        rw [hstateCoins] at hrefreshedCoins
        have hsampleCoins := hsample coins
        rw [hstateCoins] at hsampleCoins
        have hprefixCoins := hprefix coins k r hr
        change levelSample coins A k i = _ at hprefixCoins
        rw [← hsampleCoins, hrefreshedCoins] at hprefixCoins
        exact hprefixCoins
      have houtputOfBase : ∀ coins : LevelCoins P, base coins = pair →
          output coins =
            ({ samples := levelSample coins A (k + 1) i, level := k + 1 } :
              RelaxedState P) := by
        intro coins hbaseCoins
        have hstateCoins : representedState coins = pair.1 :=
          congrArg Prod.fst hbaseCoins
        have hrefreshedCoins :
            refresh (A ⟨r, hr⟩) (representedState coins).level
                (coins ⟨r, hr⟩) (representedState coins).samples = pair.2 :=
          congrArg Prod.snd hbaseCoins
        rw [hstateCoins] at hrefreshedCoins
        simp [output, hstateCoins, hrefreshedCoins, hcross, k, i]
      let wanted : {a // a ∈ pair.2} → Bool := fun a => decide (a.1 ∈ target.samples)
      have hfrontierLaw :=
        hfrontier restricted hrestricted k hk E wanted hEinvariant
      change μ.toOuterMeasure
          {coins | coins ∈ E ∧
            ∀ a : {a // a ∈ pair.2},
              coins (restricted a) ⟨k, Nat.lt_succ_of_le hk⟩ = wanted a} =
        μ.toOuterMeasure E *
          (((2 : ENNReal) ^ Fintype.card {a // a ∈ pair.2})⁻¹) at hfrontierLaw
      have hfreshLaw := hfresh pair.2 wanted
      rw [Fintype.card_coe] at hfrontierLaw
      let thinned : Finset (Item P) → RelaxedState P := fun retained =>
        { samples := pair.2 ∩ retained, level := k + 1 }
      have hkernelCross : kernel pair = (freshSubset P).map thinned := by
        simp [kernel, hcross, thinned, k]
      by_cases htargetLevel : target.level = k + 1
      · by_cases htargetSubset : target.samples ⊆ pair.2
        · have hfreshEvent :
              {retained | thinned retained = target} =
                {retained | ∀ a : {a // a ∈ pair.2},
                  (a.1 ∈ retained ↔ wanted a = true)} := by
            ext retained
            constructor
            · intro hretained a
              have hsamples := congrArg RelaxedState.samples hretained
              change pair.2 ∩ retained = target.samples at hsamples
              have hmem := congrArg (fun X : Finset (Item P) => a.1 ∈ X) hsamples
              simpa [wanted, a.2] using hmem
            · intro hretained
              have hsamples : pair.2 ∩ retained = target.samples := by
                ext a
                simp only [Finset.mem_inter]
                constructor
                · rintro ⟨haX, haRetained⟩
                  have ha := (hretained ⟨a, haX⟩).mp haRetained
                  simpa [wanted] using ha
                · intro haTarget
                  have haX := htargetSubset haTarget
                  refine ⟨haX, ?_⟩
                  apply (hretained ⟨a, haX⟩).mpr
                  simpa [wanted] using haTarget
              cases target
              simp only [thinned, RelaxedState.mk.injEq] at htargetLevel ⊢
              exact ⟨hsamples, htargetLevel.symm⟩
          have hkernelProbability :
              kernel pair target =
                (freshSubset P).toOuterMeasure
                  {retained | ∀ a : {a // a ∈ pair.2},
                    (a.1 ∈ retained ↔ wanted a = true)} := by
            rw [hkernelCross, ← PMF.toOuterMeasure_apply_singleton,
              PMF.toOuterMeasure_map_apply]
            change (freshSubset P).toOuterMeasure {retained | thinned retained = target} = _
            rw [hfreshEvent]
          have houtputEvent :
              {coins | base coins = pair ∧ output coins = target} =
                {coins | coins ∈ E ∧
                  ∀ a : {a // a ∈ pair.2},
                    coins (restricted a) ⟨k, Nat.lt_succ_of_le hk⟩ = wanted a} := by
            ext coins
            constructor
            · rintro ⟨hbaseCoins, houtputCoins⟩
              refine ⟨hbaseCoins, ?_⟩
              have hnext :
                  ({ samples := levelSample coins A (k + 1) i, level := k + 1 } :
                    RelaxedState P) = target :=
                (houtputOfBase coins hbaseCoins).symm.trans houtputCoins
              have hnextSamples := congrArg RelaxedState.samples hnext
              change levelSample coins A (k + 1) i = target.samples at hnextSamples
              intro a
              rw [Bool.eq_iff_iff]
              constructor
              · intro hbit
                have haNext : a.1 ∈ levelSample coins A (k + 1) i := by
                  rw [hsuccessor coins, hprefixOfBase coins hbaseCoins]
                  refine Finset.mem_filter.mpr ⟨a.2, ?_⟩
                  refine ⟨hsubset a.2, ?_⟩
                  simpa [restricted] using hbit
                have haTarget : a.1 ∈ target.samples := by
                  rw [← hnextSamples]
                  exact haNext
                simpa [wanted] using haTarget
              · intro hwanted
                have haTarget : a.1 ∈ target.samples := by
                  simpa [wanted] using hwanted
                have haNext : a.1 ∈ levelSample coins A (k + 1) i := by
                  rw [hnextSamples]
                  exact haTarget
                rw [hsuccessor coins, hprefixOfBase coins hbaseCoins] at haNext
                obtain ⟨_haX, haPrefix, hbit⟩ := Finset.mem_filter.mp haNext
                simpa [restricted] using hbit
            · rintro ⟨hbaseCoins, hpattern⟩
              refine ⟨hbaseCoins, ?_⟩
              have hnextSamples :
                  levelSample coins A (k + 1) i = target.samples := by
                rw [hsuccessor coins, hprefixOfBase coins hbaseCoins]
                ext a
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨haX, haPrefix, hbit⟩
                  have hp := hpattern ⟨a, haX⟩
                  have hrestrictedBit :
                      coins (restricted ⟨a, haX⟩) ⟨k, Nat.lt_succ_of_le hk⟩ = true := by
                    simpa [restricted] using hbit
                  rw [hrestrictedBit] at hp
                  simpa [wanted] using hp.symm
                · intro haTarget
                  have haX := htargetSubset haTarget
                  refine ⟨haX, hsubset haX, ?_⟩
                  have hp := hpattern ⟨a, haX⟩
                  have hwanted : wanted ⟨a, haX⟩ = true := by
                    simpa [wanted] using haTarget
                  rw [hwanted] at hp
                  simpa [restricted] using hp
              have hnext :
                  ({ samples := levelSample coins A (k + 1) i, level := k + 1 } :
                    RelaxedState P) = target := by
                cases target
                simp only [RelaxedState.mk.injEq] at htargetLevel ⊢
                exact ⟨hnextSamples, htargetLevel.symm⟩
              exact (houtputOfBase coins hbaseCoins).trans hnext
          rw [houtputEvent, hfrontierLaw, ← hfreshLaw, ← hkernelProbability]
          rw [← hbaseprob]
        · have hnextSubset : ∀ coins : LevelCoins P, base coins = pair →
              levelSample coins A (k + 1) i ⊆ pair.2 := by
            intro coins hbaseCoins
            rw [hsuccessor coins, hprefixOfBase coins hbaseCoins]
            exact Finset.filter_subset _ _
          have hevent :
              {coins | base coins = pair ∧ output coins = target} = ∅ := by
            ext coins
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hbaseCoins, houtputCoins⟩
            apply htargetSubset
            intro a haTarget
            have hnext :
                ({ samples := levelSample coins A (k + 1) i, level := k + 1 } :
                  RelaxedState P) = target :=
              (houtputOfBase coins hbaseCoins).symm.trans houtputCoins
            have hnextSamples := congrArg RelaxedState.samples hnext
            change levelSample coins A (k + 1) i = target.samples at hnextSamples
            apply hnextSubset coins hbaseCoins
            rw [hnextSamples]
            exact haTarget
          have hthinnedNe : ∀ retained, thinned retained ≠ target := by
            intro retained hretained
            apply htargetSubset
            intro a haTarget
            have hsamples := congrArg RelaxedState.samples hretained
            change pair.2 ∩ retained = target.samples at hsamples
            rw [← hsamples] at haTarget
            exact Finset.mem_of_mem_inter_left haTarget
          have hkernelZero : kernel pair target = 0 := by
            rw [hkernelCross, PMF.map_apply]
            rw [ENNReal.tsum_eq_zero]
            intro retained
            rw [if_neg (Ne.symm (hthinnedNe retained))]
          rw [hevent, hkernelZero]
          simp
      · have hevent :
            {coins | base coins = pair ∧ output coins = target} = ∅ := by
          ext coins
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hbaseCoins, houtputCoins⟩
          have hnext :
              ({ samples := levelSample coins A (k + 1) i, level := k + 1 } :
                RelaxedState P) = target :=
            (houtputOfBase coins hbaseCoins).symm.trans houtputCoins
          have hlevelEq := congrArg RelaxedState.level hnext
          exact htargetLevel hlevelEq.symm
        have hthinnedNe : ∀ retained, thinned retained ≠ target := by
          intro retained hretained
          have hlevelEq := congrArg RelaxedState.level hretained
          exact htargetLevel hlevelEq.symm
        have hkernelZero : kernel pair target = 0 := by
          rw [hkernelCross, PMF.map_apply]
          rw [ENNReal.tsum_eq_zero]
          intro retained
          rw [if_neg (Ne.symm (hthinnedNe retained))]
        rw [hevent, hkernelZero]
        simp
    · have hEempty : E = ∅ := by
        ext coins
        constructor
        · intro hcoins
          exact False.elim (hE ⟨coins, hcoins⟩)
        · simp
      have hevent :
          {coins | base coins = pair ∧ output coins = target} = ∅ := by
        ext coins
        constructor
        · intro hcoins
          have : coins ∈ E := hcoins.1
          rw [hEempty] at this
          exact False.elim (by simpa using this)
        · simp
      have hmapzero : (μ.map base) pair = 0 := by
        rw [hbaseprob]
        change μ.toOuterMeasure E = 0
        rw [hEempty]
        simp
      rw [hevent, hmapzero]
      simp
  · let deterministic : RelaxedState P :=
      { samples := pair.2, level := pair.1.level }
    have houtput : ∀ coins, base coins = pair → output coins = deterministic := by
      intro coins hb
      have hs : representedState coins = pair.1 := congrArg Prod.fst hb
      have hX : refresh (A ⟨r, hr⟩) (representedState coins).level
          (coins ⟨r, hr⟩) (representedState coins).samples = pair.2 :=
        congrArg Prod.snd hb
      rw [hs] at hX
      simp [output, hs, hX, hcross, deterministic]
    by_cases ht : deterministic = target
    · have hevent :
          {coins | base coins = pair ∧ output coins = target} =
            {coins | base coins = pair} := by
        ext coins
        constructor
        · exact fun h => h.1
        · intro hb
          exact ⟨hb, (houtput coins hb).trans ht⟩
      rw [hevent, ← hbaseprob]
      have hkernel : kernel pair = pure deterministic := by
        simp [kernel, hcross, deterministic]
      rw [hkernel, ht]
      have hpure : (pure target : PMF (RelaxedState P)) target = 1 :=
        PMF.pure_apply_self target
      rw [hpure, mul_one]
    · have hevent :
          {coins | base coins = pair ∧ output coins = target} = ∅ := by
        ext coins
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hb, hout⟩
        have hh := houtput coins hb
        rw [hout] at hh
        exact ht hh.symm
      rw [hevent]
      have htn : target ≠ deterministic := Ne.symm ht
      have hpure : PMF.pure deterministic target = 0 :=
        PMF.pure_apply_of_ne deterministic target htn
      have hkernel : kernel pair = pure deterministic := by
        simp [kernel, hcross, deterministic]
      rw [hkernel]
      have hpure' : (pure deterministic : PMF (RelaxedState P)) target = 0 := hpure
      rw [hpure', mul_zero]
      simp

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · proved · reconstructed the PMF from exact adaptive-frontier laws on each refreshed-state fiber
* r10 · reduced · isolated the adaptive-frontier half of the crossing-update law
-/
