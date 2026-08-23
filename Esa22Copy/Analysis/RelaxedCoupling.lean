import Esa22Copy.Analysis.RelaxedRunLevelSampleCouplingAux
import Esa22Copy.Analysis.LevelSampleIndependence
import Esa22Copy.Analysis.LevelSamplePrefixSucc
import Esa22Copy.Analysis.LevelSampleSuccLevel
import Esa22Copy.Analysis.UniformTableFreshFrontier

/-!
# Coupling the relaxed algorithm to fixed-level samples

The coupling exposes one uniform table of occurrence blocks while preserving the
literal relaxed-state marginal.  Every supported coupled state agrees with the
fixed-level set selected by its adaptive final level.
-/

namespace Esa22Copy

/--
INTERNAL: the relaxed algorithm restricted to the first `i` stream positions.
-/
noncomputable def relaxedRunPrefix (P : Params) (A : Stream P) (i : Fin (P.m + 1)) :
    PMF (RelaxedState P) :=
  ((List.ofFn A).take i.val).foldlM (fun s a => relaxedStep P a s)
    { samples := ∅, level := 0 }

/--
INTERNAL: a joint distribution realizes the prefix-by-prefix Algorithm 2/3 coupling.
-/
theorem relaxedRun_levelSample_coupling (P : Params) (A : Stream P)
    (i : Fin (P.m + 1)) :
    ∃ coupling : PMF (RelaxedState P × LevelCoins P),
      coupling.map Prod.fst = relaxedRunPrefix P A i ∧
      coupling.map Prod.snd = freshLevelCoins P ∧
      ∀ z ∈ coupling.support,
        z.1.samples = levelSample z.2 A z.1.level i := by
  obtain ⟨coupling, hfst, hsnd, hsupport⟩ :=
    relaxedRun_levelSample_coupling_aux P A i
      (levelSample_prefix_succ P A) (levelSample_succ_level P A)
      (uniform_table_fresh_frontier P)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simpa only [relaxedRunPrefix] using hfst
  · simpa only [freshLevelCoins] using hsnd
  · intro z hz
    exact (hsupport z hz).1

end Esa22Copy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · closed the public theorem from the strengthened prefix coupling
-/
