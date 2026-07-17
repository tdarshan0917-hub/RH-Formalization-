import RHFormalization.AdmissibleFirstOrderVanish
import RHFormalization.AdmissibleResidualUniform
import RHFormalization.AdmissibleFreeTailAssembly
import RHFormalization.AdmissibleFreeFH
import RHFormalization.AdmissiblePrimeFirstOrderSplit
import RHFormalization.AdmissibleGalerkinEndpoint

/-!
# FRONT F CLOSED: the admissible `DFHLimitData` instance

Three-epsilon assembly of the banked layers along the admissible net:

`F_stage = admissibleFreeStage + FirstOrderWindow + SecondResolventResidual`

* free layer → `FHadmFree` (Brick 1, banked eps-N),
* first-order window → 0 (Gate 2 by vanishing, banked eps-N),
* second-resolvent residual → 0 (Brick 4b, banked eps-N),

hence `F_stage(α n) → FHadmFree` uniformly on Ω-compacts, and
`FHadm = FHadmFree` with holomorphy already banked.  This yields the full
`DFHLimitData galerkinStagePackage` instance at
`alpha = admissibleGalerkinStageSeq` — the F-slot of the V10 endpoint —
and the reduced endpoint `RH_from_admissible_R` consuming ONLY Front R.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped BigOperators Classical Topology

/-- **Three-epsilon assembly**: the full admissible F-stage converges to
`FHadmFree` uniformly on Ω-compacts, in the exact
`DFHLimitData.h_F_stage_to_FH` shape. -/
theorem admissible_F_stage_to_FHadmFree :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
            (FHadmFree s) < ε := by
  intro K hK hKO ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  have hfree := admissibleFreeStage_to_FHadmFree K hK hKO (ε / 3) hε3
  obtain ⟨N₁, hFOW⟩ := FirstOrderWindow_epsN K hK hKO (ε / 3) hε3
  obtain ⟨N₂, hres⟩ := SecondResolventResidual_epsN K hK hKO (ε / 3) hε3
  have hFOW' : ∀ᶠ n in Filter.atTop, ∀ n' ∈ K,
      ‖FirstOrderWindow n n'‖ ≤ ε / 3 := by
    first
      | exact Filter.eventually_atTop.mpr ⟨N₁, hFOW⟩
      | exact Filter.eventually_atTop.2 ⟨N₁, hFOW⟩
  have hres' : ∀ᶠ n in Filter.atTop, ∀ n' ∈ K,
      ‖SecondResolventResidual n n'‖ ≤ ε / 3 := by
    first
      | exact Filter.eventually_atTop.mpr ⟨N₂, hres⟩
      | exact Filter.eventually_atTop.2 ⟨N₂, hres⟩
  filter_upwards [hfree, hFOW', hres'] with n h1 h2 h3
  intro s hs
  have hsΩ : s ∈ Ω := hKO hs
  rw [package_F_stage_eq_free_add_prime n s,
    FadmPrimeStage_eq_first_plus_second n hsΩ]
  rw [dist_eq_norm]
  have key : admissibleFreeStage n s
        + (FirstOrderWindow n s + SecondResolventResidual n s)
        - FHadmFree s
      = ((admissibleFreeStage n s - FHadmFree s) + FirstOrderWindow n s)
          + SecondResolventResidual n s := by
    ring
  rw [key]
  have hA : ‖admissibleFreeStage n s - FHadmFree s‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact h1 s hs
  have hB : ‖FirstOrderWindow n s‖ ≤ ε / 3 := h2 s hs
  have hCn : ‖SecondResolventResidual n s‖ ≤ ε / 3 := h3 s hs
  have t1 : ‖((admissibleFreeStage n s - FHadmFree s) + FirstOrderWindow n s)
        + SecondResolventResidual n s‖
      ≤ ‖(admissibleFreeStage n s - FHadmFree s) + FirstOrderWindow n s‖
          + ‖SecondResolventResidual n s‖ := norm_add_le _ _
  have t2 : ‖(admissibleFreeStage n s - FHadmFree s) + FirstOrderWindow n s‖
      ≤ ‖admissibleFreeStage n s - FHadmFree s‖ + ‖FirstOrderWindow n s‖ :=
    norm_add_le _ _
  linarith

/-- **FRONT F CLOSED**: the admissible `DFHLimitData` instance —
`FH = FHadmFree`, exhaustion = the admissible net. -/
noncomputable def admissibleDFHLimitData : DFHLimitData galerkinStagePackage where
  alpha := admissibleGalerkinStageSeq
  FH := FHadmFree
  h_FH_holo := FHadmFree_holo
  h_F_stage_to_FH := admissible_F_stage_to_FHadmFree

/-- The instance runs along the admissible net (endpoint hypothesis shape). -/
theorem admissibleDFHLimitData_alpha :
    admissibleDFHLimitData.alpha = admissibleGalerkinStageSeq := rfl

/-- **REDUCED V10 ENDPOINT**: RH from Front R alone — the F-slot is now
discharged by the banked instance. -/
theorem RH_from_admissible_R
    (R : DMasterResidualData galerkinStagePackage)
    (hRalpha : R.alpha = admissibleGalerkinStageSeq) :
    RiemannHypothesis :=
  RH_from_admissible_galerkin_F_R admissibleDFHLimitData R
    admissibleDFHLimitData_alpha hRalpha

#print axioms admissible_F_stage_to_FHadmFree
#print axioms admissibleDFHLimitData
#print axioms admissibleDFHLimitData_alpha
#print axioms RH_from_admissible_R

end

end RHFormalization
