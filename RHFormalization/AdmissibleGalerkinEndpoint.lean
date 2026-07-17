import RHFormalization.SlowCutoffBConvergence
import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.GalerkinOverlapAndV9

/-!
# RHFormalization.AdmissibleGalerkinEndpoint
**THE ADMISSIBLE CAPSTONE (V10).** RH from F- and R-data along the
manuscript-faithful admissible net. Sibling of RH_from_galerkin_F_R with
alpha = admissibleGalerkinStageSeq; same package, same proof pattern.
hB transfers because the B-slot at the admissible sequence is the SAME
slow-cutoff concrete B-sequence at admR n = log(n+2)/2 (Phase 2b).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- hB along the admissible net: the B-sequence runs at the SLOW cutoff
`admR n = log(n+2)/2`, so convergence comes from the generic slow-cutoff
engine (Phase 2a) — any cutoff tending to infinity eventually covers every
fixed prime power. -/
theorem admissible_hB (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
      atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
  have hconv :=
    shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1_along
      admR tendsto_admR_atTop s hs
  have hmodel : (shiftedLaplaceModelPackageAt 1).Bshared s
      = galerkinBcanLimitData.Bcan s := by
    show shiftedLaplaceLogDerivModel s
      = (shiftedLaplacePrimePackageAt 1).Bshared s
    exact (shiftedLaplacePrime_h_model s hs).symm
  rw [← hmodel]
  refine hconv.congr (fun n => ?_)
  show finiteCanonicalPrimePowerPackage
      (concretePrimePowerBelowCutoff (admR n))
      shiftedLaplaceHeatKernelC s
    = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
  show finiteCanonicalPrimePowerPackage
      (concretePrimePowerBelowCutoff (admR n))
      shiftedLaplaceHeatKernelC s
    = finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow ((admissibleGalerkinStageSeq n).R))
        shiftedLaplaceHeatKernelC s
  rw [admissibleGalerkinStageSeq_R, activePairs_eq_concrete]

/-- **V10 endpoint.** RH from the two convergence structures along the
admissible (manuscript-faithful) exhaustion. -/
theorem RH_from_admissible_galerkin_F_R
    (F : DFHLimitData galerkinStagePackage)
    (R : DMasterResidualData galerkinStagePackage)
    (hFalpha : F.alpha = admissibleGalerkinStageSeq)
    (hRalpha : R.alpha = admissibleGalerkinStageSeq) :
    RiemannHypothesis := by
  have hsigma0 : galerkinStagePackage.sigma0 = 1 := rfl
  have hRHP : RightHalfPlane galerkinStagePackage.sigma0 ⊆ Ω := by
    exact rightHalfPlane_subset_Omega galerkinStagePackage.sigma0
      (by rw [hsigma0]; norm_num)
  have hoverlap : DOverlapIdentityAPI galerkinStagePackage
      galerkinBcanLimitData F R := by
    refine DOverlapIdentityAPI_from_pointwise_stage_limits
      galerkinStageSplitAPI ?_ ?_ ?_
    · intro s hs
      exact F.pointwise_F_stage_tendsto_of_RHP_subset_Omega hRHP s hs
    · intro s hs
      have hs1 : s ∈ RightHalfPlane (1 : ℝ) := by
        rw [← hsigma0]; exact hs
      have := admissible_hB s hs1
      rw [← hFalpha] at this
      exact this
    · intro s hs
      have := R.pointwise_R_stage_tendsto_of_RHP_subset_Omega hRHP s hs
      rw [hRalpha, ← hFalpha] at this
      exact this
  exact RH_from_DExportLayer
    { P := galerkinStagePackage
      B := galerkinBcanLimitData
      F := F
      R := R
      canRem := buildDCanRemAPIFromMasterResidual _ _ _ _
      overlap := hoverlap }
    (by rw [hsigma0])
    galerkinBcanLimitData_Cshared

#print axioms admissible_hB
#print axioms RH_from_admissible_galerkin_F_R

end

end RHFormalization
