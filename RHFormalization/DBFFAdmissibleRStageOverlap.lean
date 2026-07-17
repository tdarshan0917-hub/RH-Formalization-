import RHFormalization.DBFFProfileCatalog
import RHFormalization.AdmissibleDFHLimitData
import RHFormalization.AdmissibleGalerkinEndpoint

/-!
# DBFFAdmissibleRStageOverlap

ROUTE CARD

This file proves the admissible overlap convergence needed by the DBFF profile
catalog when the bulk residual is the actual admissible `R_stage`.

It does NOT manufacture profiles.
It does NOT use raw B on Ω.
It does NOT instantiate the DBFF catalog.

It only proves the honest algebraic/limit bridge:

  R_stage_n = F_stage_n - B_stage_n
  F_stage_n → FHadmFree
  B_stage_n → Bshared on RightHalfPlane 1

therefore

  R_stage_n → FHadmFree - Bshared on RightHalfPlane 1.

The B-side is supplied by `admissible_hB`; if the local target prints as
`galerkinBcanLimitData.Bcan`, the proof tries to discharge the definitional/simp
identification with `(shiftedLaplacePrimePackageAt 1).Bshared`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- Pointwise F-stage convergence on the overlap, extracted from the compact
eps-N admissible F convergence theorem by applying it to the singleton `{s}`. -/
theorem admissible_F_stage_tendsto_FHadmFree_pointwise
    (s : ℂ) (hsΩ : s ∈ Ω) :
    Tendsto
      (fun n : ℕ => galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
      atTop
      (𝓝 (FHadmFree s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h :=
    admissible_F_stage_to_FHadmFree
      ({s} : Set ℂ)
      isCompact_singleton
      (Set.singleton_subset_iff.mpr hsΩ)
      ε
      hε
  filter_upwards [h] with n hn
  exact hn s rfl

/-- The admissible `R_stage` overlap convergence required by the DBFF route. -/
theorem admissible_R_stage_to_DBFF_overlap
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
      atTop
      (𝓝 (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s)) := by
  have hsΩ : s ∈ Ω := by
    first
      | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num) hs
      | exact rightHalfPlane_subset_Omega 1 one_pos hs
      | exact rightHalfPlane_subset_Omega _ (by norm_num) hs

  have hF :
      Tendsto
        (fun n : ℕ =>
          galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s)
        atTop
        (𝓝 (FHadmFree s)) :=
    admissible_F_stage_tendsto_FHadmFree_pointwise s hsΩ

  have hB0 := admissible_hB s hs

  have hB :
      Tendsto
        (fun n : ℕ =>
          galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
        atTop
        (𝓝 ((shiftedLaplacePrimePackageAt 1).Bshared s)) := by
    first
      | simpa using hB0
      | simpa [galerkinBcanLimitData] using hB0

  have hsub :
      Tendsto
        (fun n : ℕ =>
          galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
            - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
        atTop
        (𝓝 (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s)) :=
    hF.sub hB

  refine hsub.congr' ?_
  filter_upwards with n
  rfl

#print axioms admissible_F_stage_tendsto_FHadmFree_pointwise
#print axioms admissible_R_stage_to_DBFF_overlap

end

end RHFormalization
