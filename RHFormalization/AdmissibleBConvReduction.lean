import RHFormalization.AdmissibleDFHLimitData

/-!
# FRONT R REDUCED TO THE B-SIDE: `RH_from_admissible_B_conv`

Since `R_stage = F_stage − B_stage` (definitional) and the F-side limit is
banked (`admissible_F_stage_to_FHadmFree`), the entire remaining input
`h_conv` collapses to a single B-side statement:

> there exists `Bω` holomorphic on Ω with
> `B_stage(α n) → Bω` uniformly on Ω-compacts along the admissible net.

Given that, `RH := FHadmFree − Bω` yields the full `DMasterResidualData`
by two-epsilon, and RH follows from the banked V10 endpoint.  By Landau,
`Bω` cannot be the raw prime-power tsum off the abs-conv parabola — it must
arise from the manuscript's pole-package/cancellation mechanism.  That
analytic identification is the genuine open frontier; this file makes it
the ONLY remaining input.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

open scoped BigOperators Classical Topology

/-- Two-epsilon: F-side banked limit + hypothesized B-side limit give the
residual limit `R_stage → FHadmFree − Bω` uniformly on Ω-compacts. -/
theorem admissible_R_stage_to_diff
    (Bω : ℂ → ℂ)
    (hBconv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
            (Bω s) < ε) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
            (FHadmFree s - Bω s) < ε := by
  intro K hK hKO ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hF := admissible_F_stage_to_FHadmFree K hK hKO (ε / 2) hε2
  have hB := hBconv K hK hKO (ε / 2) hε2
  filter_upwards [hF, hB] with n h1 h2
  intro s hs
  have hR : galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    first
      | rfl
      | simp [galerkinStagePackage]
      | (show galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            = _
         rfl)
  rw [hR, dist_eq_norm]
  have key : galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - (FHadmFree s - Bω s)
      = (galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - FHadmFree s)
        - (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
            - Bω s) := by
    ring
  rw [key]
  have hA : ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      - FHadmFree s‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact h1 s hs
  have hBn : ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      - Bω s‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact h2 s hs
  calc ‖(galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - FHadmFree s)
        - (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
            - Bω s)‖
      ≤ ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - FHadmFree s‖
        + ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
            - Bω s‖ := norm_sub_le _ _
    _ < ε := by linarith

/-- **The Front R instance from a B-side limit**: `RH := FHadmFree − Bω`. -/
noncomputable def admissibleDMasterResidualData
    (Bω : ℂ → ℂ) (hBω_holo : HolomorphicOnC Bω Ω)
    (hBconv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
            (Bω s) < ε) :
    DMasterResidualData galerkinStagePackage where
  alpha := admissibleGalerkinStageSeq
  RH := fun s => FHadmFree s - Bω s
  h_RH_holo := by
    first
      | exact AnalyticOn.sub FHadmFree_holo hBω_holo
      | exact FHadmFree_holo.sub hBω_holo
      | exact DifferentiableOn.sub FHadmFree_holo hBω_holo
      | (intro s hs
         exact (FHadmFree_holo s hs).sub (hBω_holo s hs))
  h_R_stage_to_RH := admissible_R_stage_to_diff Bω hBconv

/-- **h_conv, FINAL SHAPE — RH from the B-side limit alone.**  Everything
else in the V10 chain is banked; the manuscript's remaining analytic
content is exactly the pair `(Bω, hBconv)`. -/
theorem RH_from_admissible_B_conv
    (Bω : ℂ → ℂ) (hBω_holo : HolomorphicOnC Bω Ω)
    (hBconv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
            (Bω s) < ε) :
    RiemannHypothesis :=
  RH_from_admissible_R
    (admissibleDMasterResidualData Bω hBω_holo hBconv) rfl

#print axioms admissible_R_stage_to_diff
#print axioms admissibleDMasterResidualData
#print axioms RH_from_admissible_B_conv

end

end RHFormalization
