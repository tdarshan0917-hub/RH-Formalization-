import RHFormalization.AdmissibleRouteHFWired

/-!
# AdmissibleRStageOverlapLimit — the uniqueness anchor for h_conv

ROUTE CARD
1. Target: `R_stage(adm n) → FHadmFree − Bcan` pointwise on RHP(1) — the
   overlap identification every Montel subsequential limit must match.
2. Proof: R = F − B (rfl) + banked admissible_hF_pointwise + admissible_hB
   + Tendsto.sub. No new analysis.
3. Consumer: the h_conv Montel-uniqueness step (next brick).
4. Raw B on Ω? NO. hComb/CompensatedB/B-locbdd targeted? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- The R-stage limit candidate on the overlap. -/
def admissibleRHcand (s : ℂ) : ℂ :=
  FHadmFree s - galerkinBcanLimitData.Bcan s

/-- **Overlap limit**: the admissible R-stages converge pointwise on
RHP(1) to `FHadmFree − Bcan`. -/
theorem admissible_R_stage_overlap_limit
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ => galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
      Filter.atTop (nhds (admissibleRHcand s)) := by
  have hR : (fun n : ℕ =>
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
      = fun n : ℕ =>
        galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    funext n
    rfl
  rw [hR]
  exact (admissible_hF_pointwise s hs).sub (admissible_hB s hs)

#print axioms admissible_R_stage_overlap_limit

end

end RHFormalization
