import RHFormalization.GalerkinEigenvalueFloor
import RHFormalization.ShiftedLaplaceOmegaGeometry
import RHFormalization.ResolventStageHolo

/-!
# RHFormalization.GalerkinRStageHolo
h_stage_holo for Front R: per-stage Omega-holomorphy of the genuine-operator
package residual R_stage = F_stage − B_stage along galerkinStageSeq.
F-side: banked galerkinStagePackage_F_stage_holo (shifted resolvent trace).
B-side: banked shifted-Laplace finite-canonical holomorphy (kernel-correct;
the designer-kernel trap was F-side wiring only, B was never rewired).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set

/-- B-side per-stage holomorphy: the finite shifted-Laplace canonical package
at every galerkin stage is holomorphic on Ω. -/
theorem galerkinStagePackage_B_stage_holo (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.B_stage (galerkinStageSeq n) s) Ω := by
  first
    | (apply holomorphicOnC_of_forall_holomorphicAtC
       intro s hs
       exact finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
         (activePrimePowerPairsCenterBelow ((galerkinStageSeq n).R)) s hs)
    | (intro s hs
       exact (finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
         (activePrimePowerPairsCenterBelow ((galerkinStageSeq n).R)) s hs).analyticWithinAt)
    | (intro s hs
       exact finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
         (activePrimePowerPairsCenterBelow ((galerkinStageSeq n).R)) s hs)

/-- **h_stage_holo for buildDMasterResidualDataAlong**: per-stage
Omega-holomorphy of the package residual along the genuine exhaustion. -/
theorem galerkinStagePackage_R_stage_holo (n : ℕ) :
    HolomorphicOnC
      (fun s => galerkinStagePackage.R_stage (galerkinStageSeq n) s) Ω := by
  have hF := galerkinStagePackage_F_stage_holo n
  have hB := galerkinStagePackage_B_stage_holo n
  have hR : (fun s => galerkinStagePackage.R_stage (galerkinStageSeq n) s)
      = (fun s => galerkinStagePackage.F_stage (galerkinStageSeq n) s)
        - (fun s => galerkinStagePackage.B_stage (galerkinStageSeq n) s) := by
    funext s; rfl
  rw [hR]
  exact hF.sub hB

#print axioms galerkinStagePackage_B_stage_holo
#print axioms galerkinStagePackage_R_stage_holo

end

end RHFormalization
