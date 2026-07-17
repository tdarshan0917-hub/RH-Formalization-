import RHFormalization.PrimePerturbedOperatorLayer
import RHFormalization.PrimePerturbedPayload
import RHFormalization.PrimePerturbedFStage
import RHFormalization.ResolventStageHolo
import Mathlib

/-!
# Prime-perturbed R-stage holomorphy (SHIFTED-LAPLACE B, the right one)

R_stage = primePerturbedFStage - finiteCanonicalPrimePowerPackage(...shiftedLaplaceHeatKernelC).
F holo via primePerturbedFStage_holo (given nonneg spectrum);
B holo via the banked shifted-Laplace finite-canonical holo.
NOT the dead displacementCanonicalKernel B. This is h_stage_holo input 1 for the RIGHT layer.
-/

namespace RHFormalization
open Complex Set

theorem primePerturbed_R_stage_holo
    (μ : Fin N → ℝ) (α : DFiniteStage)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ
              (primePotential_isHermitian
                (primeStageWeights (primePerturbedStageIndex α))) i) :
    HolomorphicOnC
      (fun s => (primePerturbedPayload μ).R_stage α s) Ω := by
  have hF : HolomorphicOnC
      (fun s => primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s) Ω :=
    primePerturbedFStage_holo μ (primeStageWeights (primePerturbedStageIndex α)) hpos
  have hB : HolomorphicOnC
      (fun s => finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s) Ω := by
    apply holomorphicOnC_of_forall_holomorphicAtC
    intro s hs
    exact finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
      (resolventIndices α) s hs
  have hR : (fun s => (primePerturbedPayload μ).R_stage α s)
      = (fun s => primePerturbedFStage μ (primeStageWeights (primePerturbedStageIndex α)) s)
        - (fun s => finiteCanonicalPrimePowerPackage (resolventIndices α) shiftedLaplaceHeatKernelC s) := by
    funext s; rfl
  rw [hR]
  exact hF.sub hB

#print axioms primePerturbed_R_stage_holo

end RHFormalization
