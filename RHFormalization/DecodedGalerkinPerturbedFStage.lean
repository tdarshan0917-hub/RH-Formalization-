-- SENTINEL: decoded-perturbed-fstage-v2
import RHFormalization.DecodedGalerkinFStageForwardGate
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

variable {N : ℕ}

/-- Perturbed resolvent F-stage using the manuscript-faithful decoded matrix. -/
noncomputable def decodedGalerkinPerturbedFStage
    (μ : Fin N → ℝ)
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ)
    (s : ℂ) : ℂ :=
  perturbedFStage μ
    (decodedGalerkinVC_isHermitian (N := N) δ qs w L) s

/-- Holomorphy of the decoded perturbed F-stage on Ω. -/
theorem decodedGalerkinPerturbedFStage_holo
    (μ : Fin N → ℝ)
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ)
    (hspec :
      ∀ i : Fin N,
        0 ≤ perturbedEigenvalues μ
          (decodedGalerkinVC_isHermitian
            (N := N) δ qs w L) i) :
    HolomorphicOnC
      (decodedGalerkinPerturbedFStage
        (N := N) μ δ qs w L) Ω := by
  exact perturbedFStage_holo μ
    (decodedGalerkinVC_isHermitian
      (N := N) δ qs w L) hspec

#print axioms decodedGalerkinPerturbedFStage
#print axioms decodedGalerkinPerturbedFStage_holo

end

end RHFormalization
