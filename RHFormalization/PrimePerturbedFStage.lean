import RHFormalization.PrimeWeightedPotential
import RHFormalization.PerturbedResidual

namespace RHFormalization
noncomputable section
open Complex

variable {N : ℕ}

/-- **The prime-perturbed F-stage.** The resolvent trace `∑_k 1/(s + λ_k(H₀+V_prime))`
of the genuine prime-weighted operator `H₀ + V_prime = freeDiag μ + primePotential w`.
This is a real `ℂ → ℂ` object built from the actual prime potential — NOT zero, NOT free.
It is the concrete D-side `F_stage` the manuscript's operator demands. -/
def primePerturbedFStage (μ : Fin N → ℝ) (w : Fin N → ℝ) : ℂ → ℂ :=
  perturbedFStage μ (primePotential_isHermitian w)

/-- It unfolds to the resolvent trace of the perturbed (prime) spectrum. -/
theorem primePerturbedFStage_eq (μ : Fin N → ℝ) (w : Fin N → ℝ) (s : ℂ) :
    primePerturbedFStage μ w s =
      FstageFinite (perturbedEigenvalues μ (primePotential_isHermitian w)) s := by
  rfl

/-- **The prime-perturbed resolvent is holomorphic on Ω**, provided the perturbed
prime spectrum is nonnegative (the globally-shifted regime). Inherited directly from
`perturbedFStage_holo` — the operator-side holomorphy, now for the genuine prime operator. -/
theorem primePerturbedFStage_holo (μ : Fin N → ℝ) (w : Fin N → ℝ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ (primePotential_isHermitian w) i) :
    HolomorphicOnC (primePerturbedFStage μ w) Ω :=
  perturbedFStage_holo μ (primePotential_isHermitian w) hpos

#print axioms primePerturbedFStage
#print axioms primePerturbedFStage_eq
#print axioms primePerturbedFStage_holo
end
end RHFormalization
