import RHFormalization.PerturbedResidual
import RHFormalization.DA2HeatTrace
import RHFormalization.PrimeHeatTrace
import RHFormalization.PrimeDuhamel2Integrand
import Mathlib

/-!
# Step 1 (free-split, part A): perturbed F-stage as Laplace of the operator heat trace.

`perturbedFStage μ hV s = ∫₀^∞ e^{-st} · Tr(e^{-tH}) dt` where the eigenvalue heat
trace `∑_i e^{-(s+λ_i)t}` is the trace of `diagonal(e^{-tλ})`. This is the bridge
that lets the Duhamel expansion of `e^{-tH}` (orders ≥ 1) attach to the F-stage.

This file proves the eigenvalue-trace = matrix-trace identity, so the perturbed
heat trace `∑_i e^{-(s+λ_i)t}` equals `e^{-st}·Tr(diagonal(e^{-tλ}))` — the form
the Duhamel correction is written in.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Complex MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The eigenvalue heat trace `∑_i e^{-(s+λ_i)t}` equals `e^{-st}` times the trace
of the diagonal heat-weight matrix `diagonal(e^{-tλ})`. This is the algebraic bridge
connecting `FstageFinite`'s integrand to the matrix-trace form the Duhamel expansion uses. -/
theorem perturbedHeatTrace_eq_smul_diagTrace
    (lam : Fin N → ℝ) (s : ℂ) (t : ℝ) :
    (∑ i, Complex.exp (-(s + (lam i : ℂ)) * (t : ℂ)))
      = Complex.exp (-s * (t : ℂ)) *
          (Matrix.diagonal (fun i => Complex.exp (-(t : ℂ) * (lam i : ℂ)))).trace := by
  rw [Matrix.trace_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **Step 1A.** `perturbedFStage μ hV s = ∫₀^∞ e^{-st}·Tr(diagonal(e^{-tλ})) dt`,
the Laplace transform of the operator heat trace (in diagonal form). This is the
form into which the Duhamel expansion `e^{-tH} = e^{-tD} + (orders ≥1)` plugs. -/
theorem perturbedFStage_eq_laplace_diagHeatTrace
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hs : 0 < s.re) (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ hV i) :
    perturbedFStage μ hV s
      = ∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-s * (t : ℂ)) *
            (Matrix.diagonal
              (fun i => Complex.exp (-(t : ℂ) *
                ((perturbedEigenvalues μ hV i : ℝ) : ℂ)))).trace := by
  unfold perturbedFStage
  rw [FstageFinite_eq_laplace_heatTrace (perturbedEigenvalues μ hV) hpos s hs]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  exact perturbedHeatTrace_eq_smul_diagTrace (perturbedEigenvalues μ hV) s t

#print axioms perturbedHeatTrace_eq_smul_diagTrace
#print axioms perturbedFStage_eq_laplace_diagHeatTrace

end
end RHFormalization
