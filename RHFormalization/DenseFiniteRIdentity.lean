import RHFormalization.CompensatorDensityKernelForm
import RHFormalization.DenseCompactGaps
import RHFormalization.DenseFctrBound
import Mathlib

/-!
# DenseFiniteRIdentity — B(i)-6½: the exact finite-R continuum identity

On Ω, with w = √(s+¼):
  ∫₀^{admR n} e^{u/2}·K(u,s) du = compensatorM n s − denseE0 s
(minus sign, GPT-countersigned). Pure algebra on the banked C-REP theorem
`compensatorM_eq_densityKernelIntegral_add_pole` once one notes
`compensatorPole s = denseE0 s`. Stated in both weight forms: the banked
`Complex.exp((u:ℂ)/2)` and the `((Real.exp (u/2):ℝ):ℂ)` form `denseFctr` uses.
No estimates.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- The C-REP pole is the disk-identity main term. -/
theorem compensatorPole_eq_denseE0 (s : ℂ) : compensatorPole s = denseE0 s := by
  unfold compensatorPole denseE0
  rw [one_div_mul_one_div]

/-- **Finite-R identity** (banked weight form). -/
theorem finiteR_kernel_integral_eq (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    (∫ u in (0:ℝ)..(admR n),
        Complex.exp ((u:ℂ)/2) * shiftedLaplaceHeatKernelC u s)
      = compensatorM n s - denseE0 s := by
  rw [compensatorM_eq_densityKernelIntegral_add_pole n hs, compensatorPole_eq_denseE0]
  ring

/-- Weight coercion: `((e^{u/2} : ℝ) : ℂ) = exp((u:ℂ)/2)`. -/
theorem exp_half_ofReal_eq (u : ℝ) :
    ((Real.exp (u/2) : ℝ) : ℂ) = Complex.exp ((u:ℂ)/2) := by
  simp [Complex.ofReal_exp]

/-- **Finite-R identity** (`denseFctr` weight form). -/
theorem finiteR_kernel_integral_eq' (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    (∫ u in (0:ℝ)..(admR n),
        ((Real.exp (u/2) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s)
      = compensatorM n s - denseE0 s := by
  rw [← finiteR_kernel_integral_eq n hs]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [exp_half_ofReal_eq]

#print axioms compensatorPole_eq_denseE0
#print axioms finiteR_kernel_integral_eq
#print axioms exp_half_ofReal_eq
#print axioms finiteR_kernel_integral_eq'

end

end RHFormalization
