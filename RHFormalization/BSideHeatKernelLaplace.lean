import RHFormalization.DA2HeatTrace
import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.CanonicalPrimePowerHeatKernelWeightedSummabilityTarget
import Mathlib

/-!
# B-side connector (D.A2 twin): the Gaussian heat-kernel Laplace transform.

The ONE remaining classical analytic input. F-side twin is GREEN
(FstageFinite_eq_laplace_heatTrace). This is its B-side mirror:
the closed-form shifted Laplace kernel equals the Laplace transform of the
shifted 1D Gaussian heat kernel.

  shiftedLaplaceHeatKernelC a s = ∫₀^∞ e^{-st}·exp(-t/4)·heatKernelG t a dt

This is a known classical identity (Laplace transform of the 1D heat kernel /
inverse-Gaussian / first-passage density). Mathlib lacks it directly; carried
here as a single named analytic lemma so the entire D.USR chain closes around it.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/-- The shifted Gaussian heat integrand whose Laplace transform is the closed-form
B-kernel: `e^{-st}·exp(-t/4)·heatKernelG t a`. -/
noncomputable def shiftedHeatIntegrand (a : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-s * (t:ℂ)) * Complex.exp (-(t:ℂ)/4) * heatKernelG t a

/-!
The former `shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG` (carried here as a
`sorry`ed classical input) is now PROVED, unconditionally, as
`shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane` in
`RHFormalization/BSideHeatKernelLaplaceConnector.lean`.
This file now only supplies `shiftedHeatIntegrand`.
-/

end RHFormalization
