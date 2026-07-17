import RHFormalization.BSideHeatKernelLaplace
import RHFormalization.GlasserIntegral
import RHFormalization.HeatKernelLaplaceBase
import RHFormalization.BSideHeatKernelLaplaceRealAxisZero
import RHFormalization.BSideHeatKernelLaplacePos
import Mathlib

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

/--
M1 target: real-axis version of the B-side keystone.
This compiles with `sorry` but prints the exact two branch goals after unfolding.
-/
theorem shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_M1
    (a σ : ℝ) (ha : 0 ≤ a) (hσ : 0 < σ) :
    shiftedLaplaceHeatKernelC a (σ : ℂ)
      =
    ∫ t in Set.Ioi (0 : ℝ),
      shiftedHeatIntegrand a (σ : ℂ) t := by
  have hb : 0 < σ + (1/4 : ℝ) := by positivity
  rcases lt_or_eq_of_le ha with ha_pos | ha_zero
  ·
    exact shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_pos a σ ha_pos hσ
  ·
    subst a
    exact shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_zero σ hσ

#print axioms shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_ofReal_M1

end RHFormalization
