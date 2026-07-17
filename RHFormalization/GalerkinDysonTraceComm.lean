import RHFormalization.GalerkinDysonTraceStep
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFormalization
noncomputable section
open Matrix MeasureTheory intervalIntegral
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- Trace commutes with the interval integral: `Tr(∫ F) = ∫ Tr(F)`, since trace
is a continuous linear map on the finite matrix algebra and the Bochner interval
integral commutes with continuous linear maps. -/
theorem trace_duhamel_integral_comm
    (t : ℝ)
    (F : ℝ → Matrix (Fin N) (Fin N) ℂ) (hcontF : Continuous F) :
    (∫ u in (0:ℝ)..t, F u).trace = ∫ u in (0:ℝ)..t, (F u).trace := by
  -- trace as a continuous linear map, via the LinearMap in finite dimensions
  let T : Matrix (Fin N) (Fin N) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin N) ℂ ℂ)
  have hTapp : ∀ M : Matrix (Fin N) (Fin N) ℂ, T M = M.trace := fun M => rfl
  have hFI : IntervalIntegrable F MeasureTheory.volume 0 t :=
    hcontF.intervalIntegrable 0 t
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm T hFI
  simp only [hTapp] at hcomm
  exact hcomm.symm

#print axioms trace_duhamel_integral_comm
end
end RHFormalization
