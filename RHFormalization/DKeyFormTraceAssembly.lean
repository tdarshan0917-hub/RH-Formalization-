import RHFormalization.GalerkinDysonTraceStep
import RHFormalization.GalerkinFreeHeatDiagonal
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

/-- Trace commutes with the interval integral, over ℝ matrices. -/
theorem trace_integral_comm_real
    (t : ℝ) (F : ℝ → Matrix (Fin N) (Fin N) ℝ) (hcontF : Continuous F) :
    (∫ u in (0:ℝ)..t, F u).trace = ∫ u in (0:ℝ)..t, (F u).trace := by
  let T : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin N) ℝ ℝ)
  have hTapp : ∀ M : Matrix (Fin N) (Fin N) ℝ, T M = M.trace := fun M => rfl
  have hFI : IntervalIntegrable F MeasureTheory.volume 0 t :=
    hcontF.intervalIntegrable 0 t
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm T hFI
  simp only [hTapp] at hcomm
  exact hcomm.symm

/-- **D.KEY-FORM-TRACE bridge identity (ℝ).** The real trace difference equals the
interval integral of the scalar order-1 Duhamel integrand, free-heat factor
diagonalized, right factor the exact full perturbed semigroup. EXACT IDENTITY
(infrastructure), NOT the uniform trace estimate — its consumer is a norm bound
on the right-hand integrand. -/
theorem galerkinDuhamel_trace_eq_diagonal
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
      - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
      = ∫ u in (0:ℝ)..t,
          (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (u • (-(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L)))).trace := by
  rw [galerkinDuhamel_trace_eq (N := N) δ qs w L t]
  rw [trace_integral_comm_real (N := N) t
      (fun u => NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-(galerkinV (N := N) δ qs w L))
        * NormedSpace.exp (u • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L))))
      (by fun_prop)]
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [galerkinFreeHeat_eq_diagonal (N := N) L (t - u)]

#print axioms galerkinDuhamel_trace_eq_diagonal
end
end RHFormalization
