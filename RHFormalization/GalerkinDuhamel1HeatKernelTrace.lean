import RHFormalization.GalerkinDuhamel1FiniteSpikeKernel
import RHFormalization.PrimePotentialBumpSplit
import RHFormalization.DirichletEigenfunL2
import Mathlib

/-!
# Galerkin order-1 heat-kernel trace form

Exact finite-N/L identity:
  finiteGalerkinSpikeKernel
  =
  ∫ finiteGalerkinHeatDiagonal(t,x) * gaussBump(x-log q) dx.

The later comparison with `heatKernelG` is a bound/limit, not finite equality.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- Finite Galerkin heat-kernel diagonal. -/
noncomputable def finiteGalerkinHeatDiagonal
    (L : ℝ) (t : ℝ) (x : ℝ) : ℝ :=
  ∑ m : Fin N,
    heatWeight (N := N) L t m
      * dirichletEigenfun (m + 1) L x
      * dirichletEigenfun (m + 1) L x

/--
Finite Galerkin spike kernel as a heat-diagonal/bump integral.
-/
theorem finiteGalerkinSpikeKernel_eq_heatDiagonal_integral
    (δ : ℝ) (q : ℕ) (L : ℝ) (t : ℝ) :
    finiteGalerkinSpikeKernel (N := N) δ q L t =
      ∫ x in (0:ℝ)..L,
        finiteGalerkinHeatDiagonal (N := N) L t x
          * gaussBump δ (x - Real.log q) := by
  unfold finiteGalerkinSpikeKernel finiteGalerkinHeatDiagonal bumpMatrixElement
  symm
  calc
    ∫ x in (0:ℝ)..L,
        (∑ m : Fin N,
          heatWeight (N := N) L t m
            * dirichletEigenfun (m + 1) L x
            * dirichletEigenfun (m + 1) L x)
          * gaussBump δ (x - Real.log q)
        =
      ∫ x in (0:ℝ)..L,
        ∑ m : Fin N,
          heatWeight (N := N) L t m
            * dirichletEigenfun (m + 1) L x
            * dirichletEigenfun (m + 1) L x
            * gaussBump δ (x - Real.log q) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp
        rw [Finset.sum_mul]
    _ =
      ∑ m : Fin N,
        ∫ x in (0:ℝ)..L,
          heatWeight (N := N) L t m
            * dirichletEigenfun (m + 1) L x
            * dirichletEigenfun (m + 1) L x
            * gaussBump δ (x - Real.log q) := by
        rw [intervalIntegral.integral_finsetSum]
        intro m hm
        have hφ : Continuous (fun x : ℝ => dirichletEigenfun (m + 1) L x) :=
          continuous_dirichletEigenfun (m + 1) L
        have hg : Continuous (fun x : ℝ => gaussBump δ (x - Real.log q)) := by
          unfold gaussBump
          fun_prop
        exact (((continuous_const.mul hφ).mul hφ).mul hg).intervalIntegrable 0 L
    _ =
      ∑ m : Fin N,
        heatWeight (N := N) L t m *
          ∫ x in (0:ℝ)..L,
            dirichletEigenfun (m + 1) L x
              * gaussBump δ (x - Real.log q)
              * dirichletEigenfun (m + 1) L x := by
        apply Finset.sum_congr rfl
        intro m hm
        calc
          ∫ x in (0:ℝ)..L,
            heatWeight (N := N) L t m
              * dirichletEigenfun (m + 1) L x
              * dirichletEigenfun (m + 1) L x
              * gaussBump δ (x - Real.log q)
            =
          ∫ x in (0:ℝ)..L,
            heatWeight (N := N) L t m *
              (dirichletEigenfun (m + 1) L x
                * gaussBump δ (x - Real.log q)
                * dirichletEigenfun (m + 1) L x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
          _ =
            heatWeight (N := N) L t m *
              ∫ x in (0:ℝ)..L,
                dirichletEigenfun (m + 1) L x
                  * gaussBump δ (x - Real.log q)
                  * dirichletEigenfun (m + 1) L x := by
              rw [intervalIntegral.integral_const_mul]

#print axioms finiteGalerkinHeatDiagonal
#print axioms finiteGalerkinSpikeKernel_eq_heatDiagonal_integral

end
end RHFormalization
