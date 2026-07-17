import RHFormalization.DTailDensityFreeBound
import RHFormalization.HeatSumSqrtBound
import RHFormalization.Duhamel2IntegratedBound

/-!
# DTailFreeHeatTraceBound

ROUTE CARD
1. Target: free half of `h_fk`, the D.TAIL density-normalized heat-trace bound.
2. Object: free Galerkin heat trace `∑ i, heatWeight L t i`.
3. Raw B on Ω? NO.
4. R = F − raw B? NO.
5. True outright from the Gaussian heat-sum bound.
6. Manuscript: D.TAIL-DENSITY, free Dirichlet heat kernel domination.
7. Consumer: `h_fk` / `dTail_uniform_bound`.

This proves the free trace density estimate:

  (1 / (2L)) · Tr(e^{-tK_L}) ≤ freeHeatDiagonal(t).

The perturbed domination `Tr(e^{-t(K+V)}) ≤ Tr(e^{-tK})` is the next brick.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real
open scoped BigOperators

variable {N : ℕ}

/-- Rewrite the whole-line heat diagonal in rpow form. -/
theorem freeHeatDiagonal_eq_rpow (t : ℝ) (ht : 0 < t) :
    freeHeatDiagonal t =
      (1 / (2 * Real.sqrt Real.pi)) * t ^ (-(1 : ℝ) / 2) := by
  unfold freeHeatDiagonal
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt_arg :
      Real.sqrt (4 * Real.pi * t) =
        2 * Real.sqrt Real.pi * Real.sqrt t := by
    have hsquare :
        (2 * Real.sqrt Real.pi * Real.sqrt t) ^ 2 =
          4 * Real.pi * t := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hpi.le, Real.sq_sqrt ht.le]
      ring
    rw [← hsquare, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [hsqrt_arg]
  have htneg :
      (Real.sqrt t)⁻¹ = t ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    have hpow :
        (t ^ ((1 : ℝ) / 2))⁻¹ = t ^ (-((1 : ℝ) / 2)) :=
      (Real.rpow_neg ht.le ((1 : ℝ) / 2)).symm
    rw [hpow]
    first
      | (congr 1; ring)
      | (congr 1; norm_num)
      | norm_num
      | ring_nf
  rw [← htneg]
  field_simp

/--
Free Galerkin heat trace, density-normalized.

This is the free part of the `h_fk` premise used by `dTail_uniform_bound`.
-/
theorem freeHeatTrace_density_bound
    (L t : ℝ) (hL : 0 < L) (ht : 0 < t) :
    (1 / (2 * L)) * (∑ i : Fin N, heatWeight L t i)
      ≤ freeHeatDiagonal t := by
  have hsum :=
    sum_heatWeight_le_sqrt (N := N) L hL t ht

  have hfactor :=
    sqrt_heat_factor L t hL ht

  have hcoef :
      (1 / (2 * L)) * (L / (2 * Real.sqrt Real.pi))
        ≤ 1 / (2 * Real.sqrt Real.pi) := by
    have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    calc
      (1 / (2 * L)) * (L / (2 * Real.sqrt Real.pi))
          = 1 / (4 * Real.sqrt Real.pi) := by
            field_simp [ne_of_gt hL, ne_of_gt hsqrtpi]
            ring
      _ ≤ 1 / (2 * Real.sqrt Real.pi) := by
            field_simp [ne_of_gt hsqrtpi]
            nlinarith [hsqrtpi]

  have hrpow_nonneg : 0 ≤ t ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg ht.le _

  calc
    (1 / (2 * L)) * (∑ i : Fin N, heatWeight L t i)
        ≤ (1 / (2 * L)) *
            (Real.sqrt (Real.pi / (t * (Real.pi / L) ^ 2)) / 2) := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (2 * L)) *
          ((L / (2 * Real.sqrt Real.pi)) * t ^ (-(1 : ℝ) / 2)) := by
          rw [hfactor]
    _ = ((1 / (2 * L)) * (L / (2 * Real.sqrt Real.pi)))
          * t ^ (-(1 : ℝ) / 2) := by ring
    _ ≤ (1 / (2 * Real.sqrt Real.pi)) * t ^ (-(1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_right hcoef hrpow_nonneg
    _ = freeHeatDiagonal t := by
          rw [freeHeatDiagonal_eq_rpow t ht]

/--
The same free heat-trace estimate in the exact `h_fk` shape, with a generic
eigenvalue function equal to the free Galerkin heat weights.
-/
theorem h_fk_free_galerkin
    (L t : ℝ) (hL : 0 < L) (ht : 0 < t) :
    (1 / (2 * L)) * (∑ i : Fin N, Real.exp (-t * galerkinLam L i))
      ≤ freeHeatDiagonal t := by
  simpa [heatWeight] using
    freeHeatTrace_density_bound (N := N) L t hL ht

#print axioms freeHeatDiagonal_eq_rpow
#print axioms freeHeatTrace_density_bound
#print axioms h_fk_free_galerkin

end

end RHFormalization
