-- SENTINEL: L1-v4
import RHFormalization.CompletedZetaGrowth
import Mathlib

/-!
# Laplace integrals of the stage defect rate pieces (defect-gate L1)

From the banked `integral_rpow_mul_exp_eq_gamma`:

  ∫₀^∞ e^{−δt} dt           = 1/δ
  ∫₀^∞ t^{−1/2} e^{−δt} dt  = √π · δ^{−1/2}
  ∫₀^∞ t^{−1/2} e^{−δt} e^{−tM²/2} dt ≤ √(2π)/M

The third is the binding gate rate: at M = N_nπ/L_n ≥ (n+2)π it delivers
O(1/(n+2)), beating the √(n+2) stage mass.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- `∫₀^∞ e^{−δt} dt = 1/δ`. -/
theorem laplace_one_eq (δ : ℝ) (hδ : 0 < δ) :
    ∫ t in Set.Ioi (0:ℝ), Real.exp (-δ * t) = 1 / δ := by
  have h := integral_rpow_mul_exp_eq_gamma (a := 1) (b := δ) one_pos hδ
  have hcongr : (∫ t in Set.Ioi (0:ℝ), t ^ ((1:ℝ) - 1) * Real.exp (-δ * t))
      = ∫ t in Set.Ioi (0:ℝ), Real.exp (-δ * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    norm_num
  rw [hcongr] at h
  rw [h, Real.Gamma_one, mul_one, Real.rpow_neg_one, one_div]

/-- `∫₀^∞ t^{−1/2} e^{−δt} dt = √π · δ^{−1/2}`. -/
theorem laplace_inv_sqrt_eq (δ : ℝ) (hδ : 0 < δ) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (-(1/2) : ℝ) * Real.exp (-δ * t)
      = Real.sqrt Real.pi * δ ^ (-(1/2) : ℝ) := by
  have h := integral_rpow_mul_exp_eq_gamma (a := (1/2 : ℝ)) (b := δ)
    (by norm_num) hδ
  have he : ((1:ℝ)/2 - 1) = (-(1/2) : ℝ) := by norm_num
  rw [he] at h
  rw [h, Real.Gamma_one_half_eq, mul_comm]

/-- Auxiliary: `√(M²/2) = M/√2` for `0 < M`. -/
theorem sqrt_half_sq_eq (M : ℝ) (hM : 0 < M) :
    Real.sqrt (M ^ 2 / 2) = M / Real.sqrt 2 := by
  rw [show M ^ 2 / 2 = M ^ 2 * (2:ℝ)⁻¹ by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le,
    Real.sqrt_inv]
  rw [division_def]

/-- Auxiliary: `(M²/2)^{−1/2} = √2/M` for `0 < M`. -/
theorem rpow_neg_half_half_sq (M : ℝ) (hM : 0 < M) :
    (M ^ 2 / 2 : ℝ) ^ (-(1/2) : ℝ) = Real.sqrt 2 / M := by
  have hbase : (0:ℝ) < M ^ 2 / 2 := by positivity
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.rpow_neg hbase.le, ← Real.sqrt_eq_rpow, sqrt_half_sq_eq M hM]
  rw [inv_div]

/-- **The binding gate integral**: `∫₀^∞ t^{−1/2}·e^{−δt}·e^{−tM²/2} dt
≤ √(2π)/M`. -/
theorem laplace_inv_sqrt_gauss_le (δ M : ℝ) (hδ : 0 < δ) (hM : 0 < M) :
    ∫ t in Set.Ioi (0:ℝ),
        t ^ (-(1/2) : ℝ) * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2 / 2)))
      ≤ Real.sqrt (2 * Real.pi) / M := by
  have hδ' : (0:ℝ) < δ + M ^ 2 / 2 := by positivity
  have hcombine : (∫ t in Set.Ioi (0:ℝ),
      t ^ (-(1/2) : ℝ) * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2 / 2))))
      = ∫ t in Set.Ioi (0:ℝ),
        t ^ (-(1/2) : ℝ) * Real.exp (-(δ + M ^ 2 / 2) * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hcombine, laplace_inv_sqrt_eq _ hδ']
  have hmono : (δ + M ^ 2 / 2 : ℝ) ^ (-(1/2) : ℝ)
      ≤ (M ^ 2 / 2 : ℝ) ^ (-(1/2) : ℝ) := by
    have hbase : (0:ℝ) < M ^ 2 / 2 := by positivity
    have hle : (M ^ 2 / 2 : ℝ) ≤ δ + M ^ 2 / 2 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hbase hle (by norm_num)
  calc Real.sqrt Real.pi * (δ + M ^ 2 / 2 : ℝ) ^ (-(1/2) : ℝ)
      ≤ Real.sqrt Real.pi * (M ^ 2 / 2 : ℝ) ^ (-(1/2) : ℝ) :=
        mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)
    _ = Real.sqrt Real.pi * (Real.sqrt 2 / M) := by
        rw [rpow_neg_half_half_sq M hM]
    _ = Real.sqrt (2 * Real.pi) / M := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        ring

#print axioms laplace_one_eq
#print axioms laplace_inv_sqrt_eq
#print axioms sqrt_half_sq_eq
#print axioms rpow_neg_half_half_sq
#print axioms laplace_inv_sqrt_gauss_le

end

end RHFormalization
