-- SENTINEL: spike-transfer-c1-profile-v1
import RHFormalization.SpikeTransferRateM1Integral
import RHFormalization.GalerkinDuhamel1Term
import Mathlib

/-! # Core brick 3 — the c₁ profile (D.BFF.5 expansion structure).
On the diagonal the two heat weights merge: the order-1 Duhamel integrand
is u-independent and its time integral is exactly `t · Σ_m V_mm e^{−tλ_m}`
— the finite-stage form of the manuscript's `t·c₁(a)` term. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- Trace of `diag(d₁)·V·diag(d₂)` as a single sum. -/
theorem trace_diag_V_diag (V : Matrix (Fin N) (Fin N) ℝ) (d₁ d₂ : Fin N → ℝ) :
    (Matrix.diagonal d₁ * V * Matrix.diagonal d₂).trace
      = ∑ m, d₁ m * V m m * d₂ m := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro m _
  rw [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **u-independence**: the order-1 integrand collapses. -/
theorem duhamel1Integrand_u_independent
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u
      = ∑ m : Fin N, galerkinV (N := N) δ qs w L m m
          * Real.exp (-(t * galerkinLam L (m : ℕ))) := by
  unfold duhamel1Integrand
  rw [trace_diag_V_diag]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  unfold heatWeight
  have hmerge : Real.exp (-((t - u) * galerkinLam L (m : ℕ)))
        * Real.exp (-(u * galerkinLam L (m : ℕ)))
      = Real.exp (-(t * galerkinLam L (m : ℕ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-((t - u) * galerkinLam L (m : ℕ)))
        * galerkinV (N := N) δ qs w L m m
        * Real.exp (-(u * galerkinLam L (m : ℕ)))
      = galerkinV (N := N) δ qs w L m m
          * (Real.exp (-((t - u) * galerkinLam L (m : ℕ)))
            * Real.exp (-(u * galerkinLam L (m : ℕ)))) := by ring
    _ = galerkinV (N := N) δ qs w L m m
          * Real.exp (-(t * galerkinLam L (m : ℕ))) := by rw [hmerge]

/-- **CORE BRICK 3 (the c₁ term).** The order-1 Duhamel time integral is
exactly `t · Σ_m V_mm e^{−tλ_m}`. -/
theorem duhamel1Integral_eq_t_mul_heat_trace
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u)
      = t * ∑ m : Fin N, galerkinV (N := N) δ qs w L m m
          * Real.exp (-(t * galerkinLam L (m : ℕ))) := by
  have hcongr : (∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u)
      = ∫ _u in (0:ℝ)..t,
          (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
            * Real.exp (-(t * galerkinLam L (m : ℕ)))) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact duhamel1Integrand_u_independent δ qs w L t u
  rw [hcongr, intervalIntegral.integral_const]
  rw [sub_zero, smul_eq_mul]

#print axioms trace_diag_V_diag
#print axioms duhamel1Integrand_u_independent
#print axioms duhamel1Integral_eq_t_mul_heat_trace

end

end RHFormalization
