import RHFormalization.LaplaceTSquaredKit
import RHFormalization.DA2HeatTrace
import Mathlib

/-!
# LaplaceHeatSumKit — termwise Laplace transforms of finite heat sums

ROUTE CARD
1. Target: generic-spectrum transform identities feeding the s-side M=2
   split: (i) `∫ e^{−st}·(Σ e^{−tλ}:ℂ) = FstageFinite λ s`;
   (ii) `∫ e^{−st}·t·(Σ c_m e^{−tλ}:ℂ) = Σ (c_m:ℂ)·(s+λ_m)⁻²`; plus the
   integrability companions. Generic in `lam : Fin N → ℝ`, `0 ≤ lam`.
2. Raw B on Ω? NO. B−M bare Prop? NO — Mathlib integral algebra over the
   banked DA2 + t² kits.
3. Consumer: PerturbedFStageM2Split (free term → (i) at galerkinFreeMu;
   c₁ term → (ii) at c = V_mm; perturbed total → (i) at λpert for the
   E2-integrand integrability).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

variable {N : ℕ}

/-- Atom integrability: `e^{−(s+λ)t}` on `Ioi 0`, Re s > 0, λ ≥ 0. -/
theorem integrableOn_cexp_shift (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s + (lam : ℂ)) * (t : ℂ)))
      (Ioi (0:ℝ)) := by
  have hre : (-(s + (lam : ℂ))).re < 0 := by
    rw [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  simpa using integrableOn_exp_mul_complex_Ioi hre 0

/-- Atom integrability: `t·e^{−(s+λ)t}` on `Ioi 0`. -/
theorem integrableOn_t_cexp_shift (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(s + (lam : ℂ)) * (t : ℂ)))
      (Ioi (0:ℝ)) := by
  have hre : 0 < (s + (lam : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  exact integrableOn_t_cexp hre

/-- Pointwise cast: `e^{−st}·(e^{−tλ}:ℂ) = e^{−(s+λ)t}`. -/
theorem cexp_mul_ofReal_exp (s : ℂ) (lam t : ℝ) :
    Complex.exp (-s * (t : ℂ)) * ((Real.exp (-(t * lam)) : ℝ) : ℂ)
      = Complex.exp (-(s + (lam : ℂ)) * (t : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Integrability of the heat-sum integrand.** -/
theorem integrableOn_cexp_heatSum (lam : Fin N → ℝ) (hlam : ∀ m, 0 ≤ lam m)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) *
        ((∑ m : Fin N, Real.exp (-(t * lam m)) : ℝ) : ℂ))
      (Ioi (0:ℝ)) := by
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ m : Fin N, Complex.exp (-(s + (lam m : ℂ)) * (t : ℂ))) (Ioi (0:ℝ)) :=
    MeasureTheory.integrable_finset_sum _
      (fun m _ => integrableOn_cexp_shift s (lam m) (hlam m) hs)
  refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioi
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Integrability of the t·weighted-heat-sum integrand.** -/
theorem integrableOn_t_cexp_heatSum (c : Fin N → ℝ) (lam : Fin N → ℝ)
    (hlam : ∀ m, 0 ≤ lam m) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
        ((∑ m : Fin N, c m * Real.exp (-(t * lam m)) : ℝ) : ℂ))
      (Ioi (0:ℝ)) := by
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ m : Fin N, ((c m : ℝ) : ℂ) *
        ((t : ℂ) * Complex.exp (-(s + (lam m : ℂ)) * (t : ℂ)))) (Ioi (0:ℝ)) :=
    MeasureTheory.integrable_finset_sum _
      (fun m _ => (integrableOn_t_cexp_shift s (lam m) (hlam m) hs).const_mul _)
  refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioi
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← cexp_mul_ofReal_exp s (lam m) t]
  push_cast
  ring

/-- **(i) The heat-sum transform is the finite resolvent trace.** -/
theorem laplace_heatSum_eq (lam : Fin N → ℝ) (hlam : ∀ m, 0 ≤ lam m)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-s * (t : ℂ)) *
        ((∑ m : Fin N, Real.exp (-(t * lam m)) : ℝ) : ℂ))
      = FstageFinite lam s := by
  rw [FstageFinite_eq_laplace_heatTrace lam hlam s hs]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **(ii) The t·weighted-heat-sum transform is the squared-resolvent sum.** -/
theorem laplace_t_heatSum_eq (c : Fin N → ℝ) (lam : Fin N → ℝ)
    (hlam : ∀ m, 0 ≤ lam m) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
        ((∑ m : Fin N, c m * Real.exp (-(t * lam m)) : ℝ) : ℂ))
      = ∑ m : Fin N, ((c m : ℝ) : ℂ) * ((s + ((lam m : ℝ) : ℂ)) ^ 2)⁻¹ := by
  have hcongr : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
      ((∑ m : Fin N, c m * Real.exp (-(t * lam m)) : ℝ) : ℂ))
      = fun t : ℝ => ∑ m : Fin N, ((c m : ℝ) : ℂ) *
          ((t : ℂ) * Complex.exp (-(s + (lam m : ℂ)) * (t : ℂ))) := by
    funext t
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [← cexp_mul_ofReal_exp s (lam m) t]
    push_cast
    ring
  rw [hcongr]
  rw [MeasureTheory.integral_finset_sum _
    (fun m _ => (integrableOn_t_cexp_shift s (lam m) (hlam m) hs).const_mul _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact (sq_inv_eq_laplace_t_exp s (lam m) (hlam m) hs).symm

#print axioms integrableOn_cexp_heatSum
#print axioms integrableOn_t_cexp_heatSum
#print axioms laplace_heatSum_eq
#print axioms laplace_t_heatSum_eq

end

end RHFormalization
