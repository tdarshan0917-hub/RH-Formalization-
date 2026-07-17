-- SENTINEL: E1-v8
import RHFormalization.RateLaplaceIntegrals
import RHFormalization.AdaptiveWeightedDefectSum
import Mathlib

/-!
# The Laplace integral of the stage defect rate (defect-gate E1)

  ∫₀^∞ e^{−δt}·adaptiveStageDefectRate c n t dt
    ≤ (1/(2L))·(1/δ) + (πR/(2L))·δ^{−1/2} + 1/M + ((1+log N)/(2πL))·(1/δ)

with M = Nπ/L. Pieces via L1; the Gaussian piece is exactly 1/M.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- Integrability: `e^{−δt}` on `Ioi 0`. -/
theorem exp_neg_mul_integrableOn (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => Real.exp (-δ * t)) (Set.Ioi (0:ℝ)) :=
  exp_neg_integrableOn_Ioi 0 hδ

/-- Integrability: `t^{−1/2}·e^{−δt}` on `Ioi 0`. -/
theorem rpow_neg_half_exp_integrableOn (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-δ * t))
      (Set.Ioi (0:ℝ)) := by
  have hq : (-1:ℝ) < -(1/2) := by norm_num
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := -(1/2)) (b := δ) hq le_rfl hδ
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [Real.rpow_one]

/-- Bridge: `√(x/t) = √x · t^{−1/2}` for `t > 0`, `0 ≤ x`. -/
theorem sqrt_div_eq_rpow (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.sqrt (x / t) = Real.sqrt x * t ^ (-(1/2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.div_rpow hx ht.le, Real.rpow_neg ht.le,
    division_def]

/-- **E1 — the rate's Laplace bound**. `M := Nπ/L`. -/
theorem laplace_stageDefectRate_le (c : ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ t in Set.Ioi (0:ℝ),
        Real.exp (-δ * t) * adaptiveStageDefectRate c n t
      ≤ (1 / (2 * adaptiveL c n)) * (1/δ)
        + (Real.pi * admR n / (2 * adaptiveL c n)) * δ ^ (-(1/2) : ℝ)
        + 1 / ((adaptiveN c n : ℝ) * (Real.pi / adaptiveL c n))
        + ((1 + Real.log (adaptiveN c n)) / (2 * Real.pi * adaptiveL c n))
            * (1/δ) := by
  set L : ℝ := adaptiveL c n with hLdef
  set R : ℝ := admR n with hRdef
  set M : ℝ := (adaptiveN c n : ℝ) * (Real.pi / L) with hMdef
  have hL : (0:ℝ) < L := adaptiveL_pos c n
  have hR : (0:ℝ) < R := admR_pos n
  have hN : (0:ℝ) < (adaptiveN c n : ℝ) := by
    exact_mod_cast adaptiveN_pos c n
  have hM : (0:ℝ) < M := by rw [hMdef]; positivity
  -- the four pieces (f3's exponent in the DEF's shape: −(t·M²)/2)
  set f1 : ℝ → ℝ := fun t => (1 / (2 * L)) * Real.exp (-δ * t) with hf1
  set f2 : ℝ → ℝ := fun t => (Real.sqrt Real.pi * R / (2 * L))
      * (t ^ (-(1/2) : ℝ) * Real.exp (-δ * t)) with hf2
  set f3 : ℝ → ℝ := fun t => (Real.sqrt (2 * Real.pi) / (2 * Real.pi))
      * (t ^ (-(1/2) : ℝ)
        * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2) / 2))) with hf3
  set f4 : ℝ → ℝ := fun t => ((1 + Real.log (adaptiveN c n))
      / (2 * Real.pi * L)) * Real.exp (-δ * t) with hf4
  -- pointwise expansion
  have hexpand : ∀ t ∈ Set.Ioi (0:ℝ),
      Real.exp (-δ * t) * adaptiveStageDefectRate c n t
        = f1 t + f2 t + f3 t + f4 t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    rw [hf1, hf2, hf3, hf4]
    unfold adaptiveStageDefectRate
    rw [← hLdef, ← hRdef]
    rw [sqrt_div_eq_rpow Real.pi t Real.pi_pos.le ht0,
      sqrt_div_eq_rpow (2 * Real.pi) t (by positivity) ht0]
    rw [← hMdef]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hexpand]
  -- integrability, explicit-lambda typed
  have hI1 : IntegrableOn f1 (Set.Ioi (0:ℝ)) :=
    (exp_neg_mul_integrableOn δ hδ).const_mul _
  have hI2 : IntegrableOn f2 (Set.Ioi (0:ℝ)) :=
    (rpow_neg_half_exp_integrableOn δ hδ).const_mul _
  have hI3 : IntegrableOn f3 (Set.Ioi (0:ℝ)) := by
    have h := rpow_neg_half_exp_integrableOn (δ + M ^ 2 / 2) (by positivity)
    rw [hf3]
    refine (h.congr_fun (fun t _ => ?_) measurableSet_Ioi).const_mul _
    rw [← Real.exp_add]
    congr 1
    ring
  have hI4 : IntegrableOn f4 (Set.Ioi (0:ℝ)) :=
    (exp_neg_mul_integrableOn δ hδ).const_mul _
  have hI12 : IntegrableOn (fun t : ℝ => f1 t + f2 t) (Set.Ioi (0:ℝ)) :=
    hI1.add hI2
  have hI123 : IntegrableOn (fun t : ℝ => f1 t + f2 t + f3 t)
      (Set.Ioi (0:ℝ)) := hI12.add hI3
  -- split
  have hsplit : (∫ t in Set.Ioi (0:ℝ), (f1 t + f2 t + f3 t + f4 t))
      = (∫ t in Set.Ioi (0:ℝ), f1 t) + (∫ t in Set.Ioi (0:ℝ), f2 t)
        + (∫ t in Set.Ioi (0:ℝ), f3 t) + (∫ t in Set.Ioi (0:ℝ), f4 t) := by
    rw [integral_add hI123 hI4, integral_add hI12 hI3, integral_add hI1 hI2]
  rw [hsplit]
  -- evaluate/bound each piece
  have hv1 : (∫ t in Set.Ioi (0:ℝ), f1 t) = (1 / (2 * L)) * (1/δ) := by
    rw [hf1, integral_const_mul, laplace_one_eq δ hδ]
  have hv2 : (∫ t in Set.Ioi (0:ℝ), f2 t)
      = (Real.pi * R / (2 * L)) * δ ^ (-(1/2) : ℝ) := by
    rw [hf2, integral_const_mul, laplace_inv_sqrt_eq δ hδ]
    rw [show (Real.sqrt Real.pi * R / (2 * L))
          * (Real.sqrt Real.pi * δ ^ (-(1/2) : ℝ))
        = (Real.sqrt Real.pi * Real.sqrt Real.pi) * R / (2 * L)
          * δ ^ (-(1/2) : ℝ) by ring,
      Real.mul_self_sqrt Real.pi_pos.le]
  have hv3 : (∫ t in Set.Ioi (0:ℝ), f3 t) ≤ 1 / M := by
    rw [hf3, integral_const_mul]
    have hcongr : (∫ t in Set.Ioi (0:ℝ), t ^ (-(1/2) : ℝ)
          * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2) / 2)))
        = ∫ t in Set.Ioi (0:ℝ), t ^ (-(1/2) : ℝ)
          * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2 / 2))) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      rw [show -(t * M ^ 2) / 2 = -(t * M ^ 2 / 2) by ring]
    rw [hcongr]
    have h3 := laplace_inv_sqrt_gauss_le δ M hδ hM
    calc (Real.sqrt (2 * Real.pi) / (2 * Real.pi))
          * ∫ t in Set.Ioi (0:ℝ), t ^ (-(1/2) : ℝ)
            * (Real.exp (-δ * t) * Real.exp (-(t * M ^ 2 / 2)))
        ≤ (Real.sqrt (2 * Real.pi) / (2 * Real.pi))
            * (Real.sqrt (2 * Real.pi) / M) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / M := by
          rw [div_mul_div_comm,
            Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
          rw [div_eq_div_iff (by positivity) hM.ne']
          ring
  have hv4 : (∫ t in Set.Ioi (0:ℝ), f4 t)
      = ((1 + Real.log (adaptiveN c n)) / (2 * Real.pi * L)) * (1/δ) := by
    rw [hf4, integral_const_mul, laplace_one_eq δ hδ]
  rw [hv1, hv2, hv4]
  linarith [hv3]

#print axioms exp_neg_mul_integrableOn
#print axioms rpow_neg_half_exp_integrableOn
#print axioms sqrt_div_eq_rpow
#print axioms laplace_stageDefectRate_le

end

end RHFormalization
