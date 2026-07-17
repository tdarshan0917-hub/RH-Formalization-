import RHFormalization.GrowthIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace RHFormalization

open MeasureTheory Real Set Complex HurwitzZeta Asymptotics Filter

/-- **G3b-tail: the tail of the Mellin integral is bounded by a Gamma value.**
For `σ > 0`, the tail `∫_{Ioi T₀} t^(σ-1)·‖f_modif t‖` (with `T₀ ≥ 0` the decay threshold from G2)
is bounded by `C · (1/p)^σ · Γ(σ)`. This is the super-polynomial (Gamma) part of `G(σ)`'s growth. -/
theorem fmodif_tail_le_gamma {σ : ℝ} (hσ : 0 < σ) :
    ∃ (p C T₀ : ℝ), 0 < p ∧ 0 ≤ C ∧ 0 ≤ T₀ ∧
      ∫ t in Ioi T₀, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
        ≤ C * ((1 / p) ^ σ * Real.Gamma σ) := by
  obtain ⟨p, C, T₀', hp, hC, hbd⟩ := fmodif_exp_bound
  refine ⟨p, C, max T₀' 0, hp, hC, le_max_right _ _, ?_⟩
  set T : ℝ := max T₀' 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hTsub : Ioi T ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hT0
  -- the scaled Gamma integrand g t = C * (t^(σ-1) * exp(-(p t))) is integrable on Ioi 0
  have hgInt0 : IntegrableOn (fun t => t ^ (σ - 1) * Real.exp (-(p * t))) (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := p)
      (by linarith) le_rfl hp
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hgIntT : IntegrableOn (fun t => t ^ (σ - 1) * Real.exp (-(p * t))) (Ioi T) :=
    hgInt0.mono_set hTsub
  -- Step 1: tail of ‖f_modif‖ integrand ≤ tail of C * gamma-integrand, pointwise via G2
  have hstep1 : ∫ t in Ioi T, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ ∫ t in Ioi T, C * (t ^ (σ - 1) * Real.exp (-(p * t))) := by
    refine setIntegral_mono_on ((fmodif_mellin_integrable σ).mono_set hTsub)
      (hgIntT.const_mul C) measurableSet_Ioi ?_
    · intro t ht
      have htT : T ≤ t := le_of_lt ht
      have ht0 : (0:ℝ) < t := lt_of_le_of_lt hT0 ht
      have hbound := hbd t ((le_max_left T₀' 0).trans htT)
      have hpow : (0:ℝ) ≤ t ^ (σ - 1) := Real.rpow_nonneg ht0.le _
      have : t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ (σ - 1) * (C * Real.exp (-p * t)) :=
        mul_le_mul_of_nonneg_left hbound hpow
      calc t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
          ≤ t ^ (σ - 1) * (C * Real.exp (-p * t)) := this
        _ = C * (t ^ (σ - 1) * Real.exp (-(p * t))) := by rw [neg_mul]; ring
  -- Step 2: ∫_{Ioi T} C*g = C * ∫_{Ioi T} g ≤ C * ∫_{Ioi 0} g
  have hstep2 : ∫ t in Ioi T, C * (t ^ (σ - 1) * Real.exp (-(p * t)))
      ≤ C * ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * Real.exp (-(p * t)) := by
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hC
    apply setIntegral_mono_set hgInt0
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      positivity
    · exact (HasSubset.Subset.eventuallyLE hTsub)
  -- Step 3: the Gamma integral value
  have hstep3 : ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * Real.exp (-(p * t))
      = (1 / p) ^ σ * Real.Gamma σ := integral_rpow_mul_exp_neg_mul_Ioi hσ hp
  calc ∫ t in Ioi T, t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖
      ≤ ∫ t in Ioi T, C * (t ^ (σ - 1) * Real.exp (-(p * t))) := hstep1
    _ ≤ C * ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * Real.exp (-(p * t)) := hstep2
    _ = C * ((1 / p) ^ σ * Real.Gamma σ) := by rw [hstep3]

#print axioms fmodif_tail_le_gamma

end RHFormalization
