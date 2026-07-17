import RHFormalization.GalerkinSpikeShortTimeCalculus
import RHFormalization.CanonicalPrimePowerHeatKernelNormBounds
import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff
import RHFormalization.AdmissibleGalerkinStage
import Mathlib

/-!
# GalerkinSpikeShortTimeBound — spike sector of the head bound

`∑_{q ∈ active(admR n)} ‖q.weightC‖·‖heatKernelG t q.center‖ ≤ C`
uniformly in `n` AND `t ∈ (0, spikeT0]`.

Every active pair has `natValue ≥ 2`, hence `center ≥ log 2 > 0`. The Gaussian
`e^{-center²/(4t)}` therefore beats BOTH the `(4πt)^{-1/2}` prefactor and the
`≍ e^{admR n}` pair count: half the exponent kills the prefactor (banked
`sqrt_inv_mul_exp_neg_div_le`), half turns into `natValue^{-4}` (banked
`gaussian_center_split` plus `t ≤ spikeT0 = log 2 / 32`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real Finset

/-- Every valid pair has `2 ≤ natValue`. -/
theorem two_le_natValue {q : PrimePowerPair} (hq : IsPrimePowerPair q) :
    2 ≤ q.natValue := by
  have hp : 2 ≤ q.p := hq.1.two_le
  have hpow : q.p ≤ q.p ^ q.m := Nat.le_self_pow hq.2.ne' q.p
  calc (2 : ℕ) ≤ q.p := hp
    _ ≤ q.p ^ q.m := hpow
    _ = q.natValue := rfl

/-- Every valid pair has `center ≥ log 2`. -/
theorem log_two_le_center {q : PrimePowerPair} (hq : IsPrimePowerPair q) :
    Real.log 2 ≤ q.center := by
  have h2 : (2 : ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast two_le_natValue hq
  unfold PrimePowerPair.center
  exact Real.log_le_log (by norm_num) h2

/-- Membership unpacking (banked donor route). -/
theorem mem_active_isPrimePowerPair {R : ℝ} {q : PrimePowerPair}
    (hq : q ∈ activePrimePowerPairsCenterBelow R) : IsPrimePowerPair q := by
  have h : IsPrimePowerPair q ∧ q.center ≤ R := by
    first
      | exact (valid_primePower_center_le_finite R).mem_toFinset.mp hq
      | simpa using (valid_primePower_center_le_finite R).mem_toFinset.mp hq
  exact h.1

/-- **Termwise spike bound.** For `0 < t ≤ spikeT0` and any valid pair, the
weighted heat-kernel norm is dominated by a constant times the banked
`natValue^{-3}` majorant. -/
theorem spike_term_le_natValueMajorant
    {q : PrimePowerPair} (hq : IsPrimePowerPair q)
    (t : ℝ) (ht : 0 < t) (ht0 : t ≤ spikeT0) :
    ‖q.weightC‖ * ‖heatKernelG t q.center‖
      ≤ (Real.sqrt (4 * Real.pi))⁻¹ * (Real.sqrt ((Real.log 2)^2 / 8))⁻¹
          * heatKernelNatValueMajorant q := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0:ℝ) < (Real.log 2)^2 / 8 := by positivity
  have hcen : Real.log 2 ≤ q.center := log_two_le_center hq
  have hcen0 : (0:ℝ) < q.center := lt_of_lt_of_le hlog2 hcen
  have hnv2 : (2:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast two_le_natValue hq
  have hnv0 : (0:ℝ) < ((q.natValue : ℕ) : ℝ) := by linarith

  -- Step 1: expand the kernel norm and factor the prefactor
  rw [norm_heatKernelG_eq t q.center ht]
  have hpref : (1:ℝ) / Real.sqrt (4 * Real.pi * t)
      = (Real.sqrt (4 * Real.pi))⁻¹ * (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * Real.pi)]
    field_simp
  rw [hpref]

  -- Step 2: split the Gaussian exponent in half
  have hsplit : Real.exp (-(q.center ^ 2) / (4 * t))
      = Real.exp (-(q.center ^ 2) / (8 * t)) * Real.exp (-(q.center ^ 2) / (8 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring

  -- Step 3a: first half + center ≥ log 2  ⟹  kills the (√t)⁻¹ prefactor
  have hA : (Real.sqrt t)⁻¹ * Real.exp (-(q.center ^ 2) / (8 * t))
      ≤ (Real.sqrt ((Real.log 2)^2 / 8))⁻¹ := by
    have hmono : Real.exp (-(q.center ^ 2) / (8 * t))
        ≤ Real.exp (-((Real.log 2)^2 / 8) / t) := by
      apply Real.exp_le_exp.mpr
      have hre : -((Real.log 2)^2 / 8) / t = -((Real.log 2)^2) / (8 * t) := by
        field_simp
      rw [hre]
      have hsq : (Real.log 2)^2 ≤ q.center ^ 2 := by nlinarith [hcen, hlog2.le]
      gcongr
    calc (Real.sqrt t)⁻¹ * Real.exp (-(q.center ^ 2) / (8 * t))
        ≤ (Real.sqrt t)⁻¹ * Real.exp (-((Real.log 2)^2 / 8) / t) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ (Real.sqrt ((Real.log 2)^2 / 8))⁻¹ :=
          sqrt_inv_mul_exp_neg_div_le ((Real.log 2)^2 / 8) t hc ht

  -- Step 3b: second half + t ≤ spikeT0  ⟹  natValue^{-4} ≤ (natValue^3)⁻¹
  have hB : Real.exp (-(q.center ^ 2) / (8 * t)) ≤ (((q.natValue : ℕ) : ℝ) ^ 3)⁻¹ := by
    have hgs : Real.exp (-(q.center ^ 2) / (4 * (2 * t)))
        ≤ Real.exp (-(Real.log 2 * q.center) / (4 * (2 * t))) := by
      have h2t : (0:ℝ) < 2 * t := by linarith
      have := gaussian_center_split q.center (2 * t) hcen h2t
      convert this using 2 <;> ring
    have heq : (4 * (2 * t) : ℝ) = 8 * t := by ring
    rw [heq] at hgs
    refine le_trans hgs ?_
    -- exponent: (log 2 · center)/(8t) ≥ 4 · center  since t ≤ log 2 / 32
    have hexp4 : Real.exp (-(Real.log 2 * q.center) / (8 * t))
        ≤ Real.exp (-(4 * q.center)) := by
      apply Real.exp_le_exp.mpr
      have hts : t ≤ Real.log 2 / 32 := by unfold spikeT0 at ht0; exact ht0
      have h8t : (0:ℝ) < 8 * t := by positivity
      have h32 : 32 * t ≤ Real.log 2 := by linarith
      have hkey : q.center * (32 * t) ≤ q.center * Real.log 2 :=
        mul_le_mul_of_nonneg_left h32 hcen0.le
      rw [div_le_iff₀ h8t]
      nlinarith [hkey]
    refine le_trans hexp4 ?_
    -- e^{-4·center} = natValue^{-4} ≤ (natValue^3)⁻¹
    have hcenlog : q.center = Real.log ((q.natValue : ℕ) : ℝ) := rfl
    have hkey : Real.exp (-(4 * q.center)) = (((q.natValue : ℕ) : ℝ) ^ (4:ℕ))⁻¹ := by
      rw [hcenlog]
      have h4 : (4:ℝ) * Real.log (((q.natValue : ℕ) : ℝ))
          = Real.log ((((q.natValue : ℕ) : ℝ)) ^ (4:ℕ)) := by
        rw [Real.log_pow]; push_cast; ring
      rw [h4, Real.exp_neg, Real.exp_log (by positivity)]
    rw [hkey]
    refine inv_anti₀ (by positivity) ?_
    have h1 : (1:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by linarith
    have h3 : (0:ℝ) ≤ ((q.natValue : ℕ) : ℝ) ^ (3:ℕ) := by positivity
    calc ((q.natValue : ℕ) : ℝ) ^ (3:ℕ)
        = ((q.natValue : ℕ) : ℝ) ^ (3:ℕ) * 1 := by ring
      _ ≤ ((q.natValue : ℕ) : ℝ) ^ (3:ℕ) * ((q.natValue : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = ((q.natValue : ℕ) : ℝ) ^ (4:ℕ) := by ring

  -- assemble
  unfold heatKernelNatValueMajorant
  rw [hsplit]
  have hw0 : (0:ℝ) ≤ ‖q.weightC‖ := norm_nonneg _
  calc ‖q.weightC‖ * ((Real.sqrt (4*Real.pi))⁻¹ * (Real.sqrt t)⁻¹
          * (Real.exp (-(q.center^2)/(8*t)) * Real.exp (-(q.center^2)/(8*t))))
      = (Real.sqrt (4*Real.pi))⁻¹
          * ((Real.sqrt t)⁻¹ * Real.exp (-(q.center^2)/(8*t)))
          * (‖q.weightC‖ * Real.exp (-(q.center^2)/(8*t))) := by ring
    _ ≤ (Real.sqrt (4*Real.pi))⁻¹
          * (Real.sqrt ((Real.log 2)^2/8))⁻¹
          * (‖q.weightC‖ * (((q.natValue : ℕ) : ℝ)^3)⁻¹) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hA (by positivity)
        · exact mul_le_mul_of_nonneg_left hB hw0
        · positivity
        · positivity

/-- **SPIKE SECTOR, CLOSED.** Uniform in `n` and `t ∈ (0, spikeT0]`. -/
theorem spike_sum_short_time_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ spikeT0 →
      ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC‖ * ‖heatKernelG t q.center‖ ≤ C := by
  set A : ℝ := (Real.sqrt (4 * Real.pi))⁻¹ * (Real.sqrt ((Real.log 2)^2 / 8))⁻¹ with hA
  have hA0 : (0:ℝ) ≤ A := by
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [hA]; positivity
  refine ⟨A * ∑' q : PrimePowerPair, heatKernelNatValueMajorant q, ?_, ?_⟩
  · have hnn : (0:ℝ) ≤ ∑' q : PrimePowerPair, heatKernelNatValueMajorant q := by
      apply tsum_nonneg
      intro q
      unfold heatKernelNatValueMajorant
      positivity
    exact mul_nonneg hA0 hnn
  · intro n t ht ht0
    calc ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            ‖q.weightC‖ * ‖heatKernelG t q.center‖
        ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            A * heatKernelNatValueMajorant q := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          exact spike_term_le_natValueMajorant (mem_active_isPrimePowerPair hq) t ht ht0
      _ = A * ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            heatKernelNatValueMajorant q := by rw [Finset.mul_sum]
      _ ≤ A * ∑' q : PrimePowerPair, heatKernelNatValueMajorant q := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          refine heatKernelNatValueMajorant_summable.sum_le_tsum _ (fun q _ => ?_)
          unfold heatKernelNatValueMajorant
          positivity

#print axioms two_le_natValue
#print axioms log_two_le_center
#print axioms mem_active_isPrimePowerPair
#print axioms spike_term_le_natValueMajorant
#print axioms spike_sum_short_time_bound

end

end RHFormalization
