-- SENTINEL: R3-v2
import RHFormalization.SpikeCosSumBridge
import RHFormalization.GaussianIoiTailSqrt
import Mathlib

/-!
# Sqrt-tail spike-sum comparison (defect-gate R3)

Primed versions of the G3 chain with the truncation leg routed through
`gaussian_Ioi_tail_le_sqrt` (R2) instead of `gaussian_Ioi_tail_le`:
the tail term `e^{−t(Nh)²}/(t·Nh)` becomes `e^{−t(Nh)²/2}·√(2π/t)`,
which is `t`-integrable near 0 (∫₀^{t₀}√(2π/t)e^{−tM²/2}dt = O(1/M)) —
the form the G4 short-time Laplace piece needs. Banked originals untouched.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- Pointwise Gaussian domination of cosGauss. -/
theorem abs_cosGauss_le (t a ξ : ℝ) :
    |cosGauss t a ξ| ≤ Real.exp (-t * ξ ^ 2) := by
  unfold cosGauss
  rw [abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
  calc Real.exp (-(t * ξ ^ 2)) * |Real.cos (ξ * a)|
      ≤ Real.exp (-(t * ξ ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = Real.exp (-(t * ξ ^ 2)) := mul_one _

/-- **Primed finite-to-Ioi comparison**: truncation error ≤ sqrt-form tail. -/
theorem cosGauss_interval_vs_Ioi' (t a B : ℝ) (ht : 0 < t) (hB : 0 < B) :
    |(∫ ξ in (0:ℝ)..B, cosGauss t a ξ)
        - ∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ|
      ≤ Real.exp (-(t * B ^ 2) / 2) * Real.sqrt (2 * Real.pi / t) := by
  have hint := cosGauss_integrable t a ht
  have hset : Set.Ioi (0:ℝ) = Set.Ioc 0 B ∪ Set.Ioi B :=
    (Set.Ioc_union_Ioi_eq_Ioi hB.le).symm
  -- ∫_{Ioi 0} = ∫_{Ioc 0 B} + ∫_{Ioi B}
  have hsplit : (∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ)
      = (∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
        + ∫ ξ in Set.Ioi B, cosGauss t a ξ := by
    rw [hset, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint.integrableOn hint.integrableOn]
  have hIoc : (∫ ξ in (0:ℝ)..B, cosGauss t a ξ)
      = ∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ :=
    intervalIntegral.integral_of_le hB.le
  have habs : |∫ ξ in Set.Ioi B, cosGauss t a ξ|
      ≤ ∫ ξ in Set.Ioi B, Real.exp (-t * ξ ^ 2) := by
    calc |∫ ξ in Set.Ioi B, cosGauss t a ξ|
        ≤ ∫ ξ in Set.Ioi B, |cosGauss t a ξ| := by
          first
            | exact abs_integral_le_integral_abs
            | exact MeasureTheory.abs_integral_le_integral_abs
            | exact norm_integral_le_integral_norm _
      _ ≤ ∫ ξ in Set.Ioi B, Real.exp (-t * ξ ^ 2) := by
          refine setIntegral_mono_on hint.abs.integrableOn
            (integrable_exp_neg_mul_sq ht).integrableOn
            measurableSet_Ioi (fun ξ _ => abs_cosGauss_le t a ξ)
  calc |(∫ ξ in (0:ℝ)..B, cosGauss t a ξ)
        - ∫ ξ in Set.Ioi (0:ℝ), cosGauss t a ξ|
      = |∫ ξ in Set.Ioi B, cosGauss t a ξ| := by
        rw [hsplit, hIoc]
        rw [show (∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
            - ((∫ ξ in Set.Ioc (0:ℝ) B, cosGauss t a ξ)
              + ∫ ξ in Set.Ioi B, cosGauss t a ξ)
            = -(∫ ξ in Set.Ioi B, cosGauss t a ξ) by ring]
        exact abs_neg _
    _ ≤ ∫ ξ in Set.Ioi B, Real.exp (-t * ξ ^ 2) := habs
    _ ≤ Real.exp (-(t * B ^ 2) / 2) * Real.sqrt (2 * Real.pi / t) :=
        gaussian_Ioi_tail_le_sqrt t B ht hB.le

/-- **Primed cosine comparison**: sqrt-form tail. -/
theorem cosGauss_sum_vs_halfline' (t a h : ℝ) (ht : 0 < t) (hh : 0 < h)
    (N : ℕ) (hN : 0 < N) :
    |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t)))|
      ≤ h * (1 + |a| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((N : ℝ) * h) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t) := by
  have hNh : (0:ℝ) < (N : ℝ) * h := by positivity
  have h1 := cosGauss_partition_error t a h ht hh N
  have h2 := cosGauss_interval_vs_Ioi' t a ((N : ℝ) * h) ht hNh
  rw [integral_cosGauss_Ioi t a ht] at h2
  calc |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t)))|
      ≤ |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
            - ∫ x in (0:ℝ)..((N : ℝ) * h), cosGauss t a x|
          + |(∫ x in (0:ℝ)..((N : ℝ) * h), cosGauss t a x)
            - (1 / 2) * (Real.sqrt (Real.pi / t)
                * Real.exp (-a ^ 2 / (4 * t)))| :=
        abs_sub_le _ (∫ x in (0:ℝ)..((N : ℝ) * h), cosGauss t a x) _
    _ ≤ h * (1 + |a| * Real.sqrt (Real.pi / t))
          + Real.exp (-(t * ((N : ℝ) * h) ^ 2) / 2)
              * Real.sqrt (2 * Real.pi / t) := add_le_add h1 h2

/-- **Primed G3 closer**: the spike-sum comparison with the sqrt-form tail. -/
theorem abs_spikeCosSum_defect_le' (L t a : ℝ) (hL : 0 < L) (ht : 0 < t)
    (hN : 0 < N) :
    |(Real.pi / L) * spikeCosSum N L t a
        - Real.pi * heatKernelRealScalar t a|
      ≤ (Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2) / 2)
            * Real.sqrt (2 * Real.pi / t) := by
  have hh : (0:ℝ) < Real.pi / L := by positivity
  have hmain := cosGauss_sum_vs_halfline' t a (Real.pi / L) ht hh N hN
  rw [spikeCosSum_eq_riemann L t a hL, heatKernel_eq_halfline_const t a ht,
    Finset.mul_sum]
  convert hmain using 3

#print axioms abs_cosGauss_le
#print axioms cosGauss_interval_vs_Ioi'
#print axioms cosGauss_sum_vs_halfline'
#print axioms abs_spikeCosSum_defect_le'

end

end RHFormalization
