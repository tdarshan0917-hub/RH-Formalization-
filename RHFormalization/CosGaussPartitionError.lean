import RHFormalization.CosGaussMajorantIntegral
import Mathlib

/-!
# Cosine-Gaussian partition error — G3-ii-b sub-brick 5a
SENTINEL: cosgauss-partition-v2

ROUTE CARD
1. `cosGauss_partition_error`: the partition engine instantiated at
   f = cosGauss with the closed majorant:
   `|Σ_{k<N} h·f((k+1)h) − ∫₀^{Nh} f| ≤ h·(1 + |a|·√(π/t))`.
2. Chain: partition_endpoint_riemann_error → integral_mono_on with
   abs_cosGaussDeriv_le → integral_cosGauss_majorant_le.
3. Sub-brick 5b then adds the Ioi tail + evenness + the banked
   integral_cos_mul_gaussian_real to land on π·G_t(a).
-/

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory

/-- **The instantiated partition comparison** with explicit constant. -/
theorem cosGauss_partition_error (t a h : ℝ) (ht : 0 < t) (hh : 0 < h)
    (N : ℕ) :
    |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - ∫ x in (0 : ℝ)..((N : ℝ) * h), cosGauss t a x|
      ≤ h * (1 + |a| * Real.sqrt (Real.pi / t)) := by
  have hNh : (0 : ℝ) ≤ (N : ℝ) * h := by positivity
  -- the partition engine
  have hmain := partition_endpoint_riemann_error (cosGauss t a)
    (cosGaussDeriv t a) h hh N
    (fun x _ => cosGauss_hasDerivAt t a x)
    ((cosGaussDeriv_continuous t a).continuousOn)
  -- bound the variation integral by the majorant integral
  have hival : IntervalIntegrable (fun x => |cosGaussDeriv t a x|)
      volume 0 ((N : ℝ) * h) :=
    ((cosGaussDeriv_continuous t a).abs).intervalIntegrable 0 ((N : ℝ) * h)
  have himaj : IntervalIntegrable
      (fun ξ : ℝ => (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)))
      volume 0 ((N : ℝ) * h) := by
    apply Continuous.intervalIntegrable
    continuity
  have hmono : (∫ x in (0 : ℝ)..((N : ℝ) * h), |cosGaussDeriv t a x|)
      ≤ ∫ ξ in (0 : ℝ)..((N : ℝ) * h),
          (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)) := by
    apply intervalIntegral.integral_mono_on hNh hival himaj
    intro ξ hξ
    exact abs_cosGaussDeriv_le t a ξ ht.le hξ.1
  have hclosed := integral_cosGauss_majorant_le t a ((N : ℝ) * h) ht hNh
  calc |(∑ k ∈ Finset.range N, h * cosGauss t a (((k : ℝ) + 1) * h))
        - ∫ x in (0 : ℝ)..((N : ℝ) * h), cosGauss t a x|
      ≤ h * ∫ x in (0 : ℝ)..((N : ℝ) * h), |cosGaussDeriv t a x| := hmain
    _ ≤ h * ∫ ξ in (0 : ℝ)..((N : ℝ) * h),
          (2 * t * ξ + |a|) * Real.exp (-(t * ξ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hmono hh.le
    _ ≤ h * (1 + |a| * Real.sqrt (Real.pi / t)) := by
        apply mul_le_mul_of_nonneg_left hclosed hh.le

#print axioms cosGauss_partition_error

end RHFormalization
