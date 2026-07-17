import RHFormalization.CosGaussHalfLine
import RHFormalization.GalerkinSpikeDefectSplit
import Mathlib

/-!
# Spike cosine sum bridge — G3 CLOSER
SENTINEL: spike-bridge-v3

ROUTE CARD
1. `spikeCosSum_eq_riemann`: spikeCosSum IS the cosGauss Riemann sum at
   h = π/L (Fin ↔ range reindex + exact term match via λ_m = ((m+1)π/L)²).
2. `heatKernel_eq_halfline_const`: π·G_t(a) = (1/2)√(π/t)e^{−a²/4t} — the
   landing constant identification.
3. `abs_spikeCosSum_defect_le` — **G3 COMPLETE**: |(π/L)·spikeCosSum −
   π·G_t(a)| ≤ (π/L)(1+|a|√(π/t)) + tail(Nπ/L).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- The spike cosine sum is the cosGauss endpoint Riemann sum at `h = π/L`. -/
theorem spikeCosSum_eq_riemann (L t a : ℝ) (hL : 0 < L) :
    spikeCosSum N L t a
      = ∑ k ∈ Finset.range N, cosGauss t a (((k : ℝ) + 1) * (Real.pi / L)) := by
  unfold spikeCosSum cosGauss
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => Real.exp (-(t * ((((k : ℝ)) + 1) * (Real.pi / L)) ^ 2))
      * Real.cos ((((k : ℝ) + 1) * (Real.pi / L)) * a)) N]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold galerkinLam
  have harg1 : ((((m : ℕ) : ℝ)) + 1) * Real.pi / L
      = (((m : ℕ) : ℝ) + 1) * (Real.pi / L) := by
    field_simp
  have h1 : (((((m : ℕ) : ℝ)) + 1) * Real.pi / L) ^ 2
      = ((((m : ℕ) : ℝ) + 1) * (Real.pi / L)) ^ 2 := by
    rw [harg1]
  have h2 : (((m : ℕ) : ℝ) + 1) * Real.pi * a / L
      = ((((m : ℕ) : ℝ) + 1) * (Real.pi / L)) * a := by
    field_simp
  rw [h1, h2]

/-- The landing constant is exactly `π·heatKernelRealScalar`. -/
theorem heatKernel_eq_halfline_const (t a : ℝ) (ht : 0 < t) :
    Real.pi * heatKernelRealScalar t a
      = (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-a ^ 2 / (4 * t))) := by
  unfold heatKernelRealScalar
  have hsqrt4 : Real.sqrt (4 * Real.pi * t)
      = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4:ℝ) * Real.pi * t = (2:ℝ)^2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul Real.pi_pos.le]
    ring
  have hsqrtdiv : Real.sqrt (Real.pi / t)
      = Real.sqrt Real.pi / Real.sqrt t := by
    rw [Real.sqrt_div Real.pi_pos.le]
  have hexp : Real.exp (-(a ^ 2) / (4 * t)) = Real.exp (-a ^ 2 / (4 * t)) := by
    norm_num
  rw [hsqrt4, hsqrtdiv, hexp]
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_eq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hpi_eq, hst, hsp, Real.exp_pos (-a ^ 2 / (4 * t))]

/-- **G3 COMPLETE — the spike-sum comparison**. -/
theorem abs_spikeCosSum_defect_le (L t a : ℝ) (hL : 0 < L) (ht : 0 < t)
    (hN : 0 < N) :
    |(Real.pi / L) * spikeCosSum N L t a
        - Real.pi * heatKernelRealScalar t a|
      ≤ (Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
        + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2))
            / (t * ((N : ℝ) * (Real.pi / L))) := by
  have hh : (0:ℝ) < Real.pi / L := by positivity
  have hmain := cosGauss_sum_vs_halfline t a (Real.pi / L) ht hh N hN
  rw [spikeCosSum_eq_riemann L t a hL, heatKernel_eq_halfline_const t a ht,
    Finset.mul_sum]
  convert hmain using 3

#print axioms spikeCosSum_eq_riemann
#print axioms heatKernel_eq_halfline_const
#print axioms abs_spikeCosSum_defect_le

end

end RHFormalization
