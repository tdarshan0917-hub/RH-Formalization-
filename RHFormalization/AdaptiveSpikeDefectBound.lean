-- SENTINEL: S2-v3
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.SpikeCosSumBridgeSqrt
import RHFormalization.GalerkinSpikeSinHarmonic
import Mathlib

/-!
# The per-spike defect bound (defect-gate Section-2 brick)

Combines the banked split identity (`galerkinSpikeKernel_split`), the
sqrt-tail cosine comparison (`abs_spikeCosSum_defect_le'`, R3), and the
t-free sin bound (`abs_spikeSinSum_le_log`, R4) into the pointwise
per-spike estimate:

  |(1/(2L))·g_N(t,a) − G_t(a)·(L−a)/(2L)|
    ≤ ((L−a)/(2L))·(1/π)·[(π/L)(1+|a|√(π/t)) + e^{−t(Nπ/L)²/2}·√(2π/t)]
      + (1/(2L))·(1/π)·(1 + log N)

Every ingredient is a banked theorem; this is the triangle assembly.
Then instantiated at the adaptive stage as `abs_adaptiveSpikeDefectT_le`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- **Generic per-spike defect bound** (t-domain). -/
theorem abs_spikeDefect_le {N : ℕ} (L t a : ℝ) (hL : 0 < L) (ht : 0 < t)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (hN : 0 < N) :
    |(1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
        - heatKernelRealScalar t a * ((L - a) / (2 * L))|
      ≤ ((L - a) / (2 * L)) * ((1 / Real.pi) *
            ((Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
              + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2) / 2)
                  * Real.sqrt (2 * Real.pi / t)))
        + (1 / (2 * L)) * ((1 / Real.pi) * (1 + Real.log N)) := by
  have hLne : L ≠ 0 := hL.ne'
  -- Step 1: algebraic identity via the banked split
  have hid : (1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
        - heatKernelRealScalar t a * ((L - a) / (2 * L))
      = ((L - a) / (2 * L)) *
          ((1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a)
        + (1 / (2 * L)) * spikeSinSum N L t a := by
    rw [galerkinSpikeKernel_split L t a hL ha0 haL]
    first
      | (field_simp; ring)
      | field_simp
      | ring_nf
  -- Step 2: cosine leg via R3' (divide by π)
  have hcos := abs_spikeCosSum_defect_le' (N := N) L t a hL ht hN
  have hπeq : Real.pi / L * spikeCosSum N L t a
        - Real.pi * heatKernelRealScalar t a
      = Real.pi * ((1 / L) * spikeCosSum N L t a
          - heatKernelRealScalar t a) := by ring
  rw [hπeq, abs_mul, abs_of_pos Real.pi_pos] at hcos
  have hD : |(1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a|
      ≤ (1 / Real.pi) *
          ((Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
            + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2) / 2)
                * Real.sqrt (2 * Real.pi / t)) := by
    have hmul := mul_le_mul_of_nonneg_left hcos
      (by positivity : (0:ℝ) ≤ 1 / Real.pi)
    calc |(1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a|
        = (1 / Real.pi) * (Real.pi *
            |(1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a|) := by
          field_simp
      _ ≤ _ := hmul
  have hfracnn : (0:ℝ) ≤ (L - a) / (2 * L) :=
    div_nonneg (sub_nonneg.mpr haL) (by positivity)
  have hA : |((L - a) / (2 * L)) *
        ((1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a)|
      ≤ ((L - a) / (2 * L)) * ((1 / Real.pi) *
          ((Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
            + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2) / 2)
                * Real.sqrt (2 * Real.pi / t))) := by
    rw [abs_mul, abs_of_nonneg hfracnn]
    exact mul_le_mul_of_nonneg_left hD hfracnn
  -- Step 3: sin leg via R4
  have hB : |(1 / (2 * L)) * spikeSinSum N L t a|
      ≤ (1 / (2 * L)) * ((1 / Real.pi) * (1 + Real.log N)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * L))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact abs_spikeSinSum_le_log L t a ht.le
  -- Step 4: assemble
  calc |(1 / (2 * L)) * galerkinSpikeKernel (N := N) L t a
        - heatKernelRealScalar t a * ((L - a) / (2 * L))|
      = |((L - a) / (2 * L)) *
            ((1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a)
          + (1 / (2 * L)) * spikeSinSum N L t a| := by rw [hid]
    _ ≤ |((L - a) / (2 * L)) *
            ((1 / L) * spikeCosSum N L t a - heatKernelRealScalar t a)|
          + |(1 / (2 * L)) * spikeSinSum N L t a| := by
        first
          | exact abs_add_le _ _
          | exact norm_add_le _ _
          | exact abs_add _ _
    _ ≤ ((L - a) / (2 * L)) * ((1 / Real.pi) *
            ((Real.pi / L) * (1 + |a| * Real.sqrt (Real.pi / t))
              + Real.exp (-(t * ((N : ℝ) * (Real.pi / L)) ^ 2) / 2)
                  * Real.sqrt (2 * Real.pi / t)))
          + (1 / (2 * L)) * ((1 / Real.pi) * (1 + Real.log N)) :=
        add_le_add hA hB

/-- **The adaptive per-spike defect bound** — the gate object
`adaptiveSpikeDefectT` obeys the Section-2 estimate at every stage. -/
theorem abs_adaptiveSpikeDefectT_le (c : ℝ) (n : ℕ) (a t : ℝ)
    (ht : 0 < t) (ha0 : 0 ≤ a) (haL : a ≤ adaptiveL c n) :
    |adaptiveSpikeDefectT c n a t|
      ≤ ((adaptiveL c n - a) / (2 * adaptiveL c n)) * ((1 / Real.pi) *
            ((Real.pi / adaptiveL c n)
                * (1 + |a| * Real.sqrt (Real.pi / t))
              + Real.exp (-(t * ((adaptiveN c n : ℝ)
                      * (Real.pi / adaptiveL c n)) ^ 2) / 2)
                  * Real.sqrt (2 * Real.pi / t)))
        + (1 / (2 * adaptiveL c n))
            * ((1 / Real.pi) * (1 + Real.log (adaptiveN c n))) := by
  unfold adaptiveSpikeDefectT
  exact abs_spikeDefect_le (adaptiveL c n) t a
    (adaptiveL_pos c n) ht ha0 haL (adaptiveN_pos c n)

#print axioms abs_spikeDefect_le
#print axioms abs_adaptiveSpikeDefectT_le

end

end RHFormalization
