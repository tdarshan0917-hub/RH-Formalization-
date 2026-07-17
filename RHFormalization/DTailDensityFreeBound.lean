import Mathlib

/-!
# D.TAIL density-normalization core (manuscript p179).

The manuscript's tail bound: the free Dirichlet Laplacian on [-L, L] has
  Tr(e^{-t₀ A_L}) = ∫_{-L}^{L} K_D(t₀; u, u) du ≤ 2L · (4πt₀)^{-1/2}
because the interval diagonal heat kernel is bounded by the whole-line value
(4πt₀)^{-1/2}. Dividing by 2L gives the DENSITY-NORMALIZED bound
  (1/(2L)) · Tr(e^{-t₀ A_L}) ≤ (4πt₀)^{-1/2},
which is INDEPENDENT of L (hence of the cutoff stage α). This file proves the
L-cancellation arithmetic that is the uniformity mechanism: the 2L in the trace
bound cancels the 1/(2L) normalization, leaving an α-independent constant.

This does NOT use any prime sum and does NOT depend on σ > 1/2.
-/

namespace RHFormalization
open Real

/-- The whole-line free heat-kernel diagonal value at time `t`. -/
noncomputable def freeHeatDiagonal (t : ℝ) : ℝ := 1 / Real.sqrt (4 * Real.pi * t)

theorem freeHeatDiagonal_nonneg (t : ℝ) : 0 ≤ freeHeatDiagonal t := by
  unfold freeHeatDiagonal
  positivity

/-- **D.TAIL density-normalization (the L-cancellation, p179).**
If the free Dirichlet trace on `[-L, L]` is bounded by `2L · freeHeatDiagonal t₀`
(interval kernel ≤ whole-line kernel, integrated over length `2L`), then the
density-normalized trace `(1/(2L)) · traceBound` is bounded by `freeHeatDiagonal t₀`,
INDEPENDENTLY of `L`. This is the manuscript's "dividing by 2L gives ≤ (4πt₀)^{-1/2}". -/
theorem dTail_density_normalized_bound
    (t₀ L : ℝ) (ht₀ : 0 < t₀) (hL : 0 < L)
    (traceBound : ℝ)
    (h_trace_le : traceBound ≤ 2 * L * freeHeatDiagonal t₀) :
    (1 / (2 * L)) * traceBound ≤ freeHeatDiagonal t₀ := by
  have h2L : 0 < 2 * L := by positivity
  calc
    (1 / (2 * L)) * traceBound
        ≤ (1 / (2 * L)) * (2 * L * freeHeatDiagonal t₀) := by
          apply mul_le_mul_of_nonneg_left h_trace_le
          positivity
    _ = freeHeatDiagonal t₀ := by
          field_simp

#print axioms dTail_density_normalized_bound

end RHFormalization
