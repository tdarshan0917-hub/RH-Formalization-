-- SENTINEL: spike-transfer-m2-form-v1
import RHFormalization.SpikeTransferC1Gap
import RHFormalization.DKeyFormTraceAssembly
import Mathlib

/-! # Core brick 5 — the manuscript-form M=2 identity (D.BFF.5 shape).
`Tr(e^{−t(K+V)}) = Tr(e^{−tK}) − t·Σ_m V_mm e^{−tλ_m} + E₂(t)`,
with `E₂` DEFINED as the remainder here and given its independent
integral representation + bound in brick 6 (manuscript order). -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- The M=2 spike-transfer remainder. -/
noncomputable def spikeTransferE2
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))).trace
    - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
    + ∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u

/-- **CORE BRICK 5 (D.BFF.5 manuscript form, M=2).** -/
theorem spikeTransfer_M2_form
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace
      = (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
        - t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
            * Real.exp (-(t * galerkinLam L (m : ℕ))))
        + spikeTransferE2 (N := N) δ qs w L t := by
  unfold spikeTransferE2
  rw [duhamel1Integral_eq_t_mul_heat_trace (N := N) δ qs w L t]
  ring

/-- Companion: the remainder equals the Duhamel bridge integral plus the
order-1 integral — the seam brick 6 bounds. -/
theorem spikeTransferE2_eq_bridge_add_order1
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    spikeTransferE2 (N := N) δ qs w L t
      = (∫ u in (0:ℝ)..t,
          (Matrix.diagonal (fun m : Fin N => heatWeight (N := N) L (t - u) m)
            * (-(galerkinV (N := N) δ qs w L))
            * NormedSpace.exp (u • (-(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L)))).trace)
        + ∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u := by
  unfold spikeTransferE2
  rw [galerkinDuhamel_trace_eq_diagonal (N := N) δ qs w L t]

#print axioms spikeTransferE2
#print axioms spikeTransfer_M2_form
#print axioms spikeTransferE2_eq_bridge_add_order1
end

end RHFormalization
