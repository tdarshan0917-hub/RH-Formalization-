import RHFormalization.SpikeTransferM2Form
import RHFormalization.GalerkinDuhamel1Closed
import Mathlib

/-!
# SpikeTransferM2Closed — the M=2 split with the order-1 word in closed form

ROUTE CARD
1. Target: EXACT time-side identity
   `Tr(e^{t•(−(K+V))}) = Tr(e^{t•(−K)}) − t·Σ_m V_mm e^{−tλ_m} + E2(t)`
   — the M=2 Duhamel split (banked) with the order-1 integral replaced by
   its closed c₁-profile form (banked this session). Pure algebra:
   unfold spikeTransferE2 + integral_duhamel1_eq_c1_profile + ring.
2. Raw B on Ω? NO. B−M bare Prop? NO — exact identity, no bound.
3. Consumer: the s-side Laplace pass (P2-4c) — transform each term:
   LHS → perturbedFStage integrand (trace_exp_neg_KV_eq_eigen_sum, banked),
   free → free F-transform, c₁ profile → galerkinSpikeTransform (J_loc,
   holo banked), E2 → bounded via |E2|≤t² (banked) + T1a kit.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- **The M=2 split, order-1 word closed.** The perturbed heat trace is the
free heat trace minus the c₁ profile plus the quadratic remainder. -/
theorem spikeTransfer_M2_closed
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace
      = (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
        - t * (∑ m : Fin N,
            galerkinV (N := N) δ qs w L m m * heatWeight (N := N) L t m)
        + spikeTransferE2 (N := N) δ qs w L t := by
  unfold spikeTransferE2
  rw [integral_duhamel1_eq_c1_profile]
  ring

#print axioms spikeTransfer_M2_closed

end

end RHFormalization
