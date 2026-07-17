import RHFormalization.GalerkinDuhamel1ChannelCollapse
import Mathlib

/-!
# Galerkin first-order finite spike kernel

Packages the collapsed order-1 Galerkin channel as the finite heat-kernel
bump trace attached to one prime channel.

This is the finite-N/L Galerkin version of the B-side spike kernel.
The next analytic bridge is to compare this finite kernel with `heatKernelG`
/ `shiftedHeatIntegrand`.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Finite Galerkin spike kernel for one channel `q`. -/
noncomputable def finiteGalerkinSpikeKernel
    (δ : ℝ) (q : ℕ) (L : ℝ) (t : ℝ) : ℝ :=
  ∑ m : Fin N,
    heatWeight (N := N) L t m
      * bumpMatrixElement δ q L (m + 1) (m + 1)

/-- The collapsed order-1 channel is the finite Galerkin spike kernel. -/
theorem duhamel1Channel_eq_finiteGalerkinSpikeKernel
    (δ : ℝ) (q : ℕ) (L : ℝ) (t u : ℝ) :
    duhamel1Channel (N := N) δ q L t u =
      finiteGalerkinSpikeKernel (N := N) δ q L t := by
  unfold finiteGalerkinSpikeKernel
  exact duhamel1Channel_eq_heat_bump_sum (N := N) δ q L t u

/--
The order-1 Galerkin Duhamel integrand is a weighted sum of finite Galerkin
spike kernels.

This is the first fully isolated finite-channel spike package on the genuine
operator side.
-/
theorem duhamel1Integrand_eq_finite_spike_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u =
      (2 / L) * ∑ q ∈ qs, w q * finiteGalerkinSpikeKernel (N := N) δ q L t := by
  rw [duhamel1Integrand_eq_channel_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [duhamel1Channel_eq_finiteGalerkinSpikeKernel]

#print axioms finiteGalerkinSpikeKernel
#print axioms duhamel1Channel_eq_finiteGalerkinSpikeKernel
#print axioms duhamel1Integrand_eq_finite_spike_sum

end
end RHFormalization
