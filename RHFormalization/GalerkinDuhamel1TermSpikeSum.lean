import RHFormalization.GalerkinDuhamel1TermIntegral
import RHFormalization.GalerkinDuhamel1FiniteSpikeKernel
import Mathlib

/-!
# Order-1 Duhamel term = t · (finite spike sum)

`duhamel1Integrand t u = ∑_q w q · finiteGalerkinSpikeKernel q t` is **constant in `u`**
(the RHS has no `u`), so its time integral over `[0,t]` is `t · (spike sum)`.

  duhamel1Term t = ∫₀ᵗ (∑_q w q · spikeKernel q t) du = t · ∑_q w q · spikeKernel q t.

This is the integrated order-1 = spikes identity, the next Dyson brick.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section
open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- **Order-1 Duhamel term equals `t · (finite spike sum)`.** Since the order-1
integrand is constant in the integration variable `u`, the time integral is `t ×`
the spike sum. -/
theorem duhamel1Term_eq_t_smul_spike_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    duhamel1Term (N := N) δ qs w L t
      = t * (2 / L) * ∑ q ∈ qs, w q * finiteGalerkinSpikeKernel (N := N) δ q L t := by
  unfold duhamel1Term
  rw [show (fun u : ℝ => duhamel1Integrand (N := N) δ qs w L t u)
        = (fun _ : ℝ => (2 / L) * ∑ q ∈ qs, w q * finiteGalerkinSpikeKernel (N := N) δ q L t) from ?_]
  · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  · funext u
    exact duhamel1Integrand_eq_finite_spike_sum (N := N) δ qs w L t u

#print axioms duhamel1Term_eq_t_smul_spike_sum

end
end RHFormalization
