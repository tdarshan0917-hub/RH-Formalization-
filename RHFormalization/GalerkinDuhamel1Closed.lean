import RHFormalization.GalerkinDuhamel1Term
import RHFormalization.GalerkinDisplacementKernel
import Mathlib

/-!
# GalerkinDuhamel1Closed — the order-1 Duhamel term in closed form

ROUTE CARD
1. Target: EXACT identity `∫₀ᵗ duhamel1Integrand du = t · Σ_m V_mm e^{−tλ_m}`
   — the stated (never-cut) target of GalerkinDuhamel1Term: the order-1
   Duhamel word IS the pillar-1 c₁ profile, whose Laplace transform is the
   banked J_loc `galerkinSpikeTransform`. Heat weights telescope:
   e^{−(t−u)λ}·e^{−uλ} = e^{−tλ}, so the integrand is u-constant.
2. Raw B on Ω? NO. B−M bare Prop? NO — pure finite algebra + one constant
   integral. Sandwich collapse via trace cyclicity + banked
   `trace_diagonal_mul` (GalerkinDisplacementKernel).
3. Consumer: P2-4c assembly — spikeTransferE2 (M=2 split, |E2|≤t² banked)
   + perturbedFStage_eq_laplace_diagHeatTrace (F = Laplace of heat trace)
   + THIS = the operator-side seam cancellation feeding hSC.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The diagonal sandwich trace: only V's diagonal survives. -/
theorem duhamel1Integrand_eq_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u
      = ∑ m : Fin N,
          heatWeight (N := N) L (t - u) m
            * galerkinV (N := N) δ qs w L m m
            * heatWeight (N := N) L u m := by
  unfold duhamel1Integrand
  rw [Matrix.trace_mul_cycle, Matrix.diagonal_mul_diagonal,
    trace_diagonal_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- **The telescope**: the order-1 integrand is constant in `u`. -/
theorem duhamel1Integrand_eq_const
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    duhamel1Integrand (N := N) δ qs w L t u
      = ∑ m : Fin N,
          galerkinV (N := N) δ qs w L m m * heatWeight (N := N) L t m := by
  rw [duhamel1Integrand_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  unfold heatWeight
  rw [mul_comm (Real.exp (-((t - u) * galerkinLam L (m : ℕ))))
      (galerkinV (N := N) δ qs w L m m), mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- **THE CLOSED FORM (order-1 Duhamel = c₁ profile).**
`∫₀ᵗ Tr(e^{−(t−u)K} V e^{−uK}) du = t · Σ_m V_mm e^{−tλ_m}` — the B-side
spike package shape at the diagonal, exactly the pillar-1 profile whose
Laplace transform is the banked J_loc `galerkinSpikeTransform`. -/
theorem integral_duhamel1_eq_c1_profile
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    ∫ u in (0:ℝ)..t, duhamel1Integrand (N := N) δ qs w L t u
      = t * ∑ m : Fin N,
          galerkinV (N := N) δ qs w L m m * heatWeight (N := N) L t m := by
  have hcongr :
      (fun u => duhamel1Integrand (N := N) δ qs w L t u)
        = fun _ : ℝ => ∑ m : Fin N,
            galerkinV (N := N) δ qs w L m m * heatWeight (N := N) L t m := by
    funext u
    exact duhamel1Integrand_eq_const δ qs w L t u
  rw [hcongr, intervalIntegral.integral_const]
  simp [smul_eq_mul]

#print axioms duhamel1Integrand_eq_sum
#print axioms duhamel1Integrand_eq_const
#print axioms integral_duhamel1_eq_c1_profile

end

end RHFormalization
