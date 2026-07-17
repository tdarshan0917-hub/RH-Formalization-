import RHFormalization.DA2LaplaceResolvent
import RHFormalization.FiniteStageSpectrum
import Mathlib

/-!
# D.A2 full (finite-stage): F(s) = ∫₀^∞ e^{-st} Tr(e^{-tH}) dt   (manuscript p163 line 19)

F(s) = ∑ᵢ (s+λᵢ)⁻¹ = ∫₀^∞ ∑ᵢ e^{-(s+λᵢ)t} dt = ∫₀^∞ e^{-st} (∑ᵢ e^{-tλᵢ}) dt.

The bracket ∑ᵢ e^{-tλᵢ} is the heat trace Tr(e^{-tH}). This equates the
frequency-side resolvent trace F to the Laplace transform of the time-side heat trace.
-/

namespace RHFormalization
open Complex MeasureTheory
open scoped BigOperators

variable {n : ℕ}

/-- **D.A2 (finite-stage), summed.** For Re s > 0 and λᵢ ≥ 0,
`FstageFinite λ s = ∫₀^∞ ∑ᵢ e^{-(s+λᵢ)t} dt`. -/
theorem FstageFinite_eq_laplace_heatTrace
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (s : ℂ) (hs : 0 < s.re) :
    FstageFinite lam s
      = ∫ t in Set.Ioi (0:ℝ), ∑ i, Complex.exp (-(s + (lam i : ℂ)) * (t:ℂ)) := by
  unfold FstageFinite
  -- swap finite sum and integral on RHS
  rw [MeasureTheory.integral_finset_sum]
  · -- termwise: (s+λᵢ)⁻¹ = ∫ e^{-(s+λᵢ)t}
    apply Finset.sum_congr rfl
    intro i _
    exact inv_eq_laplace_exp s (lam i) (hlam i) hs
  · -- integrability of each term
    intro i _
    have hneg : (-(s + (lam i : ℂ))).re < 0 := by
      rw [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      have := hlam i; linarith
    have := integrableOn_exp_mul_complex_Ioi (a := -(s + (lam i : ℂ))) hneg 0
    -- align -(s+λ)*t  with  (-(s+λ))*t
    simpa [neg_mul] using this

#print axioms FstageFinite_eq_laplace_heatTrace

end RHFormalization
