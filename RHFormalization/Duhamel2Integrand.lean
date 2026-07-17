import RHFormalization.GalerkinDuhamelUniformBound

/-!
# Brick 2, faithful Path A1, Stone 6A: the order-2 Duhamel INTEGRAND

The manuscript's order-2 Duhamel term is the time-ordered simplex integral
`∫₀ᵗ Tr(e^{-(t-u)K} V e^{-uK} V) du`, NOT a fixed-time matrix power. Its integrand
is the fixed-time trace `trace_V_diag_V_diag`, read with heat weights `e^{-(t-u)λ}`
(left) and `e^{-uλ}` (right):
`duhamel2Integrand t u = ∑_{m,n} V_{mn} V_{nm} e^{-(t-u)λ_n} e^{-uλ_m}`.
The time integral and Beta-convolution bound come in later stones.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- Order-2 Duhamel integrand: trace of `V·e^{-(t-u)K}·V·e^{-uK}`. -/
noncomputable def duhamel2Integrand
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) : ℝ :=
  (galerkinV (N := N) δ qs w L
      * Matrix.diagonal (heatWeight (N := N) L (t - u))
      * galerkinV δ qs w L
      * Matrix.diagonal (heatWeight (N := N) L u)).trace

/-- **Stone 6A**: integrand as `∑_{m,n} V_{mn} V_{nm} e^{-(t-u)λ_n} e^{-uλ_m}`. -/
theorem duhamel2Integrand_eq_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t u : ℝ) :
    duhamel2Integrand (N := N) δ qs w L t u
      = ∑ m : Fin N, ∑ n : Fin N,
          galerkinV δ qs w L m n
          * heatWeight L (t - u) n
          * galerkinV δ qs w L n m
          * heatWeight L u m := by
  unfold duhamel2Integrand
  rw [trace_V_diag_V_diag]

#print axioms duhamel2Integrand_eq_sum
end
end RHFormalization
